// trust-cegar: IC3/PDR model checking engine
//
// IC3 maintains a sequence of frames F_0, F_1, ..., F_k where each frame
// overapproximates the set of reachable states at depth i. The algorithm
// iteratively blocks bad cubes and propagates clauses forward until either:
//   - Two consecutive frames become equal (property proved: inductive invariant found)
//   - A counterexample trace is extracted (property violated)
//
// Reference: Aaron Bradley, "SAT-Based Model Checking without Unrolling" (VMCAI 2011)
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::Formula;

use super::prime::prime_formula;
use super::sat::SatResult;
use super::types::{Cube, Frame, Ic3Config, Ic3Result, ProofObligation, TransitionSystem};
use crate::error::CegarError;
use crate::sat_oracle::{SatOracle, StructuralSatOracle, default_oracle};

/// IC3/PDR model checking engine (safety properties only).
///
/// **Important:** IC3/PDR can only prove safety properties -- "bad states are
/// never reached" (AG !bad). It cannot prove termination or liveness.
/// For `VcKind::NonTermination`, use lean5, sunder, or tla2 instead.
///
/// Maintains the frame sequence and orchestrates the IC3 algorithm:
/// 1. Initialize F_0 = Init
/// 2. Check if bad states are reachable from F_k
/// 3. If reachable, try to block the bad cube recursively
/// 4. If blocking fails at F_0, extract counterexample
/// 5. After blocking, propagate clauses forward
/// 6. If F_i == F_{i+1} for some i, property is proved
pub struct Ic3Engine {
    /// The transition system being checked.
    system: TransitionSystem,
    /// Frame sequence: F_0, F_1, ..., F_k.
    pub(super) frames: Vec<Frame>,
    /// Configuration.
    config: Ic3Config,
    /// Total blocking iterations used (for budget tracking).
    block_iterations: usize,
    /// SAT oracle for satisfiability queries (structural or z4 SMT).
    oracle: Box<dyn SatOracle>,
}

impl Ic3Engine {
    /// Create a new IC3 engine for the given transition system.
    ///
    /// Uses `StructuralSatOracle` by default (fast, conservative).
    /// Use `with_oracle` for z4-backed SMT checking.
    #[must_use]
    pub fn new(system: TransitionSystem, config: Ic3Config) -> Self {
        // F_0 is initialized with the negation of init
        // (clauses that block non-initial states are implicit).
        let f0 = Frame::new(0);
        Self {
            system,
            frames: vec![f0],
            config,
            block_iterations: 0,
            oracle: Box::new(StructuralSatOracle),
        }
    }

    /// Create a new IC3 engine with a specific SAT oracle.
    ///
    /// Use `SmtSatOracle::new()` for z4-backed checking, or
    /// `StructuralSatOracle` for fast tests.
    #[must_use]
    #[allow(dead_code)]
    pub fn with_oracle(
        system: TransitionSystem,
        config: Ic3Config,
        oracle: Box<dyn SatOracle>,
    ) -> Self {
        let f0 = Frame::new(0);
        Self { system, frames: vec![f0], config, block_iterations: 0, oracle }
    }

    /// Access the current frame sequence.
    #[must_use]
    pub fn frames(&self) -> &[Frame] {
        &self.frames
    }

    /// Current maximum frame depth.
    #[must_use]
    pub fn depth(&self) -> usize {
        self.frames.len().saturating_sub(1)
    }

    /// Run the IC3 algorithm to completion.
    ///
    /// # Errors
    /// Returns `CegarError::SolverError` on internal failures.
    /// Returns `CegarError::MaxIterationsExceeded` if the depth bound is reached.
    pub fn check(&mut self) -> Result<Ic3Result, CegarError> {
        // If init is unsatisfiable, property holds vacuously (no initial states).
        // Uses the configured SAT oracle (z4 SMT or structural fallback).
        if self.oracle.check_sat(&self.system.init)? == SatResult::Unsat {
            return Ok(Ic3Result::Safe {
                invariant_clauses: vec![Cube::new(vec![self.system.property.clone()])],
                convergence_depth: 0,
            });
        }

        // Check that initial states satisfy the property.
        // Only report Unsafe if we have a definitive SAT result (concrete model).
        // If the oracle returns Sat(None), it's conservative/unknown --
        // proceed to the loop which may prove safety or find a real counterexample.
        {
            let neg_property = Formula::Not(Box::new(self.system.property.clone()));
            let query = Formula::And(vec![self.system.init.clone(), neg_property]);
            match self.oracle.check_sat(&query)? {
                SatResult::Sat(Some(_model)) => {
                    // Definitive counterexample in initial states.
                    return Ok(Ic3Result::Unsafe {
                        trace: vec![Cube::new(vec![self.system.init.clone()])],
                    });
                }
                SatResult::Unsat => {
                    // Init satisfies property, continue to loop.
                }
                SatResult::Sat(None) => {
                    // Conservative: can't determine, let the loop decide.
                }
            }
        }

        loop {
            if self.frames.len() > self.config.max_depth {
                return Ok(Ic3Result::Unknown { depth: self.depth() });
            }

            // Extend frame sequence by one.
            let new_idx = self.frames.len();
            self.frames.push(Frame::new(new_idx));

            // Try to block all bad cubes at the frontier.
            match self.block_all_bad_cubes()? {
                BlockResult::Blocked => {
                    // All bad cubes blocked. Propagate clauses.
                    if let Some(converged_depth) = self.propagate_clauses()? {
                        // Frames converged: property is proved.
                        let invariant = self.extract_invariant(converged_depth);
                        return Ok(Ic3Result::Safe {
                            invariant_clauses: invariant,
                            convergence_depth: converged_depth,
                        });
                    }
                    // No convergence yet. Continue to next depth.
                }
                BlockResult::CounterexampleTrace(trace) => {
                    return Ok(Ic3Result::Unsafe { trace });
                }
            }
        }
    }

    /// Check if the initial states satisfy the property.
    ///
    /// Checks: SAT?(Init /\ !Property). If UNSAT, init satisfies property.
    ///
    /// Uses the configured SAT oracle (z4 SMT or structural fallback).
    /// Returns `true` only when UNSAT is definitive. `Sat(None)` (unknown)
    /// yields `false` (conservative).
    pub(super) fn init_satisfies_property(&self) -> bool {
        // Encode: init /\ !property
        let neg_property = Formula::Not(Box::new(self.system.property.clone()));
        let query = Formula::And(vec![self.system.init.clone(), neg_property]);
        // If init /\ !property is unsatisfiable, init satisfies property.
        self.oracle.check_sat(&query).unwrap_or(SatResult::Sat(None)) == SatResult::Unsat
    }

    /// Try to block all bad cubes at the current frontier frame.
    ///
    /// A "bad cube" is a state satisfying !Property that is reachable from
    /// the frontier frame via the transition relation.
    fn block_all_bad_cubes(&mut self) -> Result<BlockResult, CegarError> {
        let frontier = self.depth();

        // Find cubes in the frontier that intersect !Property.
        let bad_cubes = self.find_bad_cubes_at(frontier)?;

        for cube in bad_cubes {
            match self.block_cube(cube, frontier)? {
                BlockCubeResult::Blocked => continue,
                BlockCubeResult::CounterexampleTrace(trace) => {
                    return Ok(BlockResult::CounterexampleTrace(trace));
                }
            }
        }

        Ok(BlockResult::Blocked)
    }

    /// Find cubes that violate the property at the given frame level.
    ///
    /// Full query: SAT?(F_k /\ T /\ !P'). With z4, extracts a bad cube from
    /// the satisfying assignment. With the structural oracle, falls back to
    /// syntactic extraction from the property negation.
    fn find_bad_cubes_at(&self, frame_level: usize) -> Result<Vec<Cube>, CegarError> {
        // If the property is trivially true, there are no bad states.
        if self.system.property == Formula::Bool(true) {
            return Ok(Vec::new());
        }

        let neg_prop = Formula::Not(Box::new(self.system.property.clone()));
        let primed_neg_prop = prime_formula(&neg_prop)?;

        // Build the full IC3 bad-state query: F_k /\ T /\ !P'
        let frame_formula = if frame_level < self.frames.len() {
            self.frames[frame_level].to_formula()
        } else {
            Formula::Bool(true)
        };

        let query =
            Formula::And(vec![frame_formula, self.system.transition.clone(), primed_neg_prop]);

        // Try the oracle for the full query.
        Ok(match self.oracle.check_sat(&query) {
            Ok(SatResult::Unsat) => Vec::new(), // No bad states reachable.
            Ok(SatResult::Sat(Some(model))) => {
                // z4 gave a concrete bad cube.
                vec![model]
            }
            Ok(SatResult::Sat(None)) | Err(_) => {
                // Conservative fallback: extract from property negation.
                self.extract_bad_cubes_structural()
            }
        })
    }

    /// Structural fallback for bad cube extraction from property negation.
    fn extract_bad_cubes_structural(&self) -> Vec<Cube> {
        let neg_prop = Formula::Not(Box::new(self.system.property.clone()));
        match &neg_prop {
            Formula::Not(inner) => match inner.as_ref() {
                Formula::And(conjuncts) => conjuncts
                    .iter()
                    .map(|c| Cube::new(vec![Formula::Not(Box::new(c.clone()))]))
                    .collect(),
                _ => vec![Cube::new(vec![neg_prop])],
            },
            _ => vec![Cube::new(vec![neg_prop])],
        }
    }

    /// Recursively block a cube at the given frame level.
    ///
    /// If the cube can be blocked (no predecessor at level-1), add a clause
    /// to the frame. If it cannot be blocked at level 0, a counterexample
    /// trace is found.
    fn block_cube(&mut self, cube: Cube, level: usize) -> Result<BlockCubeResult, CegarError> {
        // Priority queue of proof obligations.
        let mut obligations = vec![ProofObligation { level, cube }];
        let mut trace_cubes: Vec<Cube> = Vec::new();

        while let Some(obligation) = obligations.pop() {
            self.block_iterations += 1;
            if self.block_iterations > self.config.max_block_iterations {
                return Err(CegarError::MaxIterationsExceeded {
                    max: self.config.max_block_iterations,
                });
            }

            if obligation.level == 0 {
                // Cannot block at level 0: counterexample found.
                trace_cubes.push(obligation.cube);
                return Ok(BlockCubeResult::CounterexampleTrace(trace_cubes));
            }

            // Check if the cube is already blocked at this level.
            if self.is_cube_blocked(&obligation.cube, obligation.level) {
                continue;
            }

            // Try to find a predecessor cube at level-1.
            match self.find_predecessor(&obligation.cube, obligation.level)? {
                Some(pred_cube) => {
                    // Predecessor found: need to block it first.
                    trace_cubes.push(obligation.cube.clone());
                    obligations
                        .push(ProofObligation { level: obligation.level, cube: obligation.cube });
                    obligations
                        .push(ProofObligation { level: obligation.level - 1, cube: pred_cube });
                }
                None => {
                    // No predecessor: the cube is blocked by induction.
                    let generalized = self.generalize_cube(&obligation.cube, obligation.level)?;
                    // Add the blocking clause to frames 1..=level.
                    for i in 1..=obligation.level {
                        if i < self.frames.len() {
                            self.frames[i].add_clause(generalized.clone());
                        }
                    }
                }
            }
        }

        Ok(BlockCubeResult::Blocked)
    }

    /// Check if a cube is already blocked by clauses in the given frame.
    ///
    /// A cube is blocked if the frame contains a clause whose negation
    /// subsumes the cube (the clause's blocked states include this cube's states).
    fn is_cube_blocked(&self, cube: &Cube, level: usize) -> bool {
        if level >= self.frames.len() {
            return false;
        }
        // A cube is blocked if any clause in the frame is a subset of
        // (or equal to) the cube.
        self.frames[level]
            .clauses
            .iter()
            .any(|clause| clause.literals.iter().all(|lit| cube.literals.contains(lit)))
    }

    /// Find a predecessor cube: a state at `level-1` that transitions to `cube`.
    ///
    /// Checks: SAT?(F_{level-1} /\ T /\ cube')
    /// If satisfiable, extracts a predecessor cube from the satisfying assignment.
    /// If unsatisfiable, no predecessor exists (cube is blockable).
    ///
    /// Uses the configured SAT oracle (z4 SMT or structural fallback).
    /// `Unsat` reliably means no predecessor. `Sat(Some(model))` provides a
    /// concrete predecessor from the z4 model. `Sat(None)` is conservative
    /// ("predecessor exists but unknown shape").
    pub(super) fn find_predecessor(
        &self,
        cube: &Cube,
        level: usize,
    ) -> Result<Option<Cube>, CegarError> {
        if level == 0 || cube.is_empty() {
            return Ok(None);
        }

        // Build the frame formula for F_{level-1}.
        let frame_formula = if level - 1 < self.frames.len() {
            self.frames[level - 1].to_formula()
        } else {
            Formula::Bool(true) // No frame constraints.
        };

        // Prime the cube to get next-state version: cube'.
        let primed_cube = prime_formula(&cube.to_formula())?;

        // Encode: F_{level-1} /\ T /\ cube'
        let query = Formula::And(vec![frame_formula, self.system.transition.clone(), primed_cube]);

        // Use the SAT oracle for the predecessor query.
        Ok(match self.oracle.check_sat(&query).unwrap_or(SatResult::Sat(None)) {
            SatResult::Unsat => None, // No predecessor: cube is blockable.
            SatResult::Sat(Some(model)) => {
                // z4 provided a concrete model -- use it as the predecessor.
                Some(model)
            }
            SatResult::Sat(None) => {
                // No concrete model available -- use approximate extraction.
                self.extract_predecessor_from_transition(cube)
            }
        })
    }

    /// Extract a predecessor cube from the transition relation.
    ///
    /// For identity transitions (T = true), the predecessor is the cube itself.
    /// For non-trivial transitions, we attempt to derive a predecessor by
    /// "unpriming" the cube through the transition relation.
    ///
    /// **Conservative approximation (#376):** Without a concrete satisfying
    /// assignment from z4, the extracted predecessor is the cube itself --
    /// an over-approximation that may include unreachable states.
    ///
    /// **Limitation (#376):** Without a z4 satisfying assignment, the predecessor
    /// is the cube itself (an over-approximation that may include unreachable states).
    fn extract_predecessor_from_transition(&self, cube: &Cube) -> Option<Cube> {
        match &self.system.transition {
            Formula::Bool(true) => {
                // Identity transition: predecessor is the same set of states.
                Some(cube.clone())
            }
            Formula::Bool(false) => None, // No transitions possible.
            _ => {
                // For non-trivial transitions, the predecessor is an approximation.
                // Return the cube as a conservative predecessor candidate.
                // A full implementation would extract from the SAT model.
                Some(cube.clone())
            }
        }
    }

    /// Generalize a blocked cube by removing redundant literals.
    ///
    /// For each literal in the cube, check if the cube remains blocked
    /// without it. If so, drop the literal (produces a stronger lemma).
    pub fn generalize_cube(&self, cube: &Cube, level: usize) -> Result<Cube, CegarError> {
        if cube.literals.len() <= 1 {
            return Ok(cube.clone());
        }

        let mut generalized = cube.literals.clone();
        let mut i = 0;

        while i < generalized.len() && generalized.len() > 1 {
            // Try removing literal at position i.
            let removed = generalized.remove(i);
            let candidate = Cube::new(generalized.clone());

            // Check if the reduced cube is still inductive relative to level-1.
            if self.is_inductive_relative(&candidate, level)? {
                // Literal was redundant; keep it removed.
                // Don't increment i since the next element shifted into position i.
            } else {
                // Literal was necessary; put it back.
                generalized.insert(i, removed);
                i += 1;
            }
        }

        Ok(Cube::new(generalized))
    }

    /// Check if a cube is inductive relative to a frame (approximate).
    ///
    /// A cube c is inductive relative to F_i if:
    ///   F_i /\ !c /\ T /\ c' is UNSAT
    /// (no successor of F_i /\ !c leads to c)
    ///
    /// This encodes the standard IC3 inductiveness check as an SMT query.
    ///
    /// Uses the configured SAT oracle (z4 SMT or structural fallback).
    /// `Unsat` is reliable (truly inductive). `Sat(None)` means "unknown" --
    /// conservatively treated as "not inductive" to prevent false proofs.
    pub(super) fn is_inductive_relative(
        &self,
        cube: &Cube,
        level: usize,
    ) -> Result<bool, CegarError> {
        if level == 0 || level >= self.frames.len() {
            return Ok(false);
        }

        let frame_formula = self.frames[level].to_formula();
        let neg_cube = cube.negate();
        let primed_cube = prime_formula(&cube.to_formula())?;

        // Encode: F_i /\ !c /\ T /\ c'
        let query = Formula::And(vec![
            frame_formula,
            neg_cube,
            self.system.transition.clone(),
            primed_cube,
        ]);

        // If UNSAT, cube is inductive relative to frame i.
        Ok(self.oracle.check_sat(&query).unwrap_or(SatResult::Sat(None)) == SatResult::Unsat)
    }

    /// Propagate clauses from each frame to the next.
    ///
    /// For each clause c in F_i, check if it is inductive relative to F_i
    /// (i.e., F_i /\ c /\ T |= c'). If so, add c to F_{i+1}.
    ///
    /// Only clauses that pass the inductiveness check are propagated.
    /// This prevents false convergence from unconditional propagation (#404).
    ///
    /// **Conservative approximation:** The inductiveness check uses
    /// `structural_sat_check`, where `Sat(None)` means "unknown" (not
    /// definitively satisfiable). Only `Unsat` is reliable. As a result,
    /// clauses that are actually inductive may not be propagated if the
    /// structural checker cannot determine UNSAT. This is sound (no false
    /// proofs) but incomplete (may fail to converge when a full SMT solver
    /// would find the inductive invariant).
    ///
    /// Returns `Some(depth)` if two consecutive frames become equal
    /// (convergence = inductive invariant found).
    pub fn propagate_clauses(&mut self) -> Result<Option<usize>, CegarError> {
        let depth = self.depth();
        if depth < 1 {
            return Ok(None);
        }

        for i in 1..depth {
            // Collect clauses from F_i that should propagate to F_{i+1}.
            let clauses_to_propagate: Vec<Cube> = self.frames[i].clauses.to_vec();

            for clause in clauses_to_propagate {
                if i + 1 < self.frames.len() && !self.frames[i + 1].contains(&clause) {
                    // Check inductiveness: only propagate if the clause is
                    // inductive relative to F_i.
                    // SAT?(F_i /\ c /\ T /\ !c') -- if UNSAT, clause is inductive.
                    if self.is_clause_inductive(&clause, i)? {
                        self.frames[i + 1].add_clause(clause);
                    }
                }
            }

            // Check convergence: F_i == F_{i+1}.
            if i + 1 < self.frames.len() && self.frames[i].clauses == self.frames[i + 1].clauses {
                return Ok(Some(i));
            }
        }

        Ok(None)
    }

    /// Check if a clause (negated cube) is inductive relative to frame F_i
    /// (approximate).
    ///
    /// A clause c (blocking cube) is inductive relative to F_i if:
    ///   F_i /\ !c_negated /\ T /\ c_negated' is UNSAT
    /// where c_negated is the negation of the clause (i.e., the original cube).
    ///
    /// Equivalently, the blocked states cannot have a successor that is also
    /// in the blocked set when constrained by the frame.
    ///
    /// Uses the configured SAT oracle (z4 SMT or structural fallback). Returns
    /// `true` only when the query is definitively UNSAT. `Sat(None)` (unknown)
    /// is treated as "not proven inductive" -- sound but incomplete.
    pub(super) fn is_clause_inductive(
        &self,
        clause: &Cube,
        level: usize,
    ) -> Result<bool, CegarError> {
        if level >= self.frames.len() {
            return Ok(false);
        }

        let frame_formula = self.frames[level].to_formula();
        // The clause blocks states matching the cube. The negation of the clause
        // (the cube formula) represents the blocked states.
        let cube_formula = clause.to_formula();
        let neg_cube = clause.negate();
        let primed_cube = prime_formula(&cube_formula)?;

        // Encode: F_i /\ !cube /\ T /\ cube'
        // (can a state satisfying the frame and NOT blocked reach a blocked state?)
        let query = Formula::And(vec![
            frame_formula,
            neg_cube,
            self.system.transition.clone(),
            primed_cube,
        ]);

        // If UNSAT, clause is inductive and can be propagated.
        Ok(self.oracle.check_sat(&query).unwrap_or(SatResult::Sat(None)) == SatResult::Unsat)
    }

    /// Extract the inductive invariant from converged frames.
    fn extract_invariant(&self, converged_depth: usize) -> Vec<Cube> {
        if converged_depth < self.frames.len() {
            self.frames[converged_depth].clauses.to_vec()
        } else {
            Vec::new()
        }
    }

    /// Extract a counterexample trace from a blocking failure.
    ///
    /// Given a sequence of cubes from `block_cube`, reconstruct the
    /// concrete execution trace from initial state to bad state.
    #[must_use]
    pub fn extract_counterexample_trace(&self, trace_cubes: &[Cube]) -> Vec<Cube> {
        if trace_cubes.is_empty() {
            return Vec::new();
        }
        // The trace is already ordered from the blocking procedure:
        // deepest frame to shallowest (bad state first).
        // Reverse to get init -> ... -> bad ordering.
        let mut ordered = trace_cubes.to_vec();
        ordered.reverse();
        ordered
    }
}

/// Internal result of blocking all bad cubes.
enum BlockResult {
    Blocked,
    CounterexampleTrace(Vec<Cube>),
}

/// Internal result of blocking a single cube.
enum BlockCubeResult {
    Blocked,
    CounterexampleTrace(Vec<Cube>),
}

// ---------------------------------------------------------------------------
// Public API: convenience functions
// ---------------------------------------------------------------------------

/// Run IC3 model checking on a transition system.
///
/// Uses `StructuralSatOracle` (fast, conservative). For z4-backed checking,
/// use `ic3_check_with_smt`.
///
/// # Errors
/// Returns `CegarError` on solver failures or depth bound exceeded.
pub fn ic3_check(system: TransitionSystem) -> Result<Ic3Result, CegarError> {
    let mut engine = Ic3Engine::new(system, Ic3Config::default());
    engine.check()
}

/// Run IC3 with custom configuration.
///
/// # Errors
/// Returns `CegarError` on solver failures or depth bound exceeded.
pub(crate) fn ic3_check_with_config(
    system: TransitionSystem,
    config: Ic3Config,
) -> Result<Ic3Result, CegarError> {
    let mut engine = Ic3Engine::new(system, config);
    engine.check()
}

/// Run IC3 with z4 SMT oracle (if available, falls back to structural).
///
/// This is the production entry point: uses real z4 SMT queries for all
/// IC3 satisfiability checks, giving complete decision procedures instead
/// of the conservative structural approximations.
///
/// # Errors
/// Returns `CegarError` on solver failures or depth bound exceeded.
#[allow(dead_code)]
pub(crate) fn ic3_check_with_smt(system: TransitionSystem) -> Result<Ic3Result, CegarError> {
    let oracle = default_oracle();
    let mut engine = Ic3Engine::with_oracle(system, Ic3Config::default(), oracle);
    engine.check()
}

/// Run IC3 with z4 SMT oracle and custom configuration.
///
/// # Errors
/// Returns `CegarError` on solver failures or depth bound exceeded.
#[allow(dead_code)]
pub(crate) fn ic3_check_with_smt_config(
    system: TransitionSystem,
    config: Ic3Config,
) -> Result<Ic3Result, CegarError> {
    let oracle = default_oracle();
    let mut engine = Ic3Engine::with_oracle(system, config, oracle);
    engine.check()
}
