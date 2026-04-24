// trust-cegar: CEGAR refinement loop
//
// Implements the core CEGAR algorithm: check abstract model, find counterexample,
// determine if spurious, refine predicates if so.
//
// Inspired by CPAchecker's CEGARAlgorithm:
//   refs/cpachecker/src/org/sosy_lab/cpachecker/core/algorithm/CEGARAlgorithm.java
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeSet;

use trust_types::{BasicBlock, Counterexample, CounterexampleValue, Formula};

use crate::error::CegarError;
use crate::ic3::{SatResult, structural_sat_check};
use crate::interpolation::{UnsatCore, craig_interpolant};
use crate::predicate::{AbstractState, CmpOp, Predicate, abstract_block};

/// Outcome of a single CEGAR iteration.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum CegarOutcome {
    /// Property holds under the current abstraction.
    Safe,
    /// Found a real (feasible) counterexample.
    Unsafe,
    /// Refined the abstraction (added predicates) and should iterate.
    Refined { new_predicates: Vec<Predicate> },
}

/// Configuration for the CEGAR loop.
#[derive(Debug, Clone)]
pub struct CegarConfig {
    /// Maximum number of refinement iterations.
    pub max_iterations: usize,
}

impl Default for CegarConfig {
    fn default() -> Self {
        Self { max_iterations: 100 }
    }
}

/// The CEGAR refinement loop.
///
/// Maintains the abstraction (predicate set), the counterexample history,
/// and the abstract states at each block. Follows CPAchecker's pattern:
///
/// 1. Build abstract reachability tree with current predicates.
/// 2. If safe, return Safe.
/// 3. If counterexample found, check feasibility.
/// 4. If feasible, return Unsafe.
/// 5. If spurious, refine predicates and go to 1.
#[derive(Debug)]
pub struct CegarLoop {
    /// The current set of tracked predicates.
    predicates: Vec<Predicate>,
    /// History of counterexamples seen (for convergence detection).
    counterexample_history: Vec<Counterexample>,
    /// Number of refinement iterations completed.
    pub(crate) iteration: usize,
    /// Configuration.
    config: CegarConfig,
    /// Abstract states per block (indexed by block position).
    abstract_states: Vec<AbstractState>,
}

impl CegarLoop {
    /// Create a new CEGAR loop with initial predicates.
    #[must_use]
    pub fn new(initial_predicates: Vec<Predicate>, config: CegarConfig) -> Self {
        Self {
            predicates: initial_predicates,
            counterexample_history: Vec::new(),
            iteration: 0,
            config,
            abstract_states: Vec::new(),
        }
    }

    /// Access the current predicate set.
    #[must_use]
    pub fn predicates(&self) -> &[Predicate] {
        &self.predicates
    }

    /// Access the counterexample history.
    #[must_use]
    pub fn counterexample_history(&self) -> &[Counterexample] {
        &self.counterexample_history
    }

    /// Access abstract states computed for blocks.
    #[must_use]
    pub fn abstract_states(&self) -> &[AbstractState] {
        &self.abstract_states
    }

    /// Current iteration count.
    #[must_use]
    pub fn iteration(&self) -> usize {
        self.iteration
    }

    /// Compute abstract states for all blocks using the current predicate set.
    pub fn compute_abstraction(&mut self, blocks: &[BasicBlock]) {
        self.abstract_states = blocks.iter().map(|b| abstract_block(b, &self.predicates)).collect();
    }

    /// Perform one iteration of the CEGAR loop.
    ///
    /// Given a counterexample from the abstract model checker:
    /// 1. Check if it is spurious (infeasible in concrete semantics).
    /// 2. If real, return `Unsafe`.
    /// 3. If spurious, extract new predicates and return `Refined`.
    ///
    /// When an unsat core is available (from `refine_iteration_with_core`),
    /// Craig interpolation is preferred over heuristic refinement.
    ///
    /// # Errors
    /// Returns `CegarError::MaxIterationsExceeded` if the limit is reached.
    /// Returns `CegarError::RefinementStalled` if no new predicates are found.
    pub fn refine_iteration(
        &mut self,
        counterexample: &Counterexample,
        blocks: &[BasicBlock],
    ) -> Result<CegarOutcome, CegarError> {
        if self.iteration >= self.config.max_iterations {
            return Err(CegarError::MaxIterationsExceeded { max: self.config.max_iterations });
        }

        self.counterexample_history.push(counterexample.clone());
        self.iteration += 1;

        if !self.is_spurious(counterexample, blocks) {
            return Ok(CegarOutcome::Unsafe);
        }

        let new_preds = self.refine(counterexample);
        if new_preds.is_empty() {
            return Err(CegarError::RefinementStalled);
        }

        // Add new predicates to the tracked set.
        let before = self.predicates.len();
        for pred in &new_preds {
            if !self.predicates.contains(pred) {
                self.predicates.push(pred.clone());
            }
        }

        // Re-compute abstraction with the refined predicates.
        self.compute_abstraction(blocks);

        if self.predicates.len() == before {
            // All "new" predicates were already tracked — stalled.
            return Err(CegarError::RefinementStalled);
        }

        Ok(CegarOutcome::Refined { new_predicates: new_preds })
    }

    /// Perform one CEGAR iteration using Craig interpolation from an unsat core.
    ///
    /// This is the preferred refinement method when a z4 unsat core is available.
    /// If interpolation fails to extract new predicates, it falls back to
    /// the heuristic `refine()` method.
    ///
    /// # Arguments
    /// * `counterexample` - The spurious counterexample.
    /// * `blocks` - All basic blocks in the function.
    /// * `path_a` - Named formulas for the path prefix.
    /// * `path_b` - Named formulas for the path suffix.
    /// * `unsat_core` - The unsat core from checking path_a /\ path_b.
    ///
    /// # Errors
    /// Returns `CegarError::MaxIterationsExceeded` if the limit is reached.
    /// Returns `CegarError::RefinementStalled` if neither interpolation nor
    /// heuristic produces new predicates.
    pub fn refine_iteration_with_core(
        &mut self,
        counterexample: &Counterexample,
        blocks: &[BasicBlock],
        path_a: &[(String, Formula)],
        path_b: &[(String, Formula)],
        unsat_core: &UnsatCore,
    ) -> Result<CegarOutcome, CegarError> {
        if self.iteration >= self.config.max_iterations {
            return Err(CegarError::MaxIterationsExceeded { max: self.config.max_iterations });
        }

        self.counterexample_history.push(counterexample.clone());
        self.iteration += 1;

        if !self.is_spurious(counterexample, blocks) {
            return Ok(CegarOutcome::Unsafe);
        }

        // Try Craig interpolation first.
        let interpolant_preds = if !unsat_core.is_empty() {
            craig_interpolant(path_a, path_b, unsat_core).unwrap_or_default()
        } else {
            Vec::new()
        };

        // If interpolation produced predicates, use them.
        // Otherwise, fall back to heuristic refinement.
        let new_preds = if interpolant_preds.is_empty() {
            self.refine(counterexample)
        } else {
            interpolant_preds
        };

        if new_preds.is_empty() {
            return Err(CegarError::RefinementStalled);
        }

        // Add new predicates to the tracked set.
        let before = self.predicates.len();
        for pred in &new_preds {
            if !self.predicates.contains(pred) {
                self.predicates.push(pred.clone());
            }
        }

        // Re-compute abstraction with the refined predicates.
        self.compute_abstraction(blocks);

        if self.predicates.len() == before {
            return Err(CegarError::RefinementStalled);
        }

        Ok(CegarOutcome::Refined { new_predicates: new_preds })
    }

    /// Extract new predicates from a spurious counterexample.
    ///
    /// Analyzes the counterexample's variable assignments to discover predicates
    /// that would eliminate the spurious path. This is a simplified form of
    /// Craig interpolation — we extract comparison predicates between variables
    /// in the counterexample and their boundary values.
    #[must_use]
    pub fn refine(&self, counterexample: &Counterexample) -> Vec<Predicate> {
        let mut new_preds = Vec::new();
        let existing: BTreeSet<&Predicate> = self.predicates.iter().collect();

        for (name, value) in &counterexample.assignments {
            // For each variable assignment, generate boundary predicates.
            match value {
                CounterexampleValue::Int(n) => {
                    // Generate: var >= 0, var < 0, var == value
                    let ge_zero = Predicate::comparison(name, CmpOp::Ge, "0");
                    if !existing.contains(&ge_zero) {
                        new_preds.push(ge_zero);
                    }
                    let eq_val = Predicate::comparison(name, CmpOp::Eq, n.to_string());
                    if !existing.contains(&eq_val) {
                        new_preds.push(eq_val);
                    }
                    if *n < 0 {
                        let lt_zero = Predicate::comparison(name, CmpOp::Lt, "0");
                        if !existing.contains(&lt_zero) {
                            new_preds.push(lt_zero);
                        }
                    }
                }
                CounterexampleValue::Uint(n) => {
                    let eq_val = Predicate::comparison(name, CmpOp::Eq, n.to_string());
                    if !existing.contains(&eq_val) {
                        new_preds.push(eq_val);
                    }
                    // Check for boundary values.
                    if *n == 0 {
                        let eq_zero = Predicate::comparison(name, CmpOp::Eq, "0");
                        if !existing.contains(&eq_zero) {
                            new_preds.push(eq_zero);
                        }
                    } else {
                        let gt_zero = Predicate::comparison(name, CmpOp::Gt, "0");
                        if !existing.contains(&gt_zero) {
                            new_preds.push(gt_zero);
                        }
                    }
                }
                CounterexampleValue::Bool(b) => {
                    let val = if *b { "1" } else { "0" };
                    let pred = Predicate::comparison(name, CmpOp::Eq, val);
                    if !existing.contains(&pred) {
                        new_preds.push(pred);
                    }
                }
                CounterexampleValue::Float(_) if name.contains("ptr") || name.contains("ref") => {
                    // Float predicates are harder to interpolate; add a non-null
                    // as a placeholder if this is a pointer-like name.
                    let nn = Predicate::non_null(name);
                    if !existing.contains(&nn) {
                        new_preds.push(nn);
                    }
                }
                CounterexampleValue::Float(_) => {}
                _ => {}
            }
        }

        // Generate pairwise comparison predicates between integer variables.
        let int_vars: Vec<(&String, i128)> = counterexample
            .assignments
            .iter()
            .filter_map(|(name, val)| match val {
                CounterexampleValue::Int(n) => Some((name, *n)),
                CounterexampleValue::Uint(n) => i128::try_from(*n).ok().map(|n| (name, n)),
                _ => None,
            })
            .collect();

        for i in 0..int_vars.len() {
            for j in (i + 1)..int_vars.len() {
                let (a_name, a_val) = int_vars[i];
                let (b_name, b_val) = int_vars[j];
                let op = if a_val < b_val {
                    CmpOp::Lt
                } else if a_val == b_val {
                    CmpOp::Eq
                } else {
                    CmpOp::Gt
                };
                let pred = Predicate::comparison(a_name, op, b_name);
                if !existing.contains(&pred) {
                    new_preds.push(pred);
                }
            }
        }

        new_preds
    }

    /// Check if a counterexample is spurious (infeasible in concrete semantics).
    ///
    /// Uses a two-phase approach:
    /// 1. **Fast pre-filter**: Check abstract state predicates against the
    ///    counterexample values. If any predicate contradicts the CEX, it is
    ///    spurious (cheap, no solver needed).
    /// 2. **Path formula SAT check**: Encode the counterexample as a path
    ///    formula (variable assignments + block constraints) and check
    ///    satisfiability. If UNSAT, the path is infeasible (spurious).
    ///
    /// The SAT check currently uses `structural_sat_check` which is
    /// conservative: it only detects UNSAT for trivially false formulas and
    /// direct contradictions (p /\ !p). When z4 is wired as an SMT backend,
    /// this will catch all infeasible paths.
    #[must_use]
    pub fn is_spurious(&self, cex: &Counterexample, blocks: &[BasicBlock]) -> bool {
        // Phase 1: Fast pre-filter via abstract state contradiction.
        for state in &self.abstract_states {
            for pred in &state.predicates {
                if counterexample_contradicts(cex, pred) {
                    return true;
                }
            }
        }

        // Phase 2: Build path formula from counterexample and check SAT.
        // Encode counterexample assignments as equality constraints, then
        // conjoin with block-level constraints (assert conditions, guards).
        let path_formula = build_path_formula(cex, blocks);
        if structural_sat_check(&path_formula) == SatResult::Unsat {
            return true;
        }

        false
    }
}

/// Check if a counterexample's assignments contradict a predicate.
fn counterexample_contradicts(cex: &Counterexample, pred: &Predicate) -> bool {
    match pred {
        Predicate::Comparison { lhs, op, rhs } => {
            let lhs_val = lookup_int_value(cex, lhs);
            let rhs_val = lookup_int_value(cex, rhs);
            match (lhs_val, rhs_val) {
                (Some(l), Some(r)) => {
                    let holds = match op {
                        CmpOp::Lt => l < r,
                        CmpOp::Le => l <= r,
                        CmpOp::Gt => l > r,
                        CmpOp::Ge => l >= r,
                        CmpOp::Eq => l == r,
                        CmpOp::Ne => l != r,
                    };
                    !holds // Contradiction if the predicate does NOT hold.
                }
                _ => false, // Cannot determine — no contradiction.
            }
        }
        Predicate::Range { var, lo, hi } => {
            if let Some(val) = lookup_int_value(cex, var) {
                val < *lo || val > *hi
            } else {
                false
            }
        }
        Predicate::NonNull(_) | Predicate::Custom(_) => false,
    }
}

/// Look up an integer value in the counterexample, or parse as a literal.
fn lookup_int_value(cex: &Counterexample, name: &str) -> Option<i128> {
    // First, check if it is a variable in the counterexample.
    for (var, val) in &cex.assignments {
        if var == name {
            return match val {
                CounterexampleValue::Int(n) => Some(*n),
                CounterexampleValue::Uint(n) => i128::try_from(*n).ok(),
                CounterexampleValue::Bool(b) => Some(i128::from(*b)),
                CounterexampleValue::Float(_) => None,
                _ => None,
            };
        }
    }
    // Then, try to parse as a numeric literal.
    name.parse::<i128>().ok()
}

/// Build a path formula from a counterexample and its block constraints.
///
/// The path formula is the conjunction of:
/// 1. **Assignment constraints**: `var == value` for each variable in the CEX.
/// 2. **Block constraints**: Assert conditions and branch guards from the
///    blocks along the path.
///
/// If the path formula is UNSAT, the counterexample is infeasible (spurious).
///
/// Note: `structural_sat_check` is conservative — it returns `Sat(None)` for
/// anything non-trivial. Only UNSAT results are reliable. This will be
/// upgraded to a full z4 SMT check when the solver is wired.
fn build_path_formula(cex: &Counterexample, blocks: &[BasicBlock]) -> Formula {
    let mut conjuncts = Vec::new();

    // Encode counterexample assignments as equality constraints.
    for (name, value) in &cex.assignments {
        let var = Formula::Var(name.clone(), trust_types::Sort::Int);
        let val_formula = match value {
            CounterexampleValue::Int(n) => Formula::Int(*n),
            CounterexampleValue::Uint(n) => {
                // Encode as int; safe for values within i128 range.
                match i128::try_from(*n) {
                    Ok(i) => Formula::Int(i),
                    Err(_) => continue, // Skip values that overflow i128.
                }
            }
            CounterexampleValue::Bool(b) => Formula::Bool(*b),
            CounterexampleValue::Float(_) => continue, // Skip floats for now.
            _ => Formula::Bool(false),
        };
        conjuncts.push(Formula::Eq(Box::new(var), Box::new(val_formula)));
    }

    // Encode block constraints: assert conditions and branch guards.
    for block in blocks {
        if let trust_types::Terminator::Assert { cond, expected, .. } = &block.terminator {
            // The assert requires `cond == expected`. Encode the condition
            // as a formula and conjoin it.
            if let Some(cond_formula) = operand_to_formula(cond) {
                let constraint =
                    if *expected { cond_formula } else { Formula::Not(Box::new(cond_formula)) };
                conjuncts.push(constraint);
            }
        }
    }

    match conjuncts.len() {
        0 => Formula::Bool(true),
        1 => conjuncts.into_iter().next().expect("checked len == 1"),
        _ => Formula::And(conjuncts),
    }
}

/// Convert an operand to a formula, if possible.
///
/// Only handles simple cases (local variables as `Copy` or `Move`).
/// Returns `None` for constants and complex operands.
fn operand_to_formula(operand: &trust_types::Operand) -> Option<Formula> {
    match operand {
        trust_types::Operand::Copy(place) | trust_types::Operand::Move(place) => {
            if place.projections.is_empty() {
                Some(Formula::Var(format!("_local{}", place.local), trust_types::Sort::Int))
            } else {
                None // Complex projections not yet supported.
            }
        }
        trust_types::Operand::Constant(cv) => match cv {
            trust_types::ConstValue::Bool(b) => Some(Formula::Bool(*b)),
            trust_types::ConstValue::Int(n) => Some(Formula::Int(*n)),
            trust_types::ConstValue::Uint(n, _) => i128::try_from(*n).ok().map(Formula::Int),
            _ => None,
        },
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_cex(assignments: Vec<(&str, CounterexampleValue)>) -> Counterexample {
        Counterexample::new(assignments.into_iter().map(|(n, v)| (n.to_string(), v)).collect())
    }

    #[test]
    fn test_refine_extracts_predicates_from_int_cex() {
        let cegar = CegarLoop::new(vec![], CegarConfig::default());
        let cex = make_cex(vec![
            ("x", CounterexampleValue::Int(-5)),
            ("y", CounterexampleValue::Int(10)),
        ]);
        let preds = cegar.refine(&cex);
        assert!(!preds.is_empty());
        // Should include x >= 0, x < 0, x == -5, y >= 0, y == 10, x < y
        let pred_strs: Vec<String> = preds.iter().map(ToString::to_string).collect();
        assert!(pred_strs.contains(&"x >= 0".to_string()));
        assert!(pred_strs.contains(&"x < 0".to_string()));
        assert!(pred_strs.contains(&"x < y".to_string()));
    }

    #[test]
    fn test_refine_extracts_predicates_from_uint_cex() {
        let cegar = CegarLoop::new(vec![], CegarConfig::default());
        let cex = make_cex(vec![("n", CounterexampleValue::Uint(0))]);
        let preds = cegar.refine(&cex);
        let pred_strs: Vec<String> = preds.iter().map(ToString::to_string).collect();
        assert!(pred_strs.contains(&"n == 0".to_string()));
    }

    #[test]
    fn test_refine_extracts_bool_predicates() {
        let cegar = CegarLoop::new(vec![], CegarConfig::default());
        let cex = make_cex(vec![("flag", CounterexampleValue::Bool(true))]);
        let preds = cegar.refine(&cex);
        let pred_strs: Vec<String> = preds.iter().map(ToString::to_string).collect();
        assert!(pred_strs.contains(&"flag == 1".to_string()));
    }

    #[test]
    fn test_refine_skips_existing_predicates() {
        let existing = vec![Predicate::comparison("x", CmpOp::Ge, "0")];
        let cegar = CegarLoop::new(existing, CegarConfig::default());
        let cex = make_cex(vec![("x", CounterexampleValue::Int(5))]);
        let preds = cegar.refine(&cex);
        // x >= 0 already exists, should not be in new predicates
        assert!(!preds.contains(&Predicate::comparison("x", CmpOp::Ge, "0")));
    }

    #[test]
    fn test_is_spurious_with_contradiction() {
        let mut cegar = CegarLoop::new(
            vec![Predicate::comparison("x", CmpOp::Ge, "0")],
            CegarConfig::default(),
        );
        // Manually set abstract states so x >= 0 holds.
        cegar.abstract_states = vec![{
            let mut s = AbstractState::top();
            s.add(Predicate::comparison("x", CmpOp::Ge, "0"));
            s
        }];
        // Counterexample where x = -1 contradicts x >= 0.
        let cex = make_cex(vec![("x", CounterexampleValue::Int(-1))]);
        assert!(cegar.is_spurious(&cex, &[]));
    }

    #[test]
    fn test_is_spurious_no_contradiction() {
        let mut cegar = CegarLoop::new(
            vec![Predicate::comparison("x", CmpOp::Ge, "0")],
            CegarConfig::default(),
        );
        cegar.abstract_states = vec![{
            let mut s = AbstractState::top();
            s.add(Predicate::comparison("x", CmpOp::Ge, "0"));
            s
        }];
        // Counterexample where x = 5 does NOT contradict x >= 0.
        let cex = make_cex(vec![("x", CounterexampleValue::Int(5))]);
        assert!(!cegar.is_spurious(&cex, &[]));
    }

    #[test]
    fn test_counterexample_contradicts_range() {
        let pred = Predicate::range("idx", 0, 100);
        let cex = make_cex(vec![("idx", CounterexampleValue::Int(101))]);
        assert!(counterexample_contradicts(&cex, &pred));

        let cex_ok = make_cex(vec![("idx", CounterexampleValue::Int(50))]);
        assert!(!counterexample_contradicts(&cex_ok, &pred));
    }

    // -- is_spurious path formula tests (#380) --

    #[test]
    fn test_is_spurious_uses_path_formula_not_just_abstract_states() {
        // Bug #380: is_spurious() with empty abstract states used to return
        // false (not spurious) for ALL counterexamples because there were no
        // predicates to contradict. With the path formula check, we can now
        // detect infeasibility from block constraints even without predicates.
        let cegar = CegarLoop::new(vec![], CegarConfig::default());
        // abstract_states is empty (default).

        // Create a counterexample with x=5.
        let cex = make_cex(vec![("x", CounterexampleValue::Int(5))]);

        // Block with assert(false) -- the path is always infeasible.
        let block_with_false_assert = trust_types::BasicBlock {
            id: trust_types::BlockId(0),
            stmts: vec![],
            terminator: trust_types::Terminator::Assert {
                cond: trust_types::Operand::Constant(trust_types::ConstValue::Bool(false)),
                expected: true,
                msg: trust_types::AssertMessage::BoundsCheck,
                target: trust_types::BlockId(1),
                span: trust_types::SourceSpan::default(),
            },
        };

        // With the fix: path formula includes `false` (from assert), so
        // structural_sat_check detects UNSAT and reports spurious.
        assert!(
            cegar.is_spurious(&cex, &[block_with_false_assert]),
            "is_spurious should detect infeasible path from assert(false) \
             even with empty abstract states"
        );
    }

    #[test]
    fn test_is_spurious_path_formula_with_contradictory_assert() {
        // A block asserts that a boolean constant is false (expected=false on
        // Constant(true)), producing Not(true) = false in the path formula.
        let cegar = CegarLoop::new(vec![], CegarConfig::default());

        let cex = make_cex(vec![("y", CounterexampleValue::Int(0))]);

        let block = trust_types::BasicBlock {
            id: trust_types::BlockId(0),
            stmts: vec![],
            terminator: trust_types::Terminator::Assert {
                cond: trust_types::Operand::Constant(trust_types::ConstValue::Bool(true)),
                expected: false, // assert(!true) = assert(false)
                msg: trust_types::AssertMessage::BoundsCheck,
                target: trust_types::BlockId(1),
                span: trust_types::SourceSpan::default(),
            },
        };

        assert!(
            cegar.is_spurious(&cex, &[block]),
            "is_spurious should detect infeasible path from assert(!true)"
        );
    }

    #[test]
    fn test_is_spurious_path_formula_feasible() {
        // When the path formula is satisfiable, is_spurious returns false.
        let cegar = CegarLoop::new(vec![], CegarConfig::default());
        let cex = make_cex(vec![("x", CounterexampleValue::Int(5))]);

        // Block with assert(true) -- path is always feasible.
        let block = trust_types::BasicBlock {
            id: trust_types::BlockId(0),
            stmts: vec![],
            terminator: trust_types::Terminator::Assert {
                cond: trust_types::Operand::Constant(trust_types::ConstValue::Bool(true)),
                expected: true,
                msg: trust_types::AssertMessage::BoundsCheck,
                target: trust_types::BlockId(1),
                span: trust_types::SourceSpan::default(),
            },
        };

        // No abstract states, assert(true) is feasible.
        assert!(
            !cegar.is_spurious(&cex, &[block]),
            "is_spurious should return false for feasible path"
        );
    }

    #[test]
    fn test_is_spurious_empty_blocks_empty_states() {
        // With no blocks and no abstract states, path formula is `true` (SAT),
        // so the CEX is not spurious.
        let cegar = CegarLoop::new(vec![], CegarConfig::default());
        let cex = make_cex(vec![("x", CounterexampleValue::Int(0))]);
        assert!(!cegar.is_spurious(&cex, &[]));
    }

    #[test]
    fn test_build_path_formula_encodes_assignments() {
        let cex = make_cex(vec![
            ("x", CounterexampleValue::Int(42)),
            ("flag", CounterexampleValue::Bool(true)),
        ]);
        let formula = build_path_formula(&cex, &[]);
        // Should be And([x == 42, flag == true]).
        match &formula {
            Formula::And(conjuncts) => {
                assert_eq!(conjuncts.len(), 2);
            }
            _ => panic!("expected And formula, got: {formula:?}"),
        }
    }

    #[test]
    fn test_build_path_formula_includes_assert_constraint() {
        let cex = make_cex(vec![("x", CounterexampleValue::Int(0))]);
        let block = trust_types::BasicBlock {
            id: trust_types::BlockId(0),
            stmts: vec![],
            terminator: trust_types::Terminator::Assert {
                cond: trust_types::Operand::Constant(trust_types::ConstValue::Bool(false)),
                expected: true,
                msg: trust_types::AssertMessage::BoundsCheck,
                target: trust_types::BlockId(1),
                span: trust_types::SourceSpan::default(),
            },
        };
        let formula = build_path_formula(&cex, &[block]);
        // Should include the assignment (x == 0) and the assert (false).
        // The conjunction should simplify or contain Bool(false).
        match &formula {
            Formula::And(conjuncts) => {
                // One of the conjuncts should be Bool(false) from assert(false, expected=true).
                assert!(
                    conjuncts.contains(&Formula::Bool(false)),
                    "expected Bool(false) from assert, got: {conjuncts:?}"
                );
            }
            _ => panic!("expected And formula, got: {formula:?}"),
        }
    }

    #[test]
    fn test_cegar_max_iterations() {
        let config = CegarConfig { max_iterations: 1 };
        let mut cegar = CegarLoop::new(vec![], config);
        let cex = make_cex(vec![("x", CounterexampleValue::Int(0))]);

        // First iteration should succeed.
        let block = trust_types::BasicBlock {
            id: trust_types::BlockId(0),
            stmts: vec![],
            terminator: trust_types::Terminator::Return,
        };
        let result = cegar.refine_iteration(&cex, std::slice::from_ref(&block));
        assert!(result.is_ok());

        // Second should fail with max iterations.
        let result = cegar.refine_iteration(&cex, std::slice::from_ref(&block));
        assert!(matches!(result, Err(CegarError::MaxIterationsExceeded { max: 1 })));
    }

    #[test]
    fn test_refine_iteration_with_core_uses_interpolation() {
        let mut cegar = CegarLoop::new(vec![], CegarConfig::default());
        // Set abstract states so counterexample is spurious.
        cegar.abstract_states = vec![{
            let mut s = AbstractState::top();
            s.add(Predicate::comparison("x", CmpOp::Ge, "0"));
            s
        }];

        let cex = make_cex(vec![("x", CounterexampleValue::Int(-1))]);
        let block = trust_types::BasicBlock {
            id: trust_types::BlockId(0),
            stmts: vec![],
            terminator: trust_types::Terminator::Return,
        };

        // Path A: x < 10, Path B: x >= 20
        let path_a = vec![(
            "a0".to_string(),
            Formula::Lt(
                Box::new(Formula::Var("x".into(), trust_types::Sort::Int)),
                Box::new(Formula::Int(10)),
            ),
        )];
        let path_b = vec![(
            "b0".to_string(),
            Formula::Ge(
                Box::new(Formula::Var("x".into(), trust_types::Sort::Int)),
                Box::new(Formula::Int(20)),
            ),
        )];
        let core = UnsatCore::new(vec!["a0".into(), "b0".into()]);

        let result = cegar.refine_iteration_with_core(&cex, &[block], &path_a, &path_b, &core);
        assert!(result.is_ok());
        match result.unwrap() {
            CegarOutcome::Refined { new_predicates } => {
                // Should contain interpolation-derived predicates.
                assert!(!new_predicates.is_empty());
                // "x < 10" should be among the interpolants (from A-side).
                assert!(
                    new_predicates.contains(&Predicate::comparison("x", CmpOp::Lt, "10")),
                    "expected x < 10, got: {:?}",
                    new_predicates
                );
            }
            other => panic!("expected Refined, got: {other:?}"),
        }
    }

    #[test]
    fn test_refine_iteration_with_core_fallback_to_heuristic() {
        let mut cegar = CegarLoop::new(vec![], CegarConfig::default());
        cegar.abstract_states = vec![{
            let mut s = AbstractState::top();
            s.add(Predicate::comparison("x", CmpOp::Ge, "0"));
            s
        }];

        let cex = make_cex(vec![("x", CounterexampleValue::Int(-1))]);
        let block = trust_types::BasicBlock {
            id: trust_types::BlockId(0),
            stmts: vec![],
            terminator: trust_types::Terminator::Return,
        };

        // Empty unsat core -> should fall back to heuristic.
        let empty_core = UnsatCore::default();
        let result = cegar.refine_iteration_with_core(&cex, &[block], &[], &[], &empty_core);
        assert!(result.is_ok());
        match result.unwrap() {
            CegarOutcome::Refined { new_predicates } => {
                // Heuristic should have found predicates from the counterexample.
                assert!(!new_predicates.is_empty());
            }
            other => panic!("expected Refined with heuristic fallback, got: {other:?}"),
        }
    }

    #[test]
    fn test_refine_iteration_with_core_max_iterations() {
        let config = CegarConfig { max_iterations: 0 };
        let mut cegar = CegarLoop::new(vec![], config);
        let cex = make_cex(vec![("x", CounterexampleValue::Int(0))]);
        let block = trust_types::BasicBlock {
            id: trust_types::BlockId(0),
            stmts: vec![],
            terminator: trust_types::Terminator::Return,
        };
        let core = UnsatCore::default();

        let result = cegar.refine_iteration_with_core(&cex, &[block], &[], &[], &core);
        assert!(matches!(result, Err(CegarError::MaxIterationsExceeded { max: 0 })));
    }

    #[test]
    fn test_refine_iteration_with_core_unsafe_path() {
        // No abstract states -> counterexample is NOT spurious -> Unsafe
        let mut cegar = CegarLoop::new(vec![], CegarConfig::default());
        let cex = make_cex(vec![("x", CounterexampleValue::Int(5))]);
        let block = trust_types::BasicBlock {
            id: trust_types::BlockId(0),
            stmts: vec![],
            terminator: trust_types::Terminator::Return,
        };
        let core = UnsatCore::new(vec!["a0".into()]);
        let path_a = vec![("a0".to_string(), Formula::Bool(true))];

        let result = cegar.refine_iteration_with_core(&cex, &[block], &path_a, &[], &core);
        assert!(matches!(result, Ok(CegarOutcome::Unsafe)));
    }
}
