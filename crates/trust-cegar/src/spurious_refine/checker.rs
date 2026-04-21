// trust-cegar: Counterexample feasibility checker
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{BasicBlock, Counterexample, Formula};

use crate::interpolation::UnsatCore;
use crate::predicate::AbstractState;

use super::helpers::{
    block_constraint_formula, build_cex_path_formula, cex_contradicts_predicate,
    cex_value_to_formula, collect_core_labels, find_unsat_block, is_trivially_unsat,
};

/// Result of checking a counterexample against the concrete model.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum CexCheckResult {
    /// The counterexample is feasible: it corresponds to a real execution.
    Feasible,

    /// Feasibility could not be determined by syntactic analysis alone.
    /// A full SMT solver check is needed.
    Unknown,

    /// The counterexample is spurious: infeasible on the concrete model.
    /// Includes proof data for refinement.
    Spurious {
        /// The point along the trace where infeasibility was detected
        /// (index into the counterexample's block path).
        infeasibility_point: usize,
        /// Path formulas split at the infeasibility point for interpolation.
        path_a: Vec<(String, Formula)>,
        path_b: Vec<(String, Formula)>,
        /// Unsat core from the feasibility check (empty if solver did not
        /// provide one).
        unsat_core: UnsatCore,
    },
}

/// Checks whether an abstract counterexample is feasible on the concrete model.
///
/// The checker encodes the counterexample as a path formula (variable
/// assignments conjoined with block constraints) and checks satisfiability.
/// If the formula is UNSAT, the counterexample is spurious, and the checker
/// provides proof data (infeasibility point, path formulas, unsat core) for
/// subsequent refinement.
#[derive(Debug, Clone)]
pub struct CounterexampleChecker {
    /// Abstract states at each block (used for fast pre-filtering).
    abstract_states: Vec<AbstractState>,
}

impl CounterexampleChecker {
    /// Create a new counterexample checker with the current abstraction.
    #[must_use]
    pub fn new(abstract_states: Vec<AbstractState>) -> Self {
        Self { abstract_states }
    }

    /// Update the abstract states (e.g., after refinement).
    pub fn update_states(&mut self, states: Vec<AbstractState>) {
        self.abstract_states = states;
    }

    /// Check whether a counterexample is feasible.
    ///
    /// Uses a three-phase approach:
    /// 1. **Fast pre-filter**: check abstract state predicates against the
    ///    counterexample values. If any predicate contradicts the CEX, it is
    ///    spurious (no solver invocation needed).
    /// 2. **Path formula construction**: encode the CEX as assignments +
    ///    block constraints.
    /// 3. **Satisfiability check**: determine if the path formula is SAT.
    ///    If UNSAT, extract the infeasibility point and proof data.
    #[must_use]
    pub fn check(
        &self,
        cex: &Counterexample,
        blocks: &[BasicBlock],
    ) -> CexCheckResult {
        // Phase 1: Fast pre-filter via abstract state contradiction.
        if let Some(infeasibility_point) = self.find_contradiction(cex) {
            let (path_a, path_b) = self.build_split_formulas(cex, blocks, infeasibility_point);
            return CexCheckResult::Spurious {
                infeasibility_point,
                path_a,
                path_b,
                unsat_core: UnsatCore::default(),
            };
        }

        // Phase 2: Build path formula and check satisfiability.
        let path_formula = build_cex_path_formula(cex, blocks);
        if is_trivially_unsat(&path_formula) {
            // Find the block that contributed the unsatisfiable constraint.
            let point = find_unsat_block(cex, blocks);
            let (path_a, path_b) = self.build_split_formulas(cex, blocks, point);
            let core_labels = collect_core_labels(&path_a, &path_b);
            return CexCheckResult::Spurious {
                infeasibility_point: point,
                path_a,
                path_b,
                unsat_core: UnsatCore::new(core_labels),
            };
        }

        // Phase 3: No contradiction detected by syntactic analysis.
        // Return Unknown rather than Feasible to avoid false alarms.
        // A full SMT solver check is needed to determine feasibility.
        CexCheckResult::Unknown
    }

    /// Find the first abstract state whose predicates contradict the CEX.
    ///
    /// Returns the index of the contradicting state, or None if no
    /// contradiction is found.
    fn find_contradiction(&self, cex: &Counterexample) -> Option<usize> {
        for (idx, state) in self.abstract_states.iter().enumerate() {
            for pred in &state.predicates {
                if cex_contradicts_predicate(cex, pred) {
                    return Some(idx);
                }
            }
        }
        None
    }

    /// Split path formulas at the infeasibility point for interpolation.
    ///
    /// Path A contains formulas from blocks [0, point).
    /// Path B contains formulas from blocks [point, end].
    #[allow(clippy::type_complexity)]
    fn build_split_formulas(
        &self,
        cex: &Counterexample,
        blocks: &[BasicBlock],
        split_point: usize,
    ) -> (Vec<(String, Formula)>, Vec<(String, Formula)>) {
        let mut path_a = Vec::new();
        let mut path_b = Vec::new();

        // Encode assignment constraints.
        for (i, (name, value)) in cex.assignments.iter().enumerate() {
            if let Some(formula) = cex_value_to_formula(name, value) {
                let label = format!("assign_{i}");
                if i < split_point {
                    path_a.push((label, formula));
                } else {
                    path_b.push((label, formula));
                }
            }
        }

        // Encode block constraints.
        for (i, block) in blocks.iter().enumerate() {
            if let Some(formula) = block_constraint_formula(block) {
                let label = format!("block_{i}");
                if i < split_point {
                    path_a.push((label, formula));
                } else {
                    path_b.push((label, formula));
                }
            }
        }

        (path_a, path_b)
    }
}
