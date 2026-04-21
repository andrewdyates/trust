// trust-cegar: Full CEGAR lazy refinement loop driver
//
// Wires together predicate abstraction, abstract model checking, feasibility
// checking, and predicate refinement into a complete CEGAR loop:
//
//   abstract -> check -> feasibility -> refine -> repeat
//
// Inspired by CPAchecker's CEGARAlgorithm:
//   refs/cpachecker/src/org/sosy_lab/cpachecker/core/algorithm/CEGARAlgorithm.java
//
// Part of #228: CEGAR lazy refinement loop
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::time::{Duration, Instant};

use trust_types::{BasicBlock, Counterexample, Formula};

use crate::error::CegarError;
use crate::interpolation::{UnsatCore, craig_interpolant};
use crate::predicate::{AbstractState, Predicate, abstract_block};

// ---------------------------------------------------------------------------
// Loop outcome
// ---------------------------------------------------------------------------

/// Overall outcome of the CEGAR loop.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum LoopOutcome {
    /// Property is proved safe: no reachable error state exists under the
    /// refined abstraction.
    Proved {
        /// Number of CEGAR iterations to convergence.
        iterations: usize,
        /// Final predicate count.
        predicates: usize,
    },
    /// Property is disproved: a feasible counterexample was found.
    Disproved {
        /// The concrete counterexample witnessing the violation.
        counterexample: Counterexample,
        /// Iteration at which the real counterexample was found.
        iteration: usize,
    },
    /// Resource limits exhausted before convergence.
    ResourceExhausted {
        /// Reason: "max_iterations" or "timeout".
        reason: String,
        /// Iterations completed before exhaustion.
        iterations: usize,
        /// Final predicate count.
        predicates: usize,
    },
}

// ---------------------------------------------------------------------------
// Loop configuration
// ---------------------------------------------------------------------------

/// Configuration for the CEGAR loop.
#[derive(Debug, Clone)]
pub struct LoopConfig {
    /// Maximum number of refinement iterations (0 = unlimited).
    pub max_iterations: usize,
    /// Timeout for the entire loop (0 = unlimited).
    pub timeout: Duration,
    /// Initial predicates to seed the abstraction.
    pub initial_predicates: Vec<Predicate>,
}

impl Default for LoopConfig {
    fn default() -> Self {
        Self {
            max_iterations: 100,
            timeout: Duration::from_secs(300),
            initial_predicates: Vec::new(),
        }
    }
}

// ---------------------------------------------------------------------------
// Component traits
// ---------------------------------------------------------------------------

/// Abstract model checker: checks whether an error state is reachable in
/// the abstract program under the current predicate set.
///
/// Returns `Ok(None)` if safe (no abstract counterexample), or
/// `Ok(Some(cex))` with an abstract counterexample path if an error
/// path exists in the abstraction.
pub trait AbstractChecker: std::fmt::Debug {
    /// Check the abstract model for reachability of error states.
    ///
    /// # Arguments
    /// * `blocks` - Basic blocks of the program.
    /// * `predicates` - Current predicate set defining the abstraction.
    /// * `abstract_states` - Abstract state at each block.
    ///
    /// # Errors
    /// Returns `CegarError` on internal failure.
    fn check(
        &self,
        blocks: &[BasicBlock],
        predicates: &[Predicate],
        abstract_states: &[AbstractState],
    ) -> Result<Option<Counterexample>, CegarError>;
}

/// Feasibility checker: determines whether an abstract counterexample
/// corresponds to a real (feasible) execution path.
///
/// Returns `Ok(true)` if feasible (real bug), `Ok(false)` if spurious.
/// When spurious, also provides path formulas and unsat core for refinement.
pub trait FeasibilityChecker: std::fmt::Debug {
    /// Check whether a counterexample is feasible.
    ///
    /// # Returns
    /// A `FeasibilityResult` indicating feasible, spurious (with proof data),
    /// or an error.
    fn check_feasibility(
        &self,
        counterexample: &Counterexample,
        blocks: &[BasicBlock],
        predicates: &[Predicate],
    ) -> Result<FeasibilityResult, CegarError>;
}

/// Result of a feasibility check.
#[derive(Debug, Clone)]
pub enum FeasibilityResult {
    /// The counterexample is feasible (a real bug).
    Feasible,
    /// The counterexample is spurious. Includes proof data for refinement.
    Spurious {
        /// Path formulas split into prefix (A) and suffix (B) at the
        /// interpolation point.
        path_a: Vec<(String, Formula)>,
        path_b: Vec<(String, Formula)>,
        /// Unsat core from the infeasibility proof.
        unsat_core: UnsatCore,
    },
}

/// Predicate refiner: extracts new predicates from an infeasible
/// counterexample using Craig interpolation or heuristics.
pub trait PredicateRefiner: std::fmt::Debug {
    /// Extract new predicates from a spurious counterexample.
    ///
    /// Uses the path formulas and unsat core to compute Craig interpolants,
    /// falling back to heuristic refinement if interpolation fails.
    fn refine(
        &self,
        counterexample: &Counterexample,
        path_a: &[(String, Formula)],
        path_b: &[(String, Formula)],
        unsat_core: &UnsatCore,
        existing_predicates: &[Predicate],
    ) -> Result<Vec<Predicate>, CegarError>;
}

// ---------------------------------------------------------------------------
// CEGAR driver
// ---------------------------------------------------------------------------

/// The full CEGAR lazy refinement loop driver.
///
/// Orchestrates the abstract -> check -> feasibility -> refine cycle until:
/// - The abstract model is safe (Proved)
/// - A feasible counterexample is found (Disproved)
/// - Resource limits are exhausted (ResourceExhausted)
#[derive(Debug)]
pub struct CegarDriver<C, F, R> {
    /// Abstract model checker.
    checker: C,
    /// Feasibility checker.
    feasibility: F,
    /// Predicate refiner.
    refiner: R,
    /// Loop configuration.
    config: LoopConfig,
}

impl<C, F, R> CegarDriver<C, F, R>
where
    C: AbstractChecker,
    F: FeasibilityChecker,
    R: PredicateRefiner,
{
    /// Create a new CEGAR driver with the given components.
    #[must_use]
    pub(crate) fn new(checker: C, feasibility: F, refiner: R, config: LoopConfig) -> Self {
        Self { checker, feasibility, refiner, config }
    }

    /// Run the full CEGAR loop.
    ///
    /// # Arguments
    /// * `blocks` - Basic blocks of the program under verification.
    ///
    /// # Errors
    /// Returns `CegarError` on internal component failures. Resource
    /// exhaustion is returned as `Ok(LoopOutcome::ResourceExhausted)`,
    /// not as an error.
    pub(crate) fn run(&self, blocks: &[BasicBlock]) -> Result<LoopOutcome, CegarError> {
        let start = Instant::now();
        let mut predicates: Vec<Predicate> = self.config.initial_predicates.clone();
        let mut iteration = 0;

        loop {
            // Check resource limits.
            if self.config.max_iterations > 0 && iteration >= self.config.max_iterations {
                return Ok(LoopOutcome::ResourceExhausted {
                    reason: "max_iterations".to_string(),
                    iterations: iteration,
                    predicates: predicates.len(),
                });
            }
            if !self.config.timeout.is_zero() && start.elapsed() >= self.config.timeout {
                return Ok(LoopOutcome::ResourceExhausted {
                    reason: "timeout".to_string(),
                    iterations: iteration,
                    predicates: predicates.len(),
                });
            }

            // Step 1: Compute abstract states under current predicates.
            let abstract_states: Vec<AbstractState> = blocks
                .iter()
                .map(|b| abstract_block(b, &predicates))
                .collect();

            // Step 2: Check abstract model for counterexample.
            let cex = self.checker.check(blocks, &predicates, &abstract_states)?;

            let Some(counterexample) = cex else {
                // No counterexample => property holds under this abstraction.
                return Ok(LoopOutcome::Proved {
                    iterations: iteration,
                    predicates: predicates.len(),
                });
            };

            iteration += 1;

            // Step 3: Check feasibility of the counterexample.
            let feasibility_result =
                self.feasibility.check_feasibility(&counterexample, blocks, &predicates)?;

            match feasibility_result {
                FeasibilityResult::Feasible => {
                    // Real bug found.
                    return Ok(LoopOutcome::Disproved {
                        counterexample,
                        iteration,
                    });
                }
                FeasibilityResult::Spurious { path_a, path_b, unsat_core } => {
                    // Step 4: Refine predicates from the spurious counterexample.
                    let new_preds = self.refiner.refine(
                        &counterexample,
                        &path_a,
                        &path_b,
                        &unsat_core,
                        &predicates,
                    )?;

                    if new_preds.is_empty() {
                        return Err(CegarError::RefinementStalled);
                    }

                    // Add new predicates (dedup).
                    for pred in new_preds {
                        if !predicates.contains(&pred) {
                            predicates.push(pred);
                        }
                    }
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Default implementations for the component traits
// ---------------------------------------------------------------------------

/// Default predicate refiner using Craig interpolation with heuristic fallback.
#[derive(Debug, Clone)]
pub struct InterpolatingRefiner;

impl PredicateRefiner for InterpolatingRefiner {
    fn refine(
        &self,
        counterexample: &Counterexample,
        path_a: &[(String, Formula)],
        path_b: &[(String, Formula)],
        unsat_core: &UnsatCore,
        existing_predicates: &[Predicate],
    ) -> Result<Vec<Predicate>, CegarError> {
        // Try Craig interpolation first.
        let mut new_preds = if !unsat_core.is_empty() {
            craig_interpolant(path_a, path_b, unsat_core).unwrap_or_default()
        } else {
            Vec::new()
        };

        // Fall back to heuristic refinement if interpolation produced nothing.
        if new_preds.is_empty() {
            new_preds = heuristic_refine(counterexample, existing_predicates);
        }

        // Filter out already-known predicates.
        new_preds.retain(|p| !existing_predicates.contains(p));

        Ok(new_preds)
    }
}

/// Heuristic refinement: extract predicates from counterexample values.
fn heuristic_refine(
    counterexample: &Counterexample,
    existing: &[Predicate],
) -> Vec<Predicate> {
    use crate::predicate::CmpOp;
    use trust_types::CounterexampleValue;

    let mut preds = Vec::new();
    let existing_set: std::collections::BTreeSet<&Predicate> = existing.iter().collect();

    for (name, value) in &counterexample.assignments {
        match value {
            CounterexampleValue::Int(n) => {
                let ge_zero = Predicate::comparison(name, CmpOp::Ge, "0");
                if !existing_set.contains(&ge_zero) {
                    preds.push(ge_zero);
                }
                let eq_val = Predicate::comparison(name, CmpOp::Eq, n.to_string());
                if !existing_set.contains(&eq_val) {
                    preds.push(eq_val);
                }
            }
            CounterexampleValue::Uint(n) => {
                let eq_val = Predicate::comparison(name, CmpOp::Eq, n.to_string());
                if !existing_set.contains(&eq_val) {
                    preds.push(eq_val);
                }
            }
            CounterexampleValue::Bool(b) => {
                let val = if *b { "1" } else { "0" };
                let pred = Predicate::comparison(name, CmpOp::Eq, val);
                if !existing_set.contains(&pred) {
                    preds.push(pred);
                }
            }
            CounterexampleValue::Float(_) => {}
            _ => {},
        }
    }

    preds
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use trust_types::{BlockId, CounterexampleValue, Sort, Terminator};

    use super::*;

    // -----------------------------------------------------------------------
    // Mock components
    // -----------------------------------------------------------------------

    /// Mock checker that reports safe after a given number of iterations.
    #[derive(Debug)]
    struct MockSafeChecker {
        /// Number of counterexamples to produce before reporting safe.
        spurious_rounds: usize,
        /// Counter (interior mutability for trait signature compatibility).
        call_count: std::cell::Cell<usize>,
    }

    impl MockSafeChecker {
        fn new(spurious_rounds: usize) -> Self {
            Self { spurious_rounds, call_count: std::cell::Cell::new(0) }
        }
    }

    impl AbstractChecker for MockSafeChecker {
        fn check(
            &self,
            _blocks: &[BasicBlock],
            _predicates: &[Predicate],
            _abstract_states: &[AbstractState],
        ) -> Result<Option<Counterexample>, CegarError> {
            let n = self.call_count.get();
            self.call_count.set(n + 1);
            if n < self.spurious_rounds {
                // Produce a spurious counterexample.
                Ok(Some(Counterexample::new(vec![
                    ("x".to_string(), CounterexampleValue::Int(-(n as i128) - 1)),
                ])))
            } else {
                // Abstraction is precise enough; safe.
                Ok(None)
            }
        }
    }

    /// Mock checker that always produces a counterexample (for disproved tests).
    #[derive(Debug)]
    struct MockUnsafeChecker;

    impl AbstractChecker for MockUnsafeChecker {
        fn check(
            &self,
            _blocks: &[BasicBlock],
            _predicates: &[Predicate],
            _abstract_states: &[AbstractState],
        ) -> Result<Option<Counterexample>, CegarError> {
            Ok(Some(Counterexample::new(vec![
                ("x".to_string(), CounterexampleValue::Int(42)),
            ])))
        }
    }

    /// Mock feasibility checker that always says spurious.
    ///
    /// Varies the path formulas based on counterexample values so that
    /// each refinement iteration discovers genuinely new predicates.
    #[derive(Debug)]
    struct MockSpuriousFeasibility;

    impl FeasibilityChecker for MockSpuriousFeasibility {
        fn check_feasibility(
            &self,
            counterexample: &Counterexample,
            _blocks: &[BasicBlock],
            _predicates: &[Predicate],
        ) -> Result<FeasibilityResult, CegarError> {
            // Extract the integer value from the counterexample to vary formulas.
            let bound = counterexample
                .assignments
                .iter()
                .find_map(|(_, v)| match v {
                    CounterexampleValue::Int(n) => Some(*n),
                    _ => None,
                })
                .unwrap_or(0);

            // Each counterexample produces unique path formulas so that
            // interpolation discovers new predicates each round.
            let var_name = format!("v{}", bound.unsigned_abs());
            Ok(FeasibilityResult::Spurious {
                path_a: vec![(
                    "a0".to_string(),
                    Formula::Lt(
                        Box::new(Formula::Var(var_name.clone(), Sort::Int)),
                        Box::new(Formula::Int(bound)),
                    ),
                )],
                path_b: vec![(
                    "b0".to_string(),
                    Formula::Ge(
                        Box::new(Formula::Var(var_name, Sort::Int)),
                        Box::new(Formula::Int(bound + 100)),
                    ),
                )],
                unsat_core: UnsatCore::new(vec!["a0".into(), "b0".into()]),
            })
        }
    }

    /// Mock feasibility checker that always says feasible.
    #[derive(Debug)]
    struct MockFeasibleChecker;

    impl FeasibilityChecker for MockFeasibleChecker {
        fn check_feasibility(
            &self,
            _counterexample: &Counterexample,
            _blocks: &[BasicBlock],
            _predicates: &[Predicate],
        ) -> Result<FeasibilityResult, CegarError> {
            Ok(FeasibilityResult::Feasible)
        }
    }

    // Helper: simple program blocks.
    fn test_blocks() -> Vec<BasicBlock> {
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Goto(BlockId(1)),
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![],
                terminator: Terminator::Return,
            },
        ]
    }

    // -----------------------------------------------------------------------
    // Test 1: Safe in 1 iteration (coarse abstraction sufficient)
    // -----------------------------------------------------------------------

    #[test]
    fn test_cegar_loop_safe_in_one_iteration() {
        let checker = MockSafeChecker::new(0); // immediately safe
        let feasibility = MockSpuriousFeasibility;
        let refiner = InterpolatingRefiner;
        let config = LoopConfig {
            max_iterations: 10,
            timeout: Duration::from_secs(60),
            initial_predicates: vec![],
        };

        let driver = CegarDriver::new(checker, feasibility, refiner, config);
        let result = driver.run(&test_blocks()).expect("should not error");

        match result {
            LoopOutcome::Proved { iterations, predicates } => {
                assert_eq!(iterations, 0, "safe on first check, no refinements");
                assert_eq!(predicates, 0, "no predicates needed");
            }
            other => panic!("expected Proved, got: {other:?}"),
        }
    }

    // -----------------------------------------------------------------------
    // Test 2: Program needing 2 refinements (predicates discovered)
    // -----------------------------------------------------------------------

    #[test]
    fn test_cegar_loop_two_refinements_then_safe() {
        let checker = MockSafeChecker::new(2); // 2 spurious rounds, then safe
        let feasibility = MockSpuriousFeasibility;
        let refiner = InterpolatingRefiner;
        let config = LoopConfig {
            max_iterations: 10,
            timeout: Duration::from_secs(60),
            initial_predicates: vec![],
        };

        let driver = CegarDriver::new(checker, feasibility, refiner, config);
        let result = driver.run(&test_blocks()).expect("should not error");

        match result {
            LoopOutcome::Proved { iterations, predicates } => {
                assert_eq!(iterations, 2, "two refinement iterations");
                assert!(predicates > 0, "predicates should have been discovered");
            }
            other => panic!("expected Proved after 2 refinements, got: {other:?}"),
        }
    }

    // -----------------------------------------------------------------------
    // Test 3: Real counterexample found (feasible trace)
    // -----------------------------------------------------------------------

    #[test]
    fn test_cegar_loop_real_counterexample() {
        let checker = MockUnsafeChecker;
        let feasibility = MockFeasibleChecker;
        let refiner = InterpolatingRefiner;
        let config = LoopConfig {
            max_iterations: 10,
            timeout: Duration::from_secs(60),
            initial_predicates: vec![],
        };

        let driver = CegarDriver::new(checker, feasibility, refiner, config);
        let result = driver.run(&test_blocks()).expect("should not error");

        match result {
            LoopOutcome::Disproved { counterexample, iteration } => {
                assert_eq!(iteration, 1, "found on first iteration");
                assert!(
                    counterexample.assignments.iter().any(|(n, _)| n == "x"),
                    "counterexample should contain x"
                );
            }
            other => panic!("expected Disproved, got: {other:?}"),
        }
    }

    // -----------------------------------------------------------------------
    // Test 4: Resource limit hit
    // -----------------------------------------------------------------------

    #[test]
    fn test_cegar_loop_resource_exhausted() {
        // Checker always produces counterexamples, feasibility always says
        // spurious, so we keep refining until the iteration limit.
        let checker = MockSafeChecker::new(usize::MAX); // never reports safe
        let feasibility = MockSpuriousFeasibility;
        let refiner = InterpolatingRefiner;
        let config = LoopConfig {
            max_iterations: 3,
            timeout: Duration::from_secs(60),
            initial_predicates: vec![],
        };

        let driver = CegarDriver::new(checker, feasibility, refiner, config);
        let result = driver.run(&test_blocks()).expect("should not error");

        match result {
            LoopOutcome::ResourceExhausted { reason, iterations, predicates } => {
                assert_eq!(reason, "max_iterations");
                assert_eq!(iterations, 3);
                assert!(predicates > 0, "some predicates should have been discovered");
            }
            other => panic!("expected ResourceExhausted, got: {other:?}"),
        }
    }

    // -----------------------------------------------------------------------
    // Additional coverage tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_loop_config_default() {
        let cfg = LoopConfig::default();
        assert_eq!(cfg.max_iterations, 100);
        assert_eq!(cfg.timeout, Duration::from_secs(300));
        assert!(cfg.initial_predicates.is_empty());
    }

    #[test]
    fn test_loop_outcome_variants_debug() {
        let proved = LoopOutcome::Proved { iterations: 1, predicates: 3 };
        assert!(format!("{proved:?}").contains("Proved"));

        let disproved = LoopOutcome::Disproved {
            counterexample: Counterexample::new(vec![]),
            iteration: 2,
        };
        assert!(format!("{disproved:?}").contains("Disproved"));

        let exhausted = LoopOutcome::ResourceExhausted {
            reason: "timeout".into(),
            iterations: 5,
            predicates: 10,
        };
        assert!(format!("{exhausted:?}").contains("ResourceExhausted"));
    }

    #[test]
    fn test_cegar_loop_with_initial_predicates() {
        use crate::predicate::CmpOp;

        let checker = MockSafeChecker::new(1); // 1 spurious, then safe
        let feasibility = MockSpuriousFeasibility;
        let refiner = InterpolatingRefiner;
        let config = LoopConfig {
            max_iterations: 10,
            timeout: Duration::from_secs(60),
            initial_predicates: vec![
                Predicate::comparison("x", CmpOp::Ge, "0"),
            ],
        };

        let driver = CegarDriver::new(checker, feasibility, refiner, config);
        let result = driver.run(&test_blocks()).expect("should not error");

        match result {
            LoopOutcome::Proved { iterations, predicates } => {
                assert_eq!(iterations, 1);
                // Should have the initial predicate plus discovered ones.
                assert!(predicates >= 1);
            }
            other => panic!("expected Proved, got: {other:?}"),
        }
    }

    #[test]
    fn test_interpolating_refiner_produces_predicates() {
        let refiner = InterpolatingRefiner;
        let cex = Counterexample::new(vec![
            ("x".to_string(), CounterexampleValue::Int(-5)),
        ]);
        let path_a = vec![(
            "a0".to_string(),
            Formula::Lt(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
        )];
        let path_b = vec![(
            "b0".to_string(),
            Formula::Ge(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(10)),
            ),
        )];
        let core = UnsatCore::new(vec!["a0".into(), "b0".into()]);

        let preds = refiner.refine(&cex, &path_a, &path_b, &core, &[])
            .expect("should not error");
        assert!(!preds.is_empty(), "interpolation should produce predicates");
    }

    #[test]
    fn test_interpolating_refiner_heuristic_fallback() {
        let refiner = InterpolatingRefiner;
        let cex = Counterexample::new(vec![
            ("y".to_string(), CounterexampleValue::Int(42)),
        ]);
        // Empty path formulas + empty core => heuristic fallback.
        let preds = refiner.refine(&cex, &[], &[], &UnsatCore::default(), &[])
            .expect("should not error");
        assert!(!preds.is_empty(), "heuristic should produce predicates");
    }

    #[test]
    fn test_interpolating_refiner_filters_existing() {
        use crate::predicate::CmpOp;

        let refiner = InterpolatingRefiner;
        let cex = Counterexample::new(vec![
            ("z".to_string(), CounterexampleValue::Int(5)),
        ]);
        let existing = vec![
            Predicate::comparison("z", CmpOp::Ge, "0"),
            Predicate::comparison("z", CmpOp::Eq, "5"),
        ];
        let preds = refiner.refine(&cex, &[], &[], &UnsatCore::default(), &existing)
            .expect("should not error");
        // The predicates z >= 0 and z == 5 are already known; only novel ones returned.
        for p in &preds {
            assert!(!existing.contains(p), "should not return existing predicate: {p}");
        }
    }

    #[test]
    fn test_feasibility_result_variants() {
        let feasible = FeasibilityResult::Feasible;
        assert!(format!("{feasible:?}").contains("Feasible"));

        let spurious = FeasibilityResult::Spurious {
            path_a: vec![],
            path_b: vec![],
            unsat_core: UnsatCore::default(),
        };
        assert!(format!("{spurious:?}").contains("Spurious"));
    }
}
