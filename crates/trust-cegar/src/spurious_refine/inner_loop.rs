// trust-cegar: Spurious counterexample refinement inner loop
//
// The main loop that processes counterexamples: checks feasibility,
// applies refinement strategies, and detects convergence.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{BasicBlock, Counterexample, Formula};

use crate::error::CegarError;
use crate::interpolation::UnsatCore;
use crate::predicate::{Predicate, abstract_block};
use crate::rust_abstraction::RustAbstractionDomain;

use super::checker::{CexCheckResult, CounterexampleChecker};
use super::refinement::{interpolant_refine, predicate_refine, rust_semantic_refine, trace_refine};
use super::strategy::InnerRefinementStrategy;

/// Configuration for the spurious counterexample refinement inner loop.
#[derive(Debug, Clone)]
pub struct InnerLoopConfig {
    /// Maximum refinement attempts per counterexample before giving up.
    pub max_inner_iterations: usize,
    /// Strategy to use for refinement.
    pub strategy: InnerRefinementStrategy,
    /// Enable fixed-point detection: stop if no new predicates are discovered.
    pub detect_fixed_point: bool,
    /// Maximum predicate set size before forcing convergence.
    pub max_predicates: usize,
}

impl Default for InnerLoopConfig {
    fn default() -> Self {
        Self {
            max_inner_iterations: 20,
            strategy: InnerRefinementStrategy::InterpolantBased,
            detect_fixed_point: true,
            max_predicates: 500,
        }
    }
}

/// Outcome of the inner refinement loop for a single counterexample.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum InnerLoopOutcome {
    /// The counterexample is feasible (a real bug).
    RealCounterexample,

    /// The abstraction was refined to eliminate the spurious counterexample.
    Refined {
        /// New predicates discovered during refinement.
        new_predicates: Vec<Predicate>,
        /// Number of inner iterations performed.
        inner_iterations: usize,
        /// Strategy that produced the refinement.
        strategy_used: InnerRefinementStrategy,
    },

    /// Refinement converged without new predicates (fixed point reached).
    FixedPoint {
        /// Number of inner iterations before fixed point.
        iterations: usize,
    },

    /// Feasibility could not be determined (syntactic analysis inconclusive,
    /// no SMT solver available). The caller should not treat this as a real
    /// counterexample -- it may be spurious.
    Unknown,

    /// Inner loop resource limits exhausted.
    InnerLimitExhausted {
        /// Reason for exhaustion.
        reason: String,
        /// Iterations completed.
        iterations: usize,
    },
}

/// Statistics tracked during the inner refinement loop.
#[derive(Debug, Clone, Default)]
pub struct InnerLoopStats {
    /// Total inner iterations across all counterexamples.
    pub total_inner_iterations: usize,
    /// Number of counterexamples checked.
    pub counterexamples_checked: usize,
    /// Number found to be feasible (real).
    pub feasible_count: usize,
    /// Number found to be spurious and refined away.
    pub spurious_count: usize,
    /// Number of fixed points detected.
    pub fixed_point_count: usize,
    /// Total predicates discovered across all inner loops.
    pub total_predicates_discovered: usize,
}

/// The spurious counterexample refinement inner loop.
///
/// Given an abstract counterexample, this loop:
/// 1. Checks feasibility using `CounterexampleChecker`
/// 2. If spurious, applies the selected refinement strategy
/// 3. Re-checks if the refined abstraction eliminates the counterexample
/// 4. Repeats until the CEX is eliminated, proven real, or limits hit
///
/// This is the "inner" loop in CEGAR: the outer loop generates abstract
/// counterexamples via model checking; this inner loop handles each one.
#[derive(Debug)]
pub struct SpuriousRefinementLoop {
    /// Current predicate set.
    predicates: Vec<Predicate>,
    /// Configuration.
    config: InnerLoopConfig,
    /// Accumulated statistics.
    stats: InnerLoopStats,
    /// History of predicate set sizes for convergence detection.
    predicate_count_history: Vec<usize>,
    /// Optional Rust-specific abstraction domain for the `RustSemanticRefinement`
    /// strategy. When set, the inner loop can exploit ownership, borrowing, and
    /// lifetime semantics to produce more targeted predicates.
    rust_domain: Option<RustAbstractionDomain>,
}

impl SpuriousRefinementLoop {
    /// Create a new inner refinement loop.
    #[must_use]
    pub fn new(initial_predicates: Vec<Predicate>, config: InnerLoopConfig) -> Self {
        Self {
            predicates: initial_predicates,
            config,
            stats: InnerLoopStats::default(),
            predicate_count_history: Vec::new(),
            rust_domain: None,
        }
    }

    /// Create a new inner refinement loop with a Rust abstraction domain.
    ///
    /// The domain provides ownership, borrowing, and lifetime information
    /// that the `RustSemanticRefinement` strategy uses to produce
    /// Rust-specific predicates.
    #[must_use]
    pub fn with_rust_domain(
        initial_predicates: Vec<Predicate>,
        config: InnerLoopConfig,
        domain: RustAbstractionDomain,
    ) -> Self {
        Self {
            predicates: initial_predicates,
            config,
            stats: InnerLoopStats::default(),
            predicate_count_history: Vec::new(),
            rust_domain: Some(domain),
        }
    }

    /// Set or update the Rust abstraction domain.
    pub fn set_rust_domain(&mut self, domain: RustAbstractionDomain) {
        self.rust_domain = Some(domain);
    }

    /// Access the Rust abstraction domain, if set.
    #[must_use]
    pub fn rust_domain(&self) -> Option<&RustAbstractionDomain> {
        self.rust_domain.as_ref()
    }

    /// Access the current predicate set.
    #[must_use]
    pub fn predicates(&self) -> &[Predicate] {
        &self.predicates
    }

    /// Access accumulated statistics.
    #[must_use]
    pub fn stats(&self) -> &InnerLoopStats {
        &self.stats
    }

    /// Process a single abstract counterexample through the inner loop.
    ///
    /// # Arguments
    /// * `cex` - The abstract counterexample to process.
    /// * `blocks` - Basic blocks of the program.
    ///
    /// # Errors
    /// Returns `CegarError::RefinementStalled` if no strategy produces new predicates.
    pub fn process_counterexample(
        &mut self,
        cex: &Counterexample,
        blocks: &[BasicBlock],
    ) -> Result<InnerLoopOutcome, CegarError> {
        self.stats.counterexamples_checked += 1;

        // Compute abstract states under current predicates.
        let abstract_states = blocks
            .iter()
            .map(|b| abstract_block(b, &self.predicates))
            .collect();

        let checker = CounterexampleChecker::new(abstract_states);
        let mut inner_iteration = 0;

        // Single-pass refinement: check the counterexample once and return.
        // (Originally a `loop {}` but every path returns, so it never iterated.)

        // Check resource limits.
        if inner_iteration >= self.config.max_inner_iterations {
            self.stats.total_inner_iterations += inner_iteration;
            return Ok(InnerLoopOutcome::InnerLimitExhausted {
                reason: "max_inner_iterations".to_string(),
                iterations: inner_iteration,
            });
        }

        if self.predicates.len() >= self.config.max_predicates {
            self.stats.total_inner_iterations += inner_iteration;
            return Ok(InnerLoopOutcome::InnerLimitExhausted {
                reason: "max_predicates".to_string(),
                iterations: inner_iteration,
            });
        }

        // Step 1: Check feasibility.
        let check_result = checker.check(cex, blocks);
        inner_iteration += 1;

        match check_result {
            CexCheckResult::Feasible => {
                self.stats.feasible_count += 1;
                self.stats.total_inner_iterations += inner_iteration;
                Ok(InnerLoopOutcome::RealCounterexample)
            }
            CexCheckResult::Unknown => {
                // Syntactic analysis was inconclusive. Do not treat as
                // a real counterexample -- that would cause false alarms.
                self.stats.total_inner_iterations += inner_iteration;
                Ok(InnerLoopOutcome::Unknown)
            }
            CexCheckResult::Spurious { path_a, path_b, unsat_core, .. } => {
                // Step 2: Apply refinement strategy.
                let new_preds = self.apply_strategy(
                    cex,
                    &path_a,
                    &path_b,
                    &unsat_core,
                )?;

                // Step 3: Check for convergence (fixed point).
                let mut actually_new = Vec::new();
                for pred in new_preds {
                    if !self.predicates.contains(&pred) {
                        self.predicates.push(pred.clone());
                        actually_new.push(pred);
                    }
                }

                self.predicate_count_history.push(self.predicates.len());
                self.stats.total_predicates_discovered += actually_new.len();

                if actually_new.is_empty() {
                    // No new predicates: fixed point.
                    if self.config.detect_fixed_point {
                        self.stats.fixed_point_count += 1;
                        self.stats.total_inner_iterations += inner_iteration;
                        return Ok(InnerLoopOutcome::FixedPoint {
                            iterations: inner_iteration,
                        });
                    }
                    // Without fixed-point detection, stall.
                    self.stats.total_inner_iterations += inner_iteration;
                    return Err(CegarError::RefinementStalled);
                }

                // Convergence check: if predicate count stabilized across
                // multiple iterations, we have reached a fixed point.
                if self.is_converged() {
                    self.stats.fixed_point_count += 1;
                    self.stats.total_inner_iterations += inner_iteration;
                    return Ok(InnerLoopOutcome::FixedPoint {
                        iterations: inner_iteration,
                    });
                }

                // Successfully refined.
                self.stats.spurious_count += 1;
                self.stats.total_inner_iterations += inner_iteration;
                Ok(InnerLoopOutcome::Refined {
                    new_predicates: actually_new,
                    inner_iterations: inner_iteration,
                    strategy_used: self.config.strategy,
                })
            }
        }
    }

    /// Apply the configured refinement strategy to extract new predicates.
    fn apply_strategy(
        &self,
        cex: &Counterexample,
        path_a: &[(String, Formula)],
        path_b: &[(String, Formula)],
        unsat_core: &UnsatCore,
    ) -> Result<Vec<Predicate>, CegarError> {
        match self.config.strategy {
            InnerRefinementStrategy::PredicateRefinement => {
                Ok(predicate_refine(cex, &self.predicates))
            }
            InnerRefinementStrategy::TraceRefinement => {
                Ok(trace_refine(cex, &self.predicates))
            }
            InnerRefinementStrategy::InterpolantBased => {
                interpolant_refine(cex, path_a, path_b, unsat_core, &self.predicates)
            }
            InnerRefinementStrategy::RustSemanticRefinement => {
                rust_semantic_refine(cex, &self.predicates, self.rust_domain.as_ref())
            }
        }
    }

    /// Detect convergence by checking if the predicate count has stabilized.
    ///
    /// A fixed point is detected when the predicate count remains the same
    /// across the last 3 iterations.
    fn is_converged(&self) -> bool {
        let history = &self.predicate_count_history;
        if history.len() < 3 {
            return false;
        }
        let n = history.len();
        history[n - 1] == history[n - 2] && history[n - 2] == history[n - 3]
    }
}
