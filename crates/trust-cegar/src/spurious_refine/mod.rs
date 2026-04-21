// trust-cegar: Spurious counterexample refinement inner loop
//
// Implements the CEGAR inner loop for spurious counterexample detection and
// abstraction refinement. When the abstract model checker finds a
// counterexample, this module determines whether it is real (feasible on
// the concrete model) or spurious (an artifact of over-approximation).
// If spurious, it refines the abstraction to eliminate it.
//
// The inner loop:
//   1. Receive abstract counterexample from outer CEGAR loop
//   2. Check feasibility on the concrete model (CounterexampleChecker)
//   3. If feasible: report real bug
//   4. If spurious: select refinement strategy, extract new predicates
//   5. Detect convergence (fixed-point or resource limits)
//   6. Return refined abstraction to outer loop
//
// Part of #362: CEGAR inner loop: spurious counterexample refinement
//
// Reference: CPAchecker's CEGARAlgorithm + PredicateRefiner
//   refs/cpachecker/src/org/sosy_lab/cpachecker/core/algorithm/CEGARAlgorithm.java
//   refs/cpachecker/src/org/sosy_lab/cpachecker/cpa/predicate/PredicateCPARefiner.java
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

mod checker;
pub(crate) mod helpers;
mod inner_loop;
pub(crate) mod refinement;
mod strategy;

#[cfg(test)]
mod tests;

// Re-export public API
pub use checker::{CexCheckResult, CounterexampleChecker};
pub use inner_loop::{InnerLoopConfig, InnerLoopOutcome, InnerLoopStats, SpuriousRefinementLoop};
pub use strategy::InnerRefinementStrategy;
