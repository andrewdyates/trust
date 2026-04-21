// trust-vcgen/invariant_inference: Loop invariant inference
//
// Analyzes LoopInfo + InductionVar data from loop_analysis.rs to produce
// candidate invariants with confidence scores. Includes:
//
//   Pattern-based:
//   - Counter loop:       init <= var <= bound
//   - Accumulator:        acc >= 0 (when init=0, step positive, unsigned)
//   - Array iteration:    0 <= i < arr.len()
//   - Binary search:      low <= high
//
//   Abstract interpretation:
//   - infer_invariant_abstract(): runs fixpoint to extract interval bounds
//
//   Counterexample-guided:
//   - infer_from_counterexample(): derives invariants from CEX variable values
//
//   Verification:
//   - verify_invariant(): checks initiation + consecution conditions
//   - InvariantStatus: Verified, InitFailed, ConsecutionFailed, Unknown
//
//   Structural:
//   - detect_loops_dfs(): DFS-based loop detection (natural loops)
//   - OctagonDomain: relational domain (+-x +-y <= c)
//
// Candidates are ranked by confidence and can be injected into VCs via
// the existing inject_invariants() machinery in invariants.rs.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

mod abstract_bridge;
mod counterexample;
mod loop_detection;
mod octagon;
mod patterns;
mod verification;

#[cfg(test)]
mod tests;

use trust_types::*;

use crate::loop_analysis::LoopInfo;

// Re-exports: public API of this module
#[allow(unused_imports)]
pub(crate) use abstract_bridge::infer_invariant_abstract;
#[allow(unused_imports)]
pub(crate) use counterexample::{infer_from_counterexample, Counterexample};
#[allow(unused_imports)]
pub(crate) use loop_detection::detect_loops_dfs;
#[allow(unused_imports)]
pub(crate) use octagon::{OctagonConstraint, OctagonDomain};
#[allow(unused_imports)]
pub(crate) use verification::{verify_invariant, InvariantStatus};

/// How the invariant was discovered.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum InvariantPattern {
    /// Counter bounded: `init <= var <= bound`
    CounterLoop,
    /// Monotonic accumulator: `acc >= 0`
    Accumulator,
    /// Array iteration: `0 <= i < arr.len()`
    ArrayIteration,
    /// Binary search: `low <= high`
    BinarySearch,
    /// User-provided annotation
    UserAnnotated,
}

/// A candidate loop invariant with confidence score and source pattern.
#[derive(Debug, Clone)]
pub(crate) struct InvariantCandidate {
    /// The invariant formula (must hold at loop header on every iteration).
    pub(crate) expression: Formula,
    /// Confidence that this invariant is inductive [0.0, 1.0].
    pub(crate) confidence: f64,
    /// Which pattern produced this invariant.
    pub(crate) pattern: InvariantPattern,
    /// Which loop header this invariant applies to.
    pub(crate) loop_header: BlockId,
}

/// Infer loop invariants from loop analysis results.
///
/// Applies pattern-based heuristics to each loop's induction variables
/// and MIR structure. Returns candidates sorted by confidence (highest first).
#[must_use]
pub(crate) fn infer_loop_invariants(
    loop_info: &LoopInfo,
    func: &VerifiableFunction,
) -> Vec<InvariantCandidate> {
    let mut candidates = Vec::new();

    // User-annotated invariants (highest confidence)
    candidates.extend(patterns::extract_user_invariants(func, loop_info));

    // Pattern-based inference from induction variables
    for ivar in &loop_info.induction_vars {
        candidates.extend(patterns::infer_counter_loop(loop_info, ivar));
    }

    // Accumulator detection (scans all loop-modified variables, not just induction vars)
    candidates.extend(patterns::infer_accumulators(func, loop_info));

    // Structural patterns (don't require induction vars)
    candidates.extend(patterns::infer_array_iteration(func, loop_info));
    candidates.extend(patterns::infer_binary_search(func, loop_info));

    // Sort by confidence descending
    candidates.sort_by(|a, b| {
        b.confidence
            .partial_cmp(&a.confidence)
            .unwrap_or(std::cmp::Ordering::Equal)
    });
    candidates
}
