// trust-cegar: Inner refinement strategy enum
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};

/// Strategy for refining the abstraction after a spurious counterexample.
///
/// Each strategy targets a different aspect of the abstraction:
/// - PredicateRefinement: discover new predicates from the counterexample values
/// - TraceRefinement: walk the counterexample trace and refine at each step
/// - InterpolantBased: use Craig interpolation from unsat cores
/// - RustSemanticRefinement: use Rust ownership/borrowing/lifetime semantics
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum InnerRefinementStrategy {
    /// Discover predicates from counterexample variable assignments.
    ///
    /// Cheapest strategy: extracts boundary predicates (x >= 0, x == val)
    /// and pairwise comparisons between variables. Good for simple cases
    /// but may require many iterations for complex abstractions.
    PredicateRefinement,

    /// Walk the counterexample trace step-by-step and refine at each
    /// block where the abstract state is imprecise.
    ///
    /// More targeted than pure predicate refinement: identifies the
    /// specific program point where the abstraction is too coarse.
    TraceRefinement,

    /// Use Craig interpolation from an unsat core to discover predicates
    /// that separate the infeasible prefix from the suffix.
    ///
    /// Most precise strategy when an SMT solver provides unsat cores.
    /// Produces minimal, targeted predicates. Falls back to predicate
    /// refinement if no unsat core is available.
    InterpolantBased,

    /// Use Rust-specific ownership, borrowing, and lifetime semantics
    /// to refine the abstraction.
    ///
    /// This strategy exploits Rust's type system guarantees to:
    /// - Add ownership-state predicates (owned, borrowed, moved)
    /// - Add borrow-check predicates (aliasing rules)
    /// - Refine lifetime constraints from borrow patterns
    /// - Add interval predicates from type-range violations
    ///
    /// Falls back to predicate refinement for variables that have no
    /// Rust-specific semantic information. Most effective when the
    /// `RustAbstractionDomain` is populated with type/ownership info.
    RustSemanticRefinement,
}

impl std::fmt::Display for InnerRefinementStrategy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::PredicateRefinement => write!(f, "predicate"),
            Self::TraceRefinement => write!(f, "trace"),
            Self::InterpolantBased => write!(f, "interpolant"),
            Self::RustSemanticRefinement => write!(f, "rust-semantic"),
        }
    }
}
