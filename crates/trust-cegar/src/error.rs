// trust-cegar: CEGAR error types
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

/// Errors that can occur during CEGAR refinement.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum CegarError {
    /// The refinement loop exceeded the maximum number of iterations.
    #[error("CEGAR refinement exceeded maximum iterations ({max})")]
    MaxIterationsExceeded { max: usize },

    /// A counterexample path references a block index that does not exist.
    #[error("invalid block index {index} (function has {num_blocks} blocks)")]
    #[allow(dead_code)]
    InvalidBlockIndex { index: usize, num_blocks: usize },

    /// No new predicates could be extracted from a spurious counterexample.
    #[error("refinement stalled: no new predicates from spurious counterexample")]
    RefinementStalled,

    /// The abstraction is inconsistent (e.g., contradictory predicates).
    #[error("inconsistent abstraction: {reason}")]
    #[allow(dead_code)]
    InconsistentAbstraction { reason: String },

    /// The solver returned an unexpected result.
    #[error("solver error: {detail}")]
    SolverError { detail: String },

    /// An unhandled Formula variant was encountered during IC3 priming.
    #[error("prime_formula: unhandled Formula variant: {variant}")]
    UnhandledFormulaVariant { variant: String },
}
