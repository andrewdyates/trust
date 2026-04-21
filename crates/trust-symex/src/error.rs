// trust-symex error types
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use thiserror::Error;

/// Errors arising during symbolic execution.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum SymexError {
    #[error("undefined variable: {0}")]
    UndefinedVariable(String),

    #[error("unsupported operation: {0}")]
    UnsupportedOperation(String),

    #[error("execution depth limit exceeded: {depth} > {limit}")]
    DepthLimitExceeded { depth: usize, limit: usize },

    #[error("no more paths to explore")]
    ExplorationExhausted,

    #[error("type mismatch: expected {expected}, got {actual}")]
    TypeMismatch { expected: String, actual: String },

    #[error("unreachable block reached during execution")]
    UnreachableReached,
}
