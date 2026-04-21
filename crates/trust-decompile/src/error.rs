// trust-decompile error types
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

/// Errors that can occur during decompilation.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum DecompileError {
    /// A type could not be converted to a Rust type string.
    #[error("unsupported type: {0}")]
    UnsupportedType(String),

    /// A control-flow pattern could not be lowered to structured Rust.
    #[error("unsupported control flow in block {block}: {detail}")]
    UnsupportedControlFlow { block: usize, detail: String },

    /// An operand or rvalue variant is not yet handled.
    #[error("unsupported IR construct: {0}")]
    UnsupportedConstruct(String),

    /// The function body has no blocks.
    #[error("empty function body (no basic blocks)")]
    EmptyBody,
}
