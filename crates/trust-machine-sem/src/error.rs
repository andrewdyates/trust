// trust-machine-sem error types
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_disasm::Opcode;

/// Errors produced during instruction semantics evaluation.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum SemError {
    /// The instruction opcode is not yet modeled.
    #[error("unsupported opcode: {0}")]
    UnsupportedOpcode(Opcode),

    /// An operand was missing or had unexpected form.
    #[error("invalid operand at index {index} for {opcode}: {detail}")]
    InvalidOperand {
        opcode: Opcode,
        index: usize,
        detail: String,
    },

    /// Register width mismatch in an operation.
    #[error("width mismatch: expected {expected}-bit, got {actual}-bit")]
    WidthMismatch { expected: u32, actual: u32 },
}
