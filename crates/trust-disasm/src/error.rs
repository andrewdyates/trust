// trust-disasm error types
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

/// Errors that can occur during instruction decoding.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum DisasmError {
    /// Not enough bytes to decode an instruction.
    #[error("insufficient bytes: need {needed}, have {available}")]
    InsufficientBytes { needed: usize, available: usize },

    /// The encoding does not match any known instruction.
    #[error("unknown instruction encoding: 0x{encoding:08x} at 0x{address:x}")]
    UnknownEncoding { encoding: u32, address: u64 },

    /// A reserved or unallocated encoding was encountered.
    #[error("unallocated encoding: 0x{encoding:08x} at 0x{address:x}")]
    UnallocatedEncoding { encoding: u32, address: u64 },
}
