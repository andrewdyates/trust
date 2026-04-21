// trust-lift error types
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use thiserror::Error;

/// Errors that can occur during binary lifting.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum LiftError {
    /// Binary parsing failed (requires `macho` or `elf` feature).
    #[cfg(any(feature = "macho", feature = "elf"))]
    #[error("binary parse error: {0}")]
    Parse(#[from] trust_binary_parse::ParseError),

    /// Binary parsing failed (generic message without binary-parse features).
    #[cfg(not(any(feature = "macho", feature = "elf")))]
    #[error("binary parse error: {0}")]
    Parse(String),

    /// Unsupported ELF machine type for lifting.
    #[error("unsupported ELF machine type: 0x{0:x}")]
    UnsupportedMachine(u16),

    /// Instruction decoding failed at the given address.
    #[error("disassembly error at 0x{address:x}: {source}")]
    Disasm {
        address: u64,
        source: trust_disasm::DisasmError,
    },

    /// No text section found in the binary.
    #[error("no text section found in binary")]
    NoTextSection,

    /// The requested entry point is outside the text section.
    #[error("entry point 0x{entry:x} is outside text section [0x{text_start:x}..0x{text_end:x})")]
    EntryOutOfBounds {
        entry: u64,
        text_start: u64,
        text_end: u64,
    },

    /// No function found at the given address.
    #[error("no function found at address 0x{0:x}")]
    NoFunctionAtAddress(u64),

    /// SSA construction failed.
    #[error("SSA construction error: {0}")]
    Ssa(String),

    /// Block contained no instructions after decoding.
    #[error("empty block at address 0x{address:x}")]
    EmptyBlock {
        address: u64,
    },
}
