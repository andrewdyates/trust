#![allow(dead_code)]
//! trust-disasm: Multi-architecture instruction decoder
//!
//! Author: Andrew Yates <andrew@andrewdyates.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

pub mod arch;
pub(crate) mod error;
pub mod operand;
pub mod opcode;
pub mod instruction;
pub mod aarch64;
pub mod x86_64;

pub use arch::{Arch, Decoder};
pub use error::DisasmError;
pub use instruction::{ControlFlow, Instruction};
pub use operand::{Condition, Operand, Register, ShiftType};
pub use opcode::Opcode;

/// Convenience: decode a single AArch64 instruction from bytes at a given address.
pub fn decode_aarch64(bytes: &[u8], address: u64) -> Result<Instruction, DisasmError> {
    let decoder = aarch64::Aarch64Decoder::new();
    decoder.decode(bytes, address)
}

/// Convenience: decode a single x86-64 instruction from bytes at a given address.
pub fn decode_x86_64(bytes: &[u8], address: u64) -> Result<Instruction, DisasmError> {
    let decoder = x86_64::X86_64Decoder::new();
    decoder.decode(bytes, address)
}
