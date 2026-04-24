//! trust-llvm2-bridge: Bridge between trust-types VerifiableFunction and LLVM2 LIR
//!
//! Converts trust-types IR (VerifiableFunction, BasicBlock, Statement, Terminator)
//! into LLVM2 LIR (Function, BasicBlock, Instruction) for verified code generation.
//!
//! Scope: scalars, aggregates (tuples/ADTs/arrays), function calls, memory
//! operations (load/store/stack slots), casts, drops, and discriminants.
//!
//! Author: Andrew Yates <andrew@andrewdyates.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

// tRust: FxHashMap for internal maps; std HashMap only where required by llvm2-lower API (#827)
#![allow(clippy::module_name_repetitions)]

// tRust: #828 — validation of lowered LIR for structural consistency.
pub mod validation;

// tRust: #826 — gate codegen_verify behind z4-proofs feature; z4 not in default deps.
#[cfg(feature = "z4-proofs")]
pub mod codegen_verify;

// tRust: #823 — gate translation validation behind transval feature.
#[cfg(feature = "transval")]
pub mod transval;

// tRust: #831 — gate full SMT-backed translation validation behind transval-full feature.
#[cfg(feature = "transval-full")]
pub mod transval_full;

// tRust: #829 — CodegenBackend scaffold for LLVM2 integration.
pub mod codegen_backend;

// tRust: #948 — split monolithic lib.rs into focused modules.
mod lift;
mod lower;
pub(crate) mod mapping;

#[cfg(test)]
mod tests;

// ---------------------------------------------------------------------------
// Error type
// ---------------------------------------------------------------------------

/// Errors during trust-types to LLVM2 LIR conversion.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum BridgeError {
    #[error("unsupported type: {0}")]
    UnsupportedType(String),

    #[error("unsupported operation: {0}")]
    UnsupportedOp(String),

    #[error("missing block: bb{0}")]
    MissingBlock(usize),

    #[error("missing local: _{0}")]
    MissingLocal(usize),

    #[error("empty function body: no basic blocks")]
    EmptyBody,

    #[error("invalid MIR: {0}")]
    InvalidMir(String),
}

// ---------------------------------------------------------------------------
// Public API re-exports
// ---------------------------------------------------------------------------

pub use lift::lift_from_lir;
pub use lower::{lower_body_to_lir, lower_to_lir};
pub use mapping::{map_binop, map_float_binop, map_type, map_unop};
