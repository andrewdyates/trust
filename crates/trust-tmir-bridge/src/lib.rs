//! trust-tmir-bridge: Bridge between trust-types VerifiableFunction and tMIR
//!
//! Converts trust-types IR (VerifiableFunction, BasicBlock, Statement, Terminator)
//! into tMIR IR (Module, Function, Block, Inst) for downstream dMATH verification
//! and the universal t* compilation stack.
//!
//! This is a pure translation layer -- no analysis, no optimization. Maps tRust
//! MIR concepts to tMIR equivalents. Where there's no 1:1 mapping, the gap is
//! documented and the closest approximation is used.
//!
//! ## Design decisions
//!
//! - **tMIR uses SSA values (ValueId), tRust uses place-based locals.** Each
//!   trust-types local gets a tMIR ValueId. Place projections (field, index, deref)
//!   are lowered to tMIR `ExtractField`, `ExtractElement`, or `Load` instructions.
//!
//! - **tMIR has no unsigned integer types.** Signed/unsigned distinction is carried
//!   in operations (SDiv vs UDiv, ICmp Slt vs Ult), not in types. All integer
//!   types map to tMIR I8/I16/I32/I64/I128 by width.
//!
//! - **tMIR uses Overflow instructions for checked ops.** trust-types
//!   `CheckedBinaryOp` maps to `Inst::Overflow` which produces (value, bool).
//!
//! - **Contracts/specs are lowered to tMIR ProofAnnotations and ProofObligations.**
//!   Requires -> Precondition, Ensures -> Postcondition.
//!
//! Author: Andrew Yates <andrew@andrewdyates.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

#![forbid(unsafe_code)]
#![allow(clippy::module_name_repetitions)]

mod lower;

pub use lower::{
    BridgeError, lower_to_tmir, lower_to_tmir_function, map_binop, map_type, map_unop,
};

#[cfg(test)]
mod tests;
