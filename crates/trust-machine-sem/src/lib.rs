#![allow(dead_code)]
//! trust-machine-sem: ISA semantics formalization
//!
//! Maps decoded instructions to their logical effects on machine state.
//! Used by translation validation to verify compiled output matches source
//! semantics.
//!
//! Author: Andrew Yates <andrew@andrewdyates.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

pub(crate) mod aarch64;
pub(crate) mod x86_64;
pub(crate) mod effect;
pub(crate) mod error;
pub(crate) mod semantics;
pub(crate) mod state;

pub use aarch64::Aarch64Semantics;
pub use x86_64::X86_64Semantics;
// tRust: #564 — re-export condition_to_formula for semantic_lift branch wiring.
pub use aarch64::condition_to_formula;
pub use effect::Effect;
pub use error::SemError;
pub use semantics::Semantics;
pub use state::{Flags, MachineState};

#[cfg(test)]
mod tests;
