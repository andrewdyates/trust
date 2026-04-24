//! trust-lift: Proof-producing binary lifter
//!
//! Lifts binary code into tMIR functions with CFG recovery and SSA construction.
//! Pipeline: binary bytes -> disassembly -> basic block recovery -> CFG ->
//! SSA construction -> tMIR functions.
//!
//! Each lifted tMIR statement links back to its binary offset for proof annotation.
//!
//! Author: Andrew Yates <andrew@andrewdyates.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

#![allow(rustc::default_hash_types, rustc::potential_query_instability)]
// dead_code audit: crate-level suppression removed (#939)

pub mod binary;
pub(crate) mod boundary;
pub(crate) mod calling_convention;
pub mod cfg;
pub(crate) mod cfg_builder;
pub(crate) mod error;
pub(crate) mod lifter;
pub mod semantic_lift;
pub(crate) mod ssa;
#[cfg(feature = "z4-verify")]
pub(crate) mod validation;

pub use binary::{
    BinaryFunctionSelection, BinaryLiftOptions, LiftedBinary, LiftedFunctionFailure,
    lift_binary_to_tmir,
};
pub use boundary::FunctionBoundary;
pub use calling_convention::{CallingConvention, FunctionSignature};
pub use cfg::LiftedFunction;
pub use error::LiftError;
pub use lifter::{LiftArch, Lifter};
pub use semantic_lift::LocalLayout;
