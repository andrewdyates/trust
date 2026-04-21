#![allow(dead_code)]
// trust-zani-lib: Library facade for zani bounded model checker
//
// Phase 1 of Pipeline v2 (#789, designs/2026-04-14-verification-pipeline-v2.md).
// Exposes zani's core analysis as a library API that tRust can call directly
// instead of shelling out to the CLI binary.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

//! # trust-zani-lib
//!
//! Library facade for the zani bounded model checker. This crate provides:
//!
//! - **High-level API**: `verify_function` for end-to-end BMC/CHC verification
//! - **Low-level API**: `encode_function` for MIR-to-z4 encoding without solving
//! - **Re-exports**: `BmcVc`, `ChcVc`, `Violation`, `PropertyKind` from `zani_core`
//! - **Configuration**: `ZaniConfig`, `DiagConfig` for controlling verification behavior
//! - **Results**: `ZaniResult`, `Verdict`, `TypedCounterexample` for structured output
//!
//! ## Architecture
//!
//! ```text
//! tRust compiler pass (TyCtxt, DefId)
//!          |
//!          v
//!   trust-zani-lib  (this crate)
//!          |
//!          +--[trust-build]---> zani codegen_z4 in-process (Phase 2)
//!          |
//!          +--[default]-------> zani subprocess via CLI
//!          |
//!          v
//!     ZaniResult { verdict, counterexample, proof_certificate, violations }
//! ```
//!
//! ## Feature Flags
//!
//! - `trust-build`: Enables direct `TyCtxt` integration (requires rustc nightly).
//!   Without this flag, verification falls back to subprocess invocation.

mod config;
mod error;
mod result;
mod subprocess;

pub use config::{DiagConfig, ZaniConfig};
pub use error::ZaniLibError;
pub use result::{
    EncodingContext, TraceStep, TypedCounterexample, TypedValue, Verdict, ZaniResult,
};
pub use subprocess::SubprocessBackend;

// tRust: Re-export zani_core types for consumers that need the VC IR directly.
// These are the types from the zani repo's core crate, providing BMC/CHC
// verification condition containers, violation descriptors, and property kinds.
pub use zani_core::{BmcVc, ChcVc, PropertyKind, Violation};

// Additional re-exports for lower-level access
pub use zani_core::{
    ArtifactMetadata, BmcQuery, ChcQuery, Constraints, Decl, HarnessId, PropertyId,
    SourceLocation, VcArtifact, VerificationMode,
};

/// Verify a function using zani's bounded model checking.
///
/// This is the high-level entry point matching the Pipeline v2 design:
/// ```rust,ignore
/// let result = trust_zani_lib::verify_function(tcx, def_id, config);
/// ```
///
/// In the current Phase 1 implementation, this delegates to the subprocess
/// backend. When the `trust-build` feature is enabled (Phase 2), this will
/// call zani's `codegen_z4` directly in-process.
///
/// # Arguments
///
/// * `function_name` - The fully qualified function name to verify
/// * `smtlib_script` - The SMT-LIB2 script encoding the verification condition
/// * `config` - Verification configuration (timeout, depth, diagnostics)
///
/// # Errors
///
/// Returns `ZaniLibError` if the subprocess fails to spawn or produces
/// unparseable output.
pub fn verify_function(
    function_name: &str,
    smtlib_script: &str,
    config: &ZaniConfig,
) -> Result<ZaniResult, ZaniLibError> {
    let backend = SubprocessBackend::new(config);
    backend.verify(function_name, smtlib_script)
}

/// Encode a function's MIR into verification conditions without solving.
///
/// This is the lower-level API from the Pipeline v2 design (Challenge 7):
/// returns the z4 encoding context, local variable mappings, and base
/// constraint set. Callers can compose additional constraints before solving.
///
/// In Phase 1, this returns an `EncodingContext` with the SMT-LIB2 script
/// and metadata. In Phase 2 (trust-build), this will return z4 `Expr` trees
/// and solver context directly.
///
/// # Arguments
///
/// * `function_name` - The fully qualified function name to encode
/// * `smtlib_script` - The SMT-LIB2 script encoding the function
/// * `config` - Encoding configuration
///
/// # Errors
///
/// Returns `ZaniLibError` if encoding fails.
pub fn encode_function(
    function_name: &str,
    smtlib_script: &str,
    config: &ZaniConfig,
) -> Result<EncodingContext, ZaniLibError> {
    Ok(EncodingContext::from_smtlib(
        function_name.to_string(),
        smtlib_script.to_string(),
        config.bmc_depth,
    ))
}
