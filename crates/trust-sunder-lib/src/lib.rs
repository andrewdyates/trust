#![allow(dead_code)]
// trust-sunder-lib: Library facade for sunder deductive verifier
//
// Phase 1 of Pipeline v2 (#790, designs/2026-04-14-verification-pipeline-v2.md).
// Exposes sunder's deductive verification as a library API that tRust can call
// directly instead of shelling out to the CLI binary.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

//! # trust-sunder-lib
//!
//! Library facade for the sunder deductive verifier. This crate provides:
//!
//! - **Types**: `ContractSet`, `SunderResult`, `LoopInvariant` (standalone, no nightly)
//! - **Trait**: `SunderBackend` for pluggable verification backends
//! - **CLI backend**: `CliBackend` that invokes sunder as a subprocess
//! - **Configuration**: `SunderConfig`, `DiagConfig` for controlling verification
//! - **Results**: `SunderResult`, `Verdict`, `FunctionVerdict` for structured output
//!
//! ## Architecture
//!
//! ```text
//! tRust compiler pass (TyCtxt, DefId)
//!          |
//!          v
//!   trust-sunder-lib  (this crate)
//!          |
//!          +--[trust-build]---> sunder in-process (Phase 2)
//!          |
//!          +--[default]-------> sunder subprocess via CLI
//!          |
//!          v
//!     SunderResult { verdict, function_verdicts, loop_invariants }
//! ```
//!
//! ## Feature Flags
//!
//! - `trust-build`: Enables direct `TyCtxt` integration (requires rustc nightly).
//!   Without this flag, verification falls back to subprocess invocation.
//!
//! ## Why standalone types?
//!
//! `sunder-core` requires nightly Rust (`#![feature(box_patterns)]`). This crate
//! defines its own types that mirror sunder's API surface without the nightly
//! dependency. When `trust-build` is enabled in Phase 2, these types will be
//! bridged to sunder-core's native types.

mod backend;
mod cli;
mod config;
mod contract;
mod error;
mod result;

pub use backend::SunderBackend;
pub use cli::CliBackend;
pub use config::{DiagConfig, SunderConfig};
pub use contract::{Contract, ContractKind, ContractSet};
pub use error::SunderLibError;
pub use result::{FunctionVerdict, LoopInvariant, SunderResult, Verdict};

/// Verify a function's contracts using sunder's deductive verification.
///
/// This is the high-level entry point matching the Pipeline v2 design:
/// ```rust,ignore
/// let result = trust_sunder_lib::verify_with_contracts(
///     function_name, contracts, config,
/// );
/// ```
///
/// In the current Phase 1 implementation, this delegates to the CLI backend.
/// When the `trust-build` feature is enabled (Phase 2), this will call
/// sunder's verification context directly in-process via `TyCtxt`.
///
/// # Arguments
///
/// * `function_name` - The fully qualified function name to verify
/// * `contracts` - The contract set (requires/ensures/invariants)
/// * `config` - Verification configuration (timeout, diagnostics)
///
/// # Errors
///
/// Returns `SunderLibError` if the subprocess fails or produces
/// unparseable output.
pub fn verify_with_contracts(
    function_name: &str,
    contracts: &ContractSet,
    config: &SunderConfig,
) -> Result<SunderResult, SunderLibError> {
    let backend = CliBackend::new(config);
    backend.verify(function_name, contracts)
}

/// Infer loop invariants for a function using sunder.
///
/// This is the lower-level API from the Pipeline v2 design. Returns
/// candidate loop invariants discovered by sunder's abstract interpretation.
///
/// In Phase 1, this invokes sunder with `--infer-invariants` and parses
/// the output. In Phase 2 (trust-build), this will call sunder's
/// `infer_loop_invariants` directly.
///
/// # Arguments
///
/// * `function_name` - The fully qualified function name
/// * `config` - Verification configuration
///
/// # Errors
///
/// Returns `SunderLibError` if invariant inference fails.
pub fn infer_loop_invariants(
    function_name: &str,
    config: &SunderConfig,
) -> Result<Vec<LoopInvariant>, SunderLibError> {
    let backend = CliBackend::new(config);
    backend.infer_invariants(function_name)
}
