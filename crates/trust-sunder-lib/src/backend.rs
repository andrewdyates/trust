// trust-sunder-lib backend trait
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

//! Backend trait for pluggable sunder verification implementations.
//!
//! The `SunderBackend` trait defines the interface that both the CLI backend
//! (Phase 1) and the direct in-process backend (Phase 2) must implement.

use crate::contract::ContractSet;
use crate::error::SunderLibError;
use crate::result::{LoopInvariant, SunderResult};

/// Backend trait for sunder verification.
///
/// Implementations provide different strategies for invoking sunder:
/// - `CliBackend`: subprocess via the sunder CLI (Phase 1)
/// - Future: `DirectBackend` with `TyCtxt` integration (Phase 2, trust-build)
pub trait SunderBackend {
    /// Verify a function's contracts.
    ///
    /// # Arguments
    ///
    /// * `function_name` - The fully qualified function name to verify
    /// * `contracts` - The contract set (requires/ensures/invariants)
    ///
    /// # Errors
    ///
    /// Returns `SunderLibError` if verification fails due to infrastructure issues.
    fn verify(
        &self,
        function_name: &str,
        contracts: &ContractSet,
    ) -> Result<SunderResult, SunderLibError>;

    /// Infer loop invariants for a function.
    ///
    /// # Arguments
    ///
    /// * `function_name` - The fully qualified function name
    ///
    /// # Errors
    ///
    /// Returns `SunderLibError` if invariant inference fails.
    fn infer_invariants(&self, function_name: &str) -> Result<Vec<LoopInvariant>, SunderLibError>;
}
