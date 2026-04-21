// trust-zani-lib configuration types
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

//! Configuration for zani library verification.
//!
//! `ZaniConfig` controls BMC depth, timeout, and solver behavior.
//! `DiagConfig` controls how zani diagnostics are emitted during verification.

use serde::{Deserialize, Serialize};

/// Configuration for zani verification.
///
/// Controls BMC depth, timeout, solver path, and diagnostic behavior.
/// Matches the `ZaniConfig` signature from the Pipeline v2 design.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ZaniConfig {
    /// BMC unrolling depth. Higher values explore more execution paths
    /// but increase solving time. Default: 100.
    pub bmc_depth: u32,

    /// Timeout in milliseconds for the solver. Default: 30,000 (30s).
    pub timeout_ms: u64,

    /// Path to the zani binary for subprocess mode.
    /// If `None`, probes `ZANI_PATH` env var then `PATH`.
    pub solver_path: Option<String>,

    /// Extra arguments passed to the zani solver.
    pub solver_args: Vec<String>,

    /// Diagnostic configuration controlling how zani messages are handled.
    pub diagnostics: DiagConfig,

    /// Whether to request proof certificates from the solver.
    pub produce_proofs: bool,

    /// Whether to request counterexample models on SAT results.
    pub produce_models: bool,

    /// Whether to use adaptive BMC depth based on formula complexity.
    pub adaptive_depth: bool,
}

impl Default for ZaniConfig {
    fn default() -> Self {
        Self {
            bmc_depth: 100,
            timeout_ms: 30_000,
            solver_path: None,
            solver_args: vec!["-smt2".to_string(), "-in".to_string()],
            diagnostics: DiagConfig::default(),
            produce_proofs: false,
            produce_models: true,
            adaptive_depth: false,
        }
    }
}

impl ZaniConfig {
    /// Create a new config with default settings.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Set the BMC unrolling depth.
    #[must_use]
    pub fn with_bmc_depth(mut self, depth: u32) -> Self {
        self.bmc_depth = depth;
        self
    }

    /// Set the timeout in milliseconds.
    #[must_use]
    pub fn with_timeout(mut self, timeout_ms: u64) -> Self {
        self.timeout_ms = timeout_ms;
        self
    }

    /// Set an explicit solver path.
    #[must_use]
    pub fn with_solver_path(mut self, path: impl Into<String>) -> Self {
        self.solver_path = Some(path.into());
        self
    }

    /// Set the diagnostic configuration.
    #[must_use]
    pub fn with_diagnostics(mut self, diagnostics: DiagConfig) -> Self {
        self.diagnostics = diagnostics;
        self
    }

    /// Enable or disable proof certificate production.
    #[must_use]
    pub fn with_proofs(mut self, produce: bool) -> Self {
        self.produce_proofs = produce;
        self
    }

    /// Enable or disable adaptive BMC depth.
    #[must_use]
    pub fn with_adaptive_depth(mut self, enabled: bool) -> Self {
        self.adaptive_depth = enabled;
        self
    }
}

/// Controls how zani diagnostic messages are handled during verification.
///
/// In subprocess mode, diagnostics come from stderr. In direct mode (Phase 2),
/// diagnostics are intercepted from `span_err` / `span_warn` calls.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[derive(Default)]
pub enum DiagConfig {
    /// Suppress all diagnostic output (default for library use).
    #[default]
    Silent,

    /// Capture diagnostics into the `ZaniResult::diagnostics` vector
    /// for programmatic consumption.
    Capture,

    /// Pass diagnostics through to stderr (useful for debugging).
    Passthrough,
}

