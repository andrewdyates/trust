// trust-sunder-lib error types
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

//! Error types for the sunder library facade.

/// Errors from the sunder library integration.
#[derive(Debug, thiserror::Error)]
pub enum SunderLibError {
    /// The sunder binary was not found at the configured path or on PATH.
    #[error("sunder binary not found: {reason}")]
    BinaryNotFound {
        /// Details about where we looked.
        reason: String,
    },

    /// Failed to spawn the sunder subprocess.
    #[error("failed to spawn sunder subprocess: {0}")]
    SpawnFailed(#[from] std::io::Error),

    /// The subprocess exited with a non-zero code that indicates an internal error.
    #[error("sunder subprocess failed with exit code {code}: {stderr}")]
    SubprocessFailed {
        /// Exit code from the subprocess.
        code: i32,
        /// Captured stderr output.
        stderr: String,
    },

    /// Failed to parse sunder's output.
    #[error("failed to parse sunder output: {reason}")]
    ParseError {
        /// Details about what was unexpected.
        reason: String,
    },

    /// The verification timed out.
    #[error("sunder timed out after {timeout_ms}ms")]
    Timeout {
        /// The configured timeout that was exceeded.
        timeout_ms: u64,
    },

    /// Contract serialization error.
    #[error("contract serialization error: {reason}")]
    ContractError {
        /// Details about what failed.
        reason: String,
    },

    /// Configuration error.
    #[error("configuration error: {reason}")]
    ConfigError {
        /// Details about the invalid configuration.
        reason: String,
    },
}
