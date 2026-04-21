// trust-zani-lib error types
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

//! Error types for the zani library facade.

/// Errors from the zani library integration.
#[derive(Debug, thiserror::Error)]
pub enum ZaniLibError {
    /// The zani binary was not found at the configured path or on PATH.
    #[error("zani binary not found: {reason}")]
    BinaryNotFound {
        /// Details about where we looked.
        reason: String,
    },

    /// Failed to spawn the zani subprocess.
    #[error("failed to spawn zani subprocess: {0}")]
    SpawnFailed(#[from] std::io::Error),

    /// Failed to write to the solver's stdin.
    #[error("failed to write SMT-LIB2 script to zani stdin: {reason}")]
    InputError {
        /// Details about the write failure.
        reason: String,
    },

    /// The solver produced output that could not be parsed.
    #[error("failed to parse zani output: {reason}")]
    ParseError {
        /// Details about what was unexpected.
        reason: String,
    },

    /// The solver timed out.
    #[error("zani timed out after {timeout_ms}ms")]
    Timeout {
        /// The configured timeout that was exceeded.
        timeout_ms: u64,
    },

    /// An encoding error occurred (e.g., unsupported MIR construct).
    #[error("encoding error: {reason}")]
    EncodingError {
        /// Details about what failed to encode.
        reason: String,
    },

    /// Configuration error.
    #[error("configuration error: {reason}")]
    ConfigError {
        /// Details about the invalid configuration.
        reason: String,
    },
}
