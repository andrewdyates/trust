// trust-crown/error.rs: Error types for gamma-crown integration
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use thiserror::Error;

/// Errors from the gamma-crown verification backend.
#[derive(Debug, Error)]
#[non_exhaustive]
pub(crate) enum CrownError {
    /// The gamma-crown binary was not found on the system.
    #[error("gamma-crown binary not found: {message}")]
    BinaryNotFound { message: String },

    /// Failed to serialize the verification query to JSON.
    #[error("query serialization failed: {source}")]
    Serialization {
        #[from]
        source: serde_json::Error,
    },

    /// The gamma-crown process exited with a non-zero status.
    #[error("gamma-crown process failed: exit code {code}, stderr: {stderr}")]
    ProcessFailed { code: i32, stderr: String },

    /// I/O error communicating with the gamma-crown subprocess.
    #[error("I/O error: {source}")]
    Io {
        #[from]
        source: std::io::Error,
    },

    /// The gamma-crown output could not be parsed.
    #[error("failed to parse gamma-crown output: {message}")]
    OutputParse { message: String },

    /// The verification query references an unsupported property type.
    #[error("unsupported neural network property: {property}")]
    UnsupportedProperty { property: String },

    /// The network model file was not found or unreadable.
    #[error("model file not found: {path}")]
    ModelNotFound { path: String },
}
