// trust-type-recover: error types
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

/// Errors that can occur during type recovery.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum TypeRecoveryError {
    /// No strategies produced any evidence for the given address.
    #[error("no type evidence found for address {0:#x}")]
    NoEvidence(u64),

    /// Conflicting evidence from multiple strategies that could not be resolved.
    #[error("conflicting type evidence at address {0:#x}: {1}")]
    ConflictingEvidence(u64, String),

    /// DWARF debug info is malformed or unsupported.
    #[error("DWARF parse error: {0}")]
    DwarfParse(String),

    /// An access pattern could not be interpreted as a valid type layout.
    #[error("invalid access pattern at offset {offset}: {reason}")]
    InvalidAccessPattern {
        /// Byte offset where the pattern was detected.
        offset: u64,
        /// Why the pattern is invalid.
        reason: String,
    },

    /// Value range is empty or inconsistent.
    #[error("inconsistent value range: {0}")]
    InconsistentValueRange(String),
}
