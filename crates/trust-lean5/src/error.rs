// trust-lean5/error.rs: Certificate pipeline errors
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::Fingerprint;

/// Errors from the certificate pipeline.
#[derive(Debug, thiserror::Error)]
pub enum CertificateError {
    /// The VC could not be serialized to canonical form.
    #[error("canonical serialization failed: {reason}")]
    SerializationFailed { reason: String },

    /// A certificate bundle was empty when one or more certificates were expected.
    #[error("certificate bundle is empty for project {project}")]
    EmptyCertificateBundle { project: String },

    /// Certificate bundle serialization or deserialization failed.
    #[error("certificate bundle serialization failed: {reason}")]
    BundleSerializationFailed { reason: String },

    /// Certificate bundle file I/O failed.
    #[error("certificate bundle I/O failed for {path}: {reason}")]
    BundleIoFailed { path: String, reason: String },

    /// The certificate's VC fingerprint does not match the current VC.
    /// This means the code changed since the certificate was generated.
    #[error("stale certificate: expected fingerprint {expected}, got {actual}")]
    StaleCertificate { expected: Fingerprint, actual: Fingerprint },

    /// The proof term bytes could not be deserialized by lean5.
    #[error("invalid proof term: {reason}")]
    InvalidProofTerm { reason: String },

    /// lean5 kernel rejected the proof term (type-check failure).
    #[error("lean5 kernel rejected proof: {reason}")]
    KernelRejected { reason: String },

    /// lean5 is not available (not compiled in or not reachable).
    #[error("lean5 backend not available: {reason}")]
    BackendUnavailable { reason: String },
}
