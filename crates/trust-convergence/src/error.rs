// trust-convergence: Unified error types for convergence tracking
//
// Provides a top-level error enum that unifies the module-specific errors
// (SnapshotError, PersistenceError, MetricsError, ProofVerificationError)
// under a single type for callers that interact with multiple convergence
// subsystems.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::export::ProofVerificationError;
use crate::metrics::MetricsError;
use crate::persistence::PersistenceError;
use crate::snapshot::SnapshotError;

/// Top-level error type for the trust-convergence crate.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum ConvergenceError {
    /// Invalid configuration (e.g., zero thresholds, contradictory limits).
    #[error("invalid configuration: {0}")]
    InvalidConfig(String),

    /// The convergence tracker has no observations to report on.
    #[error("no observations recorded")]
    NoObservations,

    /// A stagnation threshold was violated.
    #[error("stagnation detected: {consecutive_stale} consecutive stale iterations (threshold: {threshold})")]
    Stagnation {
        consecutive_stale: usize,
        threshold: usize,
    },

    /// Snapshot operation failed.
    #[error(transparent)]
    Snapshot(#[from] SnapshotError),

    /// Persistence operation failed.
    #[error(transparent)]
    Persistence(#[from] PersistenceError),

    /// Metrics operation failed.
    #[error(transparent)]
    Metrics(#[from] MetricsError),

    /// Proof verification failed.
    #[error(transparent)]
    ProofVerification(#[from] ProofVerificationError),
}
