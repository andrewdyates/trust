// trust-proof-cert proof composition types
//
// Core types for proof composition: errors, results, and property tags.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};

use crate::{CertError, CertificationStatus};

/// Errors specific to proof composition.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum CompositionError {
    /// The two certificates have incompatible assumptions
    /// (e.g., contradictory preconditions on shared variables).
    #[error("incompatible assumptions between {cert_a} and {cert_b}: {detail}")]
    IncompatibleAssumptions {
        cert_a: String,
        cert_b: String,
        detail: String,
    },

    /// Composing these certificates would create a circular dependency.
    #[error("circular dependency detected: {cycle}")]
    CircularDependency { cycle: String },

    /// A required intermediate certificate is missing from the composition.
    #[error("missing link: certificate for `{function}` is required but not provided")]
    MissingLink { function: String },

    /// Cannot weaken to a property that is not implied by the original.
    #[error("weakening failed: `{target_property}` is not implied by the certificate")]
    WeakeningFailed { target_property: String },

    /// Cannot strengthen: the certificate does not prove the stronger property.
    #[error("strengthening check failed: `{target_property}` is not proved by {cert_id}")]
    StrengtheningFailed {
        cert_id: String,
        target_property: String,
    },

    /// Generic composition failure.
    #[error("composition failed: {reason}")]
    CompositionFailed { reason: String },

    /// Formula deserialization failed during composition.
    ///
    /// Corrupted or incompatible `formula_json` in a proof certificate must
    /// not be silently ignored — composition cannot verify semantic
    /// consistency without the formula.
    #[error("formula deserialization failed for `{function}`: {reason}")]
    FormulaDeserializationFailed { function: String, reason: String },
}

/// Status of a composition node.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum CompositionNodeStatus {
    /// Certificate present and valid.
    Valid,
    /// Certificate present but chain integrity failed.
    ChainBroken,
    /// Certificate is stale (function hash changed).
    Stale,
    /// Certificate is missing (required but not provided).
    Missing,
}

/// Whether a change was body-only or also changed the spec/signature.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum ChangeKind {
    /// Only the function body changed; spec and signature are the same.
    /// Only the changed function itself needs re-verification.
    BodyOnly,
    /// The function's spec or signature changed.
    /// The changed function AND all transitive callers need re-verification.
    SpecChanged,
}

/// Per-function proof strength record.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FunctionStrength {
    /// Fully-qualified function name.
    pub function: String,
    /// The proof strength achieved for this function.
    pub strength: trust_types::ProofStrength,
    /// Current certification status.
    pub status: CertificationStatus,
}

impl From<CompositionError> for CertError {
    fn from(e: CompositionError) -> Self {
        CertError::VerificationFailed {
            reason: e.to_string(),
        }
    }
}

/// The result of composing multiple proof certificates.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ComposedProof {
    /// IDs of the constituent certificates.
    pub constituent_ids: Vec<String>,
    /// Functions covered by this composed proof.
    pub functions: Vec<String>,
    /// Combined proof strength: the weakest of the constituents.
    pub combined_strength: trust_types::ProofStrength,
    /// Combined certification status: Certified only if ALL constituents are Certified.
    pub combined_status: CertificationStatus,
    /// Total solver time across all constituents (ms).
    pub total_time_ms: u64,
    /// Whether the composed proof is self-consistent (no contradictions detected).
    pub is_consistent: bool,
    /// Edges in the call graph that this composition covers.
    /// Each entry is (caller_function, callee_function).
    pub call_edges: Vec<(String, String)>,
    /// Per-function proof strengths (empty for backward compat).
    pub function_strengths: Vec<FunctionStrength>,
}

/// Result of a composability check between two certificates.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ComposabilityResult {
    /// Whether the certificates can be composed.
    pub composable: bool,
    /// Reasons why composition would fail (empty if composable).
    pub issues: Vec<String>,
    /// Shared function dependencies between the two certificates.
    pub shared_deps: Vec<String>,
}

/// A property tag for weakening/strengthening operations.
/// Represented as a string label for now; in production this would
/// reference the formula AST.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Property(pub String);

impl Property {
    /// Create a property from a string label.
    pub fn new(label: impl Into<String>) -> Self {
        Property(label.into())
    }
}
