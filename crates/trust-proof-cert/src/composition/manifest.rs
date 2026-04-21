// trust-proof-cert composition manifest
//
// Cross-crate proof composition metadata for export and import.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::{FxHashMap, FxHashSet};

use serde::{Deserialize, Serialize};

use super::checkers::strength_rank;
use super::dag::ProofComposition;
use super::types::CompositionNodeStatus;

/// Per-function specification metadata for cross-crate composition.
///
/// Records the proof strength achieved and the pre/postcondition signatures
/// for a verified function, enabling downstream crates to determine whether
/// they can safely compose proofs without re-verifying the dependency.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FunctionSpec {
    /// Pre-condition descriptions (human-readable or formula hashes).
    pub preconditions: Vec<String>,
    /// Post-condition descriptions.
    pub postconditions: Vec<String>,
    /// The proof strength achieved for this function.
    pub proof_strength: trust_types::ProofStrength,
}

/// Entry in a [`CompositionManifest`] for a single function.
///
/// Combines the function's specification metadata with composability
/// flags that describe how this function's proof relates to others.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ManifestEntry {
    /// Function specification (pre/postconditions, proof strength).
    pub spec: FunctionSpec,
    /// SHA-256 hex hash of the function's MIR body, for staleness detection.
    pub signature_hash: String,
    /// Whether this function's proof can be composed with caller proofs.
    pub composable: bool,
    /// Functions this entry depends on (callees).
    pub dependencies: Vec<String>,
}

/// Errors specific to manifest operations.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum ManifestError {
    /// A referenced function is not present in the manifest.
    #[error("function `{function}` not found in manifest")]
    FunctionNotFound { function: String },

    /// Merging manifests found conflicting entries for the same function.
    #[error("conflicting entries for function `{function}`: signature hashes differ")]
    MergeConflict { function: String },

    /// Serialization or deserialization failed.
    #[error("manifest serialization failed: {reason}")]
    SerializationFailed { reason: String },
}

/// A manifest exported by a crate for cross-crate proof composition.
///
/// Maps function identifiers to their proof metadata (strength, pre/post
/// conditions, signature hash, composability flags) so downstream crates
/// can compose proofs without re-verifying dependencies.
///
/// Designed for JSON serialization and transport alongside
/// [`CertificateBundle`](crate::bundle::CertificateBundle).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompositionManifest {
    /// Crate identifier (name).
    pub crate_id: String,
    /// Crate version (semver).
    pub version: String,
    /// Function entries keyed by fully-qualified function name.
    pub entries: FxHashMap<String, ManifestEntry>,
    /// Internal call graph edges: (caller, callee) within this crate.
    pub internal_edges: Vec<(String, String)>,
    /// External dependencies: (local_function, dep_crate, dep_function).
    pub external_deps: Vec<(String, String, String)>,
    /// Spec hashes for invalidation detection (function -> hash).
    pub spec_hashes: FxHashMap<String, u64>,
    /// Bundle hash for integrity verification (from the associated bundle).
    pub bundle_hash: Vec<u8>,
}

impl CompositionManifest {
    /// Create a new empty manifest for a crate.
    #[must_use]
    pub fn new(crate_id: impl Into<String>, version: impl Into<String>) -> Self {
        CompositionManifest {
            crate_id: crate_id.into(),
            version: version.into(),
            entries: FxHashMap::default(),
            internal_edges: Vec::new(),
            external_deps: Vec::new(),
            spec_hashes: FxHashMap::default(),
            bundle_hash: Vec::new(),
        }
    }

    /// Register a proven function in the manifest.
    pub fn add_entry(&mut self, fn_id: impl Into<String>, entry: ManifestEntry) {
        let fn_id = fn_id.into();
        self.entries.insert(fn_id, entry);
    }

    /// Look up a function's manifest entry.
    #[must_use]
    pub fn lookup(&self, fn_id: &str) -> Option<&ManifestEntry> {
        self.entries.get(fn_id)
    }

    /// Quick structural compatibility check between two functions.
    ///
    /// Two functions are composable if:
    /// 1. Both exist in the manifest
    /// 2. Both have their `composable` flag set
    /// 3. Their proof strengths are both at least SMT level
    ///
    /// This is a fast structural check; full semantic composability
    /// requires [`check_composability`](super::checkers::check_composability) on the underlying certificates.
    pub fn is_composable(&self, fn_a: &str, fn_b: &str) -> Result<bool, ManifestError> {
        let entry_a = self.entries.get(fn_a).ok_or_else(|| ManifestError::FunctionNotFound {
            function: fn_a.to_string(),
        })?;
        let entry_b = self.entries.get(fn_b).ok_or_else(|| ManifestError::FunctionNotFound {
            function: fn_b.to_string(),
        })?;

        if !entry_a.composable || !entry_b.composable {
            return Ok(false);
        }

        // Both must have at least SMT-level proof strength.
        let rank_a = strength_rank(&entry_a.spec.proof_strength);
        let rank_b = strength_rank(&entry_b.spec.proof_strength);
        Ok(rank_a >= 1 && rank_b >= 1)
    }

    /// Merge another manifest into this one (for combining dependency manifests).
    ///
    /// If both manifests contain entries for the same function, the entries
    /// must have matching signature hashes; otherwise a [`ManifestError::MergeConflict`]
    /// is returned. When hashes match, the entry from `other` is kept (last-writer-wins
    /// for identical content).
    pub fn merge(&mut self, other: &CompositionManifest) -> Result<(), ManifestError> {
        for (fn_id, entry) in &other.entries {
            if let Some(existing) = self.entries.get(fn_id)
                && existing.signature_hash != entry.signature_hash {
                    return Err(ManifestError::MergeConflict {
                        function: fn_id.clone(),
                    });
                }
            self.entries.insert(fn_id.clone(), entry.clone());
        }

        // Merge edges (deduplicate).
        let existing_edges: FxHashSet<(String, String)> =
            self.internal_edges.iter().cloned().collect();
        for edge in &other.internal_edges {
            if !existing_edges.contains(edge) {
                self.internal_edges.push(edge.clone());
            }
        }

        let existing_ext: FxHashSet<(String, String, String)> =
            self.external_deps.iter().cloned().collect();
        for dep in &other.external_deps {
            if !existing_ext.contains(dep) {
                self.external_deps.push(dep.clone());
            }
        }

        // Merge spec hashes (last-writer-wins for same key).
        for (k, v) in &other.spec_hashes {
            self.spec_hashes.insert(k.clone(), *v);
        }

        Ok(())
    }

    /// Number of function entries in the manifest.
    #[must_use]
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether the manifest has no entries.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// All function names in the manifest, sorted.
    #[must_use]
    pub fn function_names(&self) -> Vec<String> {
        let mut names: Vec<String> = self.entries.keys().cloned().collect();
        names.sort();
        names
    }

    /// Serialize the manifest to JSON.
    pub fn to_json(&self) -> Result<String, ManifestError> {
        serde_json::to_string_pretty(self)
            .map_err(|e| ManifestError::SerializationFailed { reason: e.to_string() })
    }

    /// Deserialize a manifest from JSON.
    pub fn from_json(json: &str) -> Result<Self, ManifestError> {
        serde_json::from_str(json)
            .map_err(|e| ManifestError::SerializationFailed { reason: e.to_string() })
    }
}

/// Generate a [`CompositionManifest`] from a [`ProofComposition`] DAG.
///
/// Extracts function specs, proof strengths, call edges, and composability
/// flags from the composition DAG to produce a manifest suitable for
/// cross-crate distribution.
pub fn generate_manifest(
    composition: &ProofComposition,
    crate_id: &str,
    version: &str,
) -> CompositionManifest {
    let mut manifest = CompositionManifest::new(crate_id, version);

    for func_name in composition.functions() {
        let node = match composition.get_node(&func_name) {
            Some(n) => n,
            None => continue,
        };

        let cert = composition.get_certificate(&func_name);

        let spec = FunctionSpec {
            preconditions: Vec::new(), // Populated from contract metadata when available
            postconditions: Vec::new(),
            proof_strength: cert
                .map(|c| c.solver.strength.clone())
                .unwrap_or_else(trust_types::ProofStrength::smt_unsat),
        };

        let signature_hash = cert
            .map(|c| c.function_hash.0.clone())
            .unwrap_or_default();

        let composable = node.status == CompositionNodeStatus::Valid;

        let entry = ManifestEntry {
            spec,
            signature_hash,
            composable,
            dependencies: node.dependencies.clone(),
        };

        manifest.add_entry(func_name.clone(), entry);

        // Record internal edges from this function to its callees.
        for dep in &node.dependencies {
            manifest
                .internal_edges
                .push((func_name.clone(), dep.clone()));
        }
    }

    manifest
}
