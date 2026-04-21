// trust-proof-cert content-addressed certificate store
//
// Content-addressed storage: certificates keyed by SHA-256 of their canonical
// content (CertificateDigest). Provides natural deduplication, cross-crate
// addressability, and Merkle-tree roots for batch integrity verification.
//
// Part of #430: Proof certificate storage, distribution, and chain verification.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::integrity::{build_merkle_tree, compute_digest, CertificateDigest, MerkleTree};
use crate::{CertError, CertificateChain, FunctionHash, ProofCertificate};

/// Content-addressed identifier: SHA-256 of the certificate's canonical bytes.
///
/// Unlike `CertificateId` (which hashes function name + timestamp), this ID
/// is derived from the full certificate content, providing natural deduplication:
/// identical proofs of the same VC produce the same `ContentId`.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub(crate) struct ContentId(pub [u8; 32]);

impl ContentId {
    /// Compute from a proof certificate's canonical content.
    pub fn from_cert(cert: &ProofCertificate) -> Self {
        ContentId(compute_digest(cert).0)
    }

    /// Display as hex string.
    pub fn to_hex(&self) -> String {
        self.0.iter().map(|b| format!("{b:02x}")).collect()
    }

    /// Parse from a 64-char hex string.
    pub fn from_hex(hex: &str) -> Result<Self, CertError> {
        let digest = CertificateDigest::from_hex(hex)?;
        Ok(ContentId(digest.0))
    }
}

/// Hash of a verification condition, used for deduplication.
///
/// Two VCs with the same hash are semantically equivalent, so their proofs
/// are interchangeable regardless of which function they came from.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub(crate) struct VcHash(pub [u8; 32]);

impl VcHash {
    /// Compute from a VC snapshot.
    pub fn from_snapshot(snapshot: &crate::VcSnapshot) -> Self {
        VcHash(snapshot.vc_hash())
    }

    /// Display as hex string.
    pub fn to_hex(&self) -> String {
        self.0.iter().map(|b| format!("{b:02x}")).collect()
    }
}

/// A content-addressed certificate store.
///
/// Certificates are stored by their content hash (`ContentId`), providing:
/// - Natural deduplication: identical proofs share one entry
/// - Cross-crate addressability: same hash = same proof regardless of origin
/// - Merkle-tree root for batch integrity verification
///
/// The store also maintains indices for lookup by VC hash and function name.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct ContentStore {
    /// Primary storage: content_id -> certificate.
    certs: FxHashMap<String, ProofCertificate>,
    /// Content_id -> chain.
    chains: FxHashMap<String, CertificateChain>,
    /// vc_hash -> content_ids (deduplicates identical VCs).
    by_vc: FxHashMap<String, Vec<String>>,
    /// function_fqn -> vc_hashes (lookup by function name).
    index: FxHashMap<String, Vec<String>>,
    /// Crate this store belongs to.
    pub crate_name: String,
    /// Store format version.
    pub version: u32,
}

/// Current content store format version.
pub(crate) const CONTENT_STORE_VERSION: u32 = 1;

impl ContentStore {
    /// Create a new empty content-addressed store.
    pub fn new(crate_name: impl Into<String>) -> Self {
        ContentStore {
            certs: FxHashMap::default(),
            chains: FxHashMap::default(),
            by_vc: FxHashMap::default(),
            index: FxHashMap::default(),
            crate_name: crate_name.into(),
            version: CONTENT_STORE_VERSION,
        }
    }

    /// Insert a certificate with its chain.
    ///
    /// Returns the `ContentId` assigned. If a certificate with identical
    /// content already exists, the existing entry is kept and its ID returned.
    pub fn insert(
        &mut self,
        cert: ProofCertificate,
        chain: CertificateChain,
    ) -> ContentId {
        let content_id = ContentId::from_cert(&cert);
        let id_hex = content_id.to_hex();

        // Update VC hash index.
        let vc_hash = VcHash::from_snapshot(&cert.vc_snapshot);
        let vc_hex = vc_hash.to_hex();
        self.by_vc
            .entry(vc_hex.clone())
            .or_default()
            .retain(|existing| existing != &id_hex);
        self.by_vc
            .entry(vc_hex)
            .or_default()
            .push(id_hex.clone());

        // Update function name index.
        self.index
            .entry(cert.function.clone())
            .or_default()
            .retain(|existing| existing != &id_hex);
        self.index
            .entry(cert.function.clone())
            .or_default()
            .push(id_hex.clone());

        // Store certificate and chain.
        self.certs.insert(id_hex.clone(), cert);
        self.chains.insert(id_hex, chain);

        content_id
    }

    /// Get a certificate by its content ID.
    pub fn get(&self, id: &ContentId) -> Option<&ProofCertificate> {
        self.certs.get(&id.to_hex())
    }

    /// Get the chain for a certificate.
    pub fn get_chain(&self, id: &ContentId) -> Option<&CertificateChain> {
        self.chains.get(&id.to_hex())
    }

    /// Find all certificates that prove the same VC (by VC hash).
    pub fn find_by_vc_hash(&self, vc_hash: &VcHash) -> Vec<&ProofCertificate> {
        let vc_hex = vc_hash.to_hex();
        self.by_vc
            .get(&vc_hex)
            .map(|ids| {
                ids.iter()
                    .filter_map(|id| self.certs.get(id))
                    .collect()
            })
            .unwrap_or_default()
    }

    /// Find all certificates for a function.
    pub fn find_by_function(&self, function: &str) -> Vec<&ProofCertificate> {
        self.index
            .get(function)
            .map(|ids| {
                ids.iter()
                    .filter_map(|id| self.certs.get(id))
                    .collect()
            })
            .unwrap_or_default()
    }

    /// Remove a certificate by content ID.
    pub fn remove(&mut self, id: &ContentId) -> Option<ProofCertificate> {
        let id_hex = id.to_hex();
        if let Some(cert) = self.certs.remove(&id_hex) {
            self.chains.remove(&id_hex);

            // Clean up VC hash index.
            let vc_hash = VcHash::from_snapshot(&cert.vc_snapshot);
            if let Some(ids) = self.by_vc.get_mut(&vc_hash.to_hex()) {
                ids.retain(|x| x != &id_hex);
            }

            // Clean up function index.
            if let Some(ids) = self.index.get_mut(&cert.function) {
                ids.retain(|x| x != &id_hex);
            }

            Some(cert)
        } else {
            None
        }
    }

    /// Remove all certificates for functions whose body hashes have changed.
    ///
    /// Returns the content IDs of removed certificates.
    pub fn invalidate_stale(
        &mut self,
        current_hashes: &FxHashMap<String, FunctionHash>,
    ) -> Vec<ContentId> {
        let stale: Vec<(String, [u8; 32])> = self
            .certs
            .iter()
            .filter(|(_id, cert)| {
                current_hashes
                    .get(&cert.function)
                    .map(|h| !cert.is_fresh_for(h))
                    .unwrap_or(true)
            })
            .map(|(id, _)| {
                let mut bytes = [0u8; 32];
                if let Ok(cid) = ContentId::from_hex(id) {
                    bytes = cid.0;
                }
                (id.clone(), bytes)
            })
            .collect();

        let mut removed = Vec::new();
        for (id_hex, bytes) in &stale {
            let content_id = ContentId(*bytes);
            self.remove(&content_id);
            let _ = id_hex; // suppress unused warning
            removed.push(content_id);
        }
        removed
    }

    /// Number of certificates in the store.
    pub fn len(&self) -> usize {
        self.certs.len()
    }

    /// Is the store empty?
    pub fn is_empty(&self) -> bool {
        self.certs.is_empty()
    }

    /// All unique function names with certificates.
    pub fn function_names(&self) -> Vec<String> {
        let mut names: Vec<String> = self
            .index
            .iter()
            .filter(|(_, ids)| !ids.is_empty())
            .map(|(name, _)| name.clone())
            .collect();
        names.sort();
        names
    }

    /// Build a Merkle tree over all certificates for batch integrity verification.
    ///
    /// The Merkle root can be published alongside the crate binary as a
    /// compact integrity summary.
    pub fn merkle_tree(&self) -> MerkleTree {
        // tRust #803 P0-3: Sort certs by content ID (HashMap key) before building
        // the Merkle tree. HashMap iteration order is non-deterministic, which
        // caused the Merkle root to differ across runs. Sorting by key matches
        // the approach used in CertificateBundle::from_content_store.
        let mut sorted_entries: Vec<(&String, &ProofCertificate)> =
            self.certs.iter().collect();
        sorted_entries.sort_by(|(id_a, _), (id_b, _)| id_a.cmp(id_b));
        let certs: Vec<ProofCertificate> =
            sorted_entries.iter().map(|(_, cert)| (*cert).clone()).collect();
        build_merkle_tree(&certs)
    }

    /// Compute the Merkle root hash over all certificates.
    pub fn merkle_root(&self) -> [u8; 32] {
        self.merkle_tree().root()
    }

    /// All content IDs in the store.
    pub fn content_ids(&self) -> Vec<ContentId> {
        self.certs
            .keys()
            .filter_map(|hex| ContentId::from_hex(hex).ok())
            .collect()
    }

    /// Serialize to JSON.
    pub fn to_json(&self) -> Result<String, CertError> {
        serde_json::to_string_pretty(self)
            .map_err(|e| CertError::SerializationFailed { reason: e.to_string() })
    }

    /// Deserialize from JSON.
    pub fn from_json(json: &str) -> Result<Self, CertError> {
        serde_json::from_str(json)
            .map_err(|e| CertError::SerializationFailed { reason: e.to_string() })
    }
}

/// Compute a SHA-256 hash over arbitrary bytes, returning the raw 32 bytes.
pub(crate) fn sha256(data: &[u8]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(data);
    hasher.finalize().into()
}

#[cfg(test)]
mod tests {
    use trust_types::ProofStrength;

    use super::*;
    use crate::{CertificateChain, ChainStep, ChainStepType, SolverInfo, VcSnapshot};

    fn make_cert(function: &str, timestamp: &str) -> ProofCertificate {
        let vc_snapshot = VcSnapshot {
            kind: "Assertion".to_string(),
            formula_json: "true".to_string(),
            location: None,
        };
        let solver = SolverInfo {
            name: "z4".to_string(),
            version: "1.0.0".to_string(),
            time_ms: 10,
            strength: ProofStrength::smt_unsat(),
            evidence: None,
        };
        ProofCertificate::new_trusted(
            function.to_string(),
            FunctionHash::from_bytes(format!("{function}-body").as_bytes()),
            vc_snapshot,
            solver,
            vec![1, 2, 3],
            timestamp.to_string(),
        )
    }

    fn make_chain() -> CertificateChain {
        let mut chain = CertificateChain::new();
        chain.push(ChainStep {
            step_type: ChainStepType::VcGeneration,
            tool: "trust-vcgen".to_string(),
            tool_version: "0.1.0".to_string(),
            input_hash: "mir-hash".to_string(),
            output_hash: "vc-hash".to_string(),
            time_ms: 5,
            timestamp: "2026-03-27T00:00:00Z".to_string(),
        });
        chain.push(ChainStep {
            step_type: ChainStepType::SolverProof,
            tool: "z4".to_string(),
            tool_version: "1.0.0".to_string(),
            input_hash: "vc-hash".to_string(),
            output_hash: "proof-hash".to_string(),
            time_ms: 42,
            timestamp: "2026-03-27T00:00:01Z".to_string(),
        });
        chain
    }

    #[test]
    fn test_content_id_deterministic() {
        let cert = make_cert("crate::foo", "2026-04-01T00:00:00Z");
        let id1 = ContentId::from_cert(&cert);
        let id2 = ContentId::from_cert(&cert);
        assert_eq!(id1, id2);
    }

    #[test]
    fn test_content_id_hex_roundtrip() {
        let cert = make_cert("crate::foo", "2026-04-01T00:00:00Z");
        let id = ContentId::from_cert(&cert);
        let hex = id.to_hex();
        let restored = ContentId::from_hex(&hex).expect("valid hex");
        assert_eq!(restored, id);
    }

    #[test]
    fn test_insert_and_get() {
        let mut store = ContentStore::new("test-crate");
        let cert = make_cert("crate::foo", "2026-04-01T00:00:00Z");
        let chain = make_chain();
        let id = store.insert(cert.clone(), chain.clone());

        assert_eq!(store.len(), 1);
        assert_eq!(store.get(&id), Some(&cert));
        assert_eq!(store.get_chain(&id), Some(&chain));
    }

    #[test]
    fn test_deduplication_same_content() {
        let mut store = ContentStore::new("test-crate");
        let cert = make_cert("crate::foo", "2026-04-01T00:00:00Z");
        let chain = make_chain();

        let id1 = store.insert(cert.clone(), chain.clone());
        let id2 = store.insert(cert.clone(), chain.clone());

        assert_eq!(id1, id2);
        assert_eq!(store.len(), 1, "duplicate insert should not add a second entry");
    }

    #[test]
    fn test_different_content_different_ids() {
        let mut store = ContentStore::new("test-crate");
        let cert1 = make_cert("crate::foo", "2026-04-01T00:00:00Z");
        let cert2 = make_cert("crate::bar", "2026-04-01T00:00:00Z");
        let chain = make_chain();

        let id1 = store.insert(cert1, chain.clone());
        let id2 = store.insert(cert2, chain);

        assert_ne!(id1, id2);
        assert_eq!(store.len(), 2);
    }

    #[test]
    fn test_find_by_vc_hash() {
        let mut store = ContentStore::new("test-crate");
        // Two certs with same VC content but different timestamps
        let cert1 = make_cert("crate::foo", "2026-04-01T00:00:00Z");
        let cert2 = make_cert("crate::foo", "2026-04-01T00:00:01Z");
        let vc_hash = VcHash::from_snapshot(&cert1.vc_snapshot);

        store.insert(cert1, make_chain());
        store.insert(cert2, make_chain());

        let found = store.find_by_vc_hash(&vc_hash);
        assert_eq!(found.len(), 2);
    }

    #[test]
    fn test_find_by_function() {
        let mut store = ContentStore::new("test-crate");
        store.insert(make_cert("crate::foo", "2026-04-01T00:00:00Z"), make_chain());
        store.insert(make_cert("crate::bar", "2026-04-01T00:00:01Z"), make_chain());

        let foo_certs = store.find_by_function("crate::foo");
        assert_eq!(foo_certs.len(), 1);
        assert_eq!(foo_certs[0].function, "crate::foo");
    }

    #[test]
    fn test_remove() {
        let mut store = ContentStore::new("test-crate");
        let cert = make_cert("crate::foo", "2026-04-01T00:00:00Z");
        let id = store.insert(cert, make_chain());

        assert_eq!(store.len(), 1);
        let removed = store.remove(&id);
        assert!(removed.is_some());
        assert_eq!(store.len(), 0);
        assert!(store.get(&id).is_none());
    }

    #[test]
    fn test_invalidate_stale() {
        let mut store = ContentStore::new("test-crate");
        let cert1 = make_cert("crate::foo", "2026-04-01T00:00:00Z");
        let cert2 = make_cert("crate::bar", "2026-04-01T00:00:01Z");
        store.insert(cert1, make_chain());
        store.insert(cert2.clone(), make_chain());

        let mut current_hashes = FxHashMap::default();
        // foo changed body, bar stayed the same
        current_hashes.insert("crate::foo".to_string(), FunctionHash::from_bytes(b"new-body"));
        current_hashes.insert("crate::bar".to_string(), cert2.function_hash.clone());

        let removed = store.invalidate_stale(&current_hashes);
        assert_eq!(removed.len(), 1);
        assert_eq!(store.len(), 1);
        assert_eq!(store.find_by_function("crate::bar").len(), 1);
        assert!(store.find_by_function("crate::foo").is_empty());
    }

    #[test]
    fn test_function_names() {
        let mut store = ContentStore::new("test-crate");
        store.insert(make_cert("crate::bar", "2026-04-01T00:00:00Z"), make_chain());
        store.insert(make_cert("crate::foo", "2026-04-01T00:00:01Z"), make_chain());

        let names = store.function_names();
        assert_eq!(names, vec!["crate::bar", "crate::foo"]);
    }

    #[test]
    fn test_merkle_root_nonempty() {
        let mut store = ContentStore::new("test-crate");
        store.insert(make_cert("crate::foo", "2026-04-01T00:00:00Z"), make_chain());
        store.insert(make_cert("crate::bar", "2026-04-01T00:00:01Z"), make_chain());

        let root = store.merkle_root();
        assert_ne!(root, [0u8; 32], "non-empty store should have non-zero Merkle root");
    }

    #[test]
    fn test_merkle_root_empty() {
        let store = ContentStore::new("test-crate");
        let root = store.merkle_root();
        assert_eq!(root, [0u8; 32]);
    }

    #[test]
    fn test_json_roundtrip() {
        let mut store = ContentStore::new("test-crate");
        store.insert(make_cert("crate::foo", "2026-04-01T00:00:00Z"), make_chain());

        let json = store.to_json().expect("should serialize");
        let restored = ContentStore::from_json(&json).expect("should deserialize");
        assert_eq!(restored.len(), store.len());
        assert_eq!(restored.crate_name, store.crate_name);
    }

    #[test]
    fn test_content_ids() {
        let mut store = ContentStore::new("test-crate");
        let cert = make_cert("crate::foo", "2026-04-01T00:00:00Z");
        let expected_id = store.insert(cert, make_chain());

        let ids = store.content_ids();
        assert_eq!(ids.len(), 1);
        assert_eq!(ids[0], expected_id);
    }

    #[test]
    fn test_vc_hash_hex() {
        let snapshot = VcSnapshot {
            kind: "Assertion".to_string(),
            formula_json: "true".to_string(),
            location: None,
        };
        let hash = VcHash::from_snapshot(&snapshot);
        let hex = hash.to_hex();
        assert_eq!(hex.len(), 64);
        assert!(hex.chars().all(|c| c.is_ascii_hexdigit()));
    }
}
