// trust-proof-cert cross-crate certificate bundle
//
// Bundles package proof certificates for distribution alongside compiled crate
// artifacts (.rlib). A bundle contains all certificates, their chains, a manifest
// with Merkle root, and metadata for cross-crate verification.
//
// Part of #430: Proof certificate storage, distribution, and chain verification.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;
use std::path::Path;

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::content_store::{ContentId, ContentStore};
use crate::integrity::build_merkle_tree;
use crate::{CertError, CertificateChain, ProofCertificate};

/// File extension for standalone trust certificate bundles.
pub(crate) const BUNDLE_EXTENSION: &str = "trust-cert";

/// Magic bytes identifying a trust certificate bundle.
pub(crate) const BUNDLE_MAGIC: &[u8; 4] = b"tRCB";

/// Current bundle format version.
pub(crate) const BUNDLE_FORMAT_VERSION: u32 = 1;

/// A manifest describing the contents of a certificate bundle.
///
/// The manifest serves as a compact integrity summary: the Merkle root
/// can be verified without loading all certificates.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct BundleManifest {
    /// Bundle format version.
    pub version: u32,
    /// Crate name this bundle belongs to.
    pub crate_name: String,
    /// Crate version (semver).
    pub crate_version: String,
    /// Number of certificates in the bundle.
    pub cert_count: usize,
    /// Merkle root over all certificate digests.
    pub merkle_root: [u8; 32],
    /// SHA-256 of the concatenated content IDs (for quick bundle identity).
    pub bundle_hash: [u8; 32],
    /// Function names with certificates, sorted.
    pub functions: Vec<String>,
    /// Timestamp when the bundle was created.
    pub created_at: String,
}

/// A complete certificate bundle for cross-crate distribution.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct CertificateBundle {
    /// The manifest (compact summary).
    pub manifest: BundleManifest,
    /// All certificates, keyed by content ID hex.
    pub certificates: FxHashMap<String, ProofCertificate>,
    /// All chains, keyed by content ID hex.
    pub chains: FxHashMap<String, CertificateChain>,
}

impl CertificateBundle {
    /// Create a bundle from a content-addressed store.
    pub fn from_content_store(
        store: &ContentStore,
        crate_version: &str,
        timestamp: &str,
    ) -> Self {
        let content_ids = store.content_ids();
        let mut certificates = FxHashMap::default();
        let mut chains = FxHashMap::default();

        for id in &content_ids {
            let hex = id.to_hex();
            if let Some(cert) = store.get(id) {
                certificates.insert(hex.clone(), cert.clone());
            }
            if let Some(chain) = store.get_chain(id) {
                chains.insert(hex, chain.clone());
            }
        }

        // Sort certificates by content ID hex for deterministic Merkle root.
        // HashMap iteration order is non-deterministic (randomized per-process),
        // so we must canonicalize before building the Merkle tree. // tRust: #763
        let mut certs_sorted: Vec<(&String, &ProofCertificate)> =
            certificates.iter().collect();
        certs_sorted.sort_by(|(id_a, _), (id_b, _)| id_a.cmp(id_b));
        let certs_vec: Vec<ProofCertificate> =
            certs_sorted.iter().map(|(_, cert)| (*cert).clone()).collect();
        let merkle_tree = build_merkle_tree(&certs_vec);
        let merkle_root = merkle_tree.root();

        // Compute bundle hash from sorted content IDs.
        let mut id_hexes: Vec<String> = content_ids.iter().map(|id| id.to_hex()).collect();
        id_hexes.sort();
        let mut hasher = Sha256::new();
        for hex in &id_hexes {
            hasher.update(hex.as_bytes());
        }
        let bundle_hash: [u8; 32] = hasher.finalize().into();

        let functions = store.function_names();

        let manifest = BundleManifest {
            version: BUNDLE_FORMAT_VERSION,
            crate_name: store.crate_name.clone(),
            crate_version: crate_version.to_string(),
            cert_count: certificates.len(),
            merkle_root,
            bundle_hash,
            functions,
            created_at: timestamp.to_string(),
        };

        CertificateBundle {
            manifest,
            certificates,
            chains,
        }
    }

    /// Verify bundle integrity: recompute Merkle root and compare.
    pub fn verify_integrity(&self) -> Result<BundleVerification, CertError> {
        // Sort certificates by content ID hex for deterministic Merkle root.
        // Must match the canonical order used in from_content_store(). // tRust: #763
        let mut certs_sorted: Vec<(&String, &ProofCertificate)> =
            self.certificates.iter().collect();
        certs_sorted.sort_by(|(id_a, _), (id_b, _)| id_a.cmp(id_b));
        let certs_vec: Vec<ProofCertificate> =
            certs_sorted.iter().map(|(_, cert)| (*cert).clone()).collect();
        let merkle_tree = build_merkle_tree(&certs_vec);
        let computed_root = merkle_tree.root();

        let merkle_valid = computed_root == self.manifest.merkle_root;
        let count_valid = self.certificates.len() == self.manifest.cert_count;

        // Verify each certificate's content ID matches its key.
        let mut id_mismatches = Vec::new();
        for (hex, cert) in &self.certificates {
            let expected = ContentId::from_cert(cert);
            if expected.to_hex() != *hex {
                id_mismatches.push(hex.clone());
            }
        }

        let valid = merkle_valid && count_valid && id_mismatches.is_empty();

        Ok(BundleVerification {
            valid,
            merkle_valid,
            count_valid,
            id_mismatches,
            cert_count: self.certificates.len(),
        })
    }

    /// Serialize to binary format.
    ///
    /// Format: BUNDLE_MAGIC (4B) | version (4B LE) | JSON payload length (8B LE) | JSON payload
    pub fn to_bytes(&self) -> Result<Vec<u8>, CertError> {
        let json = serde_json::to_string(self)
            .map_err(|e| CertError::SerializationFailed { reason: e.to_string() })?;
        let payload = json.as_bytes();

        let mut bytes = Vec::with_capacity(4 + 4 + 8 + payload.len());
        bytes.extend_from_slice(BUNDLE_MAGIC);
        bytes.extend_from_slice(&BUNDLE_FORMAT_VERSION.to_le_bytes());
        bytes.extend_from_slice(&(payload.len() as u64).to_le_bytes());
        bytes.extend_from_slice(payload);
        Ok(bytes)
    }

    /// Deserialize from binary format.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, CertError> {
        let header_len = 4 + 4 + 8; // magic + version + length
        if bytes.len() < header_len {
            return Err(CertError::SerializationFailed {
                reason: format!(
                    "bundle too short: expected at least {header_len} bytes, got {}",
                    bytes.len()
                ),
            });
        }

        if &bytes[..4] != BUNDLE_MAGIC {
            return Err(CertError::SerializationFailed {
                reason: "invalid bundle magic bytes".to_string(),
            });
        }

        let version = u32::from_le_bytes([bytes[4], bytes[5], bytes[6], bytes[7]]);
        if version != BUNDLE_FORMAT_VERSION {
            return Err(CertError::SerializationFailed {
                reason: format!(
                    "unsupported bundle version: expected {BUNDLE_FORMAT_VERSION}, got {version}"
                ),
            });
        }

        let payload_len = u64::from_le_bytes([
            bytes[8], bytes[9], bytes[10], bytes[11],
            bytes[12], bytes[13], bytes[14], bytes[15],
        ]) as usize;

        if bytes.len() < header_len + payload_len {
            return Err(CertError::SerializationFailed {
                reason: format!(
                    "bundle truncated: expected {} bytes payload, got {}",
                    payload_len,
                    bytes.len() - header_len
                ),
            });
        }

        let payload = &bytes[header_len..header_len + payload_len];
        let json = std::str::from_utf8(payload)
            .map_err(|e| CertError::SerializationFailed { reason: e.to_string() })?;

        serde_json::from_str(json)
            .map_err(|e| CertError::SerializationFailed { reason: e.to_string() })
    }

    /// Save to a `.trust-cert` file.
    pub fn save_to_file(&self, path: impl AsRef<Path>) -> Result<(), CertError> {
        let bytes = self.to_bytes()?;
        if let Some(parent) = path.as_ref().parent() {
            std::fs::create_dir_all(parent)?;
        }
        std::fs::write(path.as_ref(), bytes)?;
        Ok(())
    }

    /// Load from a `.trust-cert` file.
    pub fn load_from_file(path: impl AsRef<Path>) -> Result<Self, CertError> {
        let bytes = std::fs::read(path.as_ref())?;
        Self::from_bytes(&bytes)
    }

    /// Import all certificates from this bundle into a content store.
    ///
    /// Returns the number of certificates imported (skipping duplicates).
    pub fn import_into(&self, store: &mut ContentStore) -> usize {
        let mut imported = 0;
        for (hex, cert) in &self.certificates {
            let chain = self.chains.get(hex).cloned().unwrap_or_default();
            let id = ContentId::from_cert(cert);
            if store.get(&id).is_none() {
                store.insert(cert.clone(), chain);
                imported += 1;
            }
        }
        imported
    }

    /// Get a certificate by content ID hex.
    pub fn get_cert(&self, content_id_hex: &str) -> Option<&ProofCertificate> {
        self.certificates.get(content_id_hex)
    }

    /// Number of certificates in the bundle.
    pub fn len(&self) -> usize {
        self.certificates.len()
    }

    /// Is the bundle empty?
    pub fn is_empty(&self) -> bool {
        self.certificates.is_empty()
    }
}

/// Result of verifying a bundle's integrity.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct BundleVerification {
    /// Overall pass/fail.
    pub valid: bool,
    /// Whether the Merkle root matches.
    pub merkle_valid: bool,
    /// Whether the certificate count matches the manifest.
    pub count_valid: bool,
    /// Content IDs that don't match their certificate content.
    pub id_mismatches: Vec<String>,
    /// Number of certificates verified.
    pub cert_count: usize,
}

#[cfg(test)]
mod tests {
    use trust_types::ProofStrength;

    use super::*;
    use crate::{
        ChainStep, ChainStepType, FunctionHash, SolverInfo, VcSnapshot,
    };

    fn make_cert(function: &str) -> ProofCertificate {
        let vc_snapshot = VcSnapshot {
            kind: "Assertion".to_string(),
            formula_json: format!("{function}-vc"),
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
            "2026-04-12T00:00:00Z".to_string(),
        )
    }

    fn make_chain() -> CertificateChain {
        let mut chain = CertificateChain::new();
        chain.push(ChainStep {
            step_type: ChainStepType::VcGeneration,
            tool: "trust-vcgen".to_string(),
            tool_version: "0.1.0".to_string(),
            input_hash: "mir".to_string(),
            output_hash: "vc".to_string(),
            time_ms: 1,
            timestamp: "2026-04-12T00:00:00Z".to_string(),
        });
        chain
    }

    fn make_store() -> ContentStore {
        let mut store = ContentStore::new("test-crate");
        store.insert(make_cert("crate::foo"), make_chain());
        store.insert(make_cert("crate::bar"), make_chain());
        store.insert(make_cert("crate::baz"), make_chain());
        store
    }

    #[test]
    fn test_bundle_from_store() {
        let store = make_store();
        let bundle = CertificateBundle::from_content_store(
            &store,
            "0.1.0",
            "2026-04-12T00:00:00Z",
        );

        assert_eq!(bundle.manifest.crate_name, "test-crate");
        assert_eq!(bundle.manifest.crate_version, "0.1.0");
        assert_eq!(bundle.manifest.cert_count, 3);
        assert_eq!(bundle.certificates.len(), 3);
        assert_ne!(bundle.manifest.merkle_root, [0u8; 32]);
    }

    #[test]
    fn test_bundle_verify_integrity() {
        let store = make_store();
        let bundle = CertificateBundle::from_content_store(
            &store,
            "0.1.0",
            "2026-04-12T00:00:00Z",
        );

        let result = bundle.verify_integrity().expect("should verify");
        assert!(result.valid);
        assert!(result.merkle_valid);
        assert!(result.count_valid);
        assert!(result.id_mismatches.is_empty());
    }

    #[test]
    fn test_bundle_binary_roundtrip() {
        let store = make_store();
        let bundle = CertificateBundle::from_content_store(
            &store,
            "0.1.0",
            "2026-04-12T00:00:00Z",
        );

        let bytes = bundle.to_bytes().expect("should serialize");
        assert_eq!(&bytes[..4], BUNDLE_MAGIC);

        let restored = CertificateBundle::from_bytes(&bytes).expect("should deserialize");
        assert_eq!(restored.manifest.crate_name, bundle.manifest.crate_name);
        assert_eq!(restored.certificates.len(), bundle.certificates.len());
    }

    #[test]
    fn test_bundle_file_roundtrip() {
        let dir = std::env::temp_dir().join(format!("trust-bundle-test-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).expect("create dir");

        let store = make_store();
        let bundle = CertificateBundle::from_content_store(
            &store,
            "0.1.0",
            "2026-04-12T00:00:00Z",
        );

        let path = dir.join("test.trust-cert");
        bundle.save_to_file(&path).expect("should save");
        assert!(path.exists());

        let loaded = CertificateBundle::load_from_file(&path).expect("should load");
        assert_eq!(loaded.certificates.len(), 3);

        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_bundle_import_into_store() {
        let store = make_store();
        let bundle = CertificateBundle::from_content_store(
            &store,
            "0.1.0",
            "2026-04-12T00:00:00Z",
        );

        let mut new_store = ContentStore::new("consumer-crate");
        let imported = bundle.import_into(&mut new_store);
        assert_eq!(imported, 3);
        assert_eq!(new_store.len(), 3);

        // Importing again should skip duplicates.
        let imported2 = bundle.import_into(&mut new_store);
        assert_eq!(imported2, 0);
        assert_eq!(new_store.len(), 3);
    }

    #[test]
    fn test_bundle_bad_magic() {
        let err = CertificateBundle::from_bytes(b"XXXX\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00")
            .expect_err("bad magic should fail");
        match err {
            CertError::SerializationFailed { reason } => {
                assert!(reason.contains("magic"));
            }
            other => panic!("unexpected error: {other:?}"),
        }
    }

    #[test]
    fn test_bundle_too_short() {
        let err = CertificateBundle::from_bytes(b"tRCB")
            .expect_err("too short should fail");
        match err {
            CertError::SerializationFailed { reason } => {
                assert!(reason.contains("too short"));
            }
            other => panic!("unexpected error: {other:?}"),
        }
    }

    #[test]
    fn test_bundle_empty_store() {
        let store = ContentStore::new("empty-crate");
        let bundle = CertificateBundle::from_content_store(
            &store,
            "0.1.0",
            "2026-04-12T00:00:00Z",
        );

        assert_eq!(bundle.len(), 0);
        assert!(bundle.is_empty());
        assert_eq!(bundle.manifest.cert_count, 0);
    }

    #[test]
    fn test_bundle_manifest_functions_sorted() {
        let store = make_store();
        let bundle = CertificateBundle::from_content_store(
            &store,
            "0.1.0",
            "2026-04-12T00:00:00Z",
        );

        let funcs = &bundle.manifest.functions;
        let mut sorted = funcs.clone();
        sorted.sort();
        assert_eq!(*funcs, sorted);
    }

    /// Same bundle must produce the same Merkle root across multiple calls.
    /// Regression test for #763: HashMap iteration order caused non-deterministic roots.
    #[test]
    fn test_merkle_root_deterministic_across_calls() {
        let store = make_store();
        let bundle = CertificateBundle::from_content_store(
            &store,
            "0.1.0",
            "2026-04-12T00:00:00Z",
        );

        // Verify integrity multiple times — each call rebuilds the Merkle tree
        // from the HashMap. Before #763 fix, iteration order was random.
        let mut roots = Vec::new();
        for _ in 0..10 {
            let result = bundle.verify_integrity().expect("should verify");
            assert!(result.valid, "bundle should be valid");
            assert!(result.merkle_valid, "merkle root should match");
            roots.push(result);
        }
    }

    /// Bundles with the same certificates inserted in different order must
    /// produce the same Merkle root, since we sort by content ID before
    /// building the tree.
    /// Regression test for #763.
    #[test]
    fn test_merkle_root_independent_of_insertion_order() {
        // Build two stores with the same certificates, inserted in different order.
        let mut store_a = ContentStore::new("test-crate");
        store_a.insert(make_cert("crate::alpha"), make_chain());
        store_a.insert(make_cert("crate::beta"), make_chain());
        store_a.insert(make_cert("crate::gamma"), make_chain());

        let mut store_b = ContentStore::new("test-crate");
        store_b.insert(make_cert("crate::gamma"), make_chain());
        store_b.insert(make_cert("crate::alpha"), make_chain());
        store_b.insert(make_cert("crate::beta"), make_chain());

        let bundle_a = CertificateBundle::from_content_store(
            &store_a,
            "0.1.0",
            "2026-04-12T00:00:00Z",
        );
        let bundle_b = CertificateBundle::from_content_store(
            &store_b,
            "0.1.0",
            "2026-04-12T00:00:00Z",
        );

        assert_eq!(
            bundle_a.manifest.merkle_root,
            bundle_b.manifest.merkle_root,
            "Merkle roots must be identical regardless of insertion order"
        );

        // Both bundles should also pass integrity verification.
        let result_a = bundle_a.verify_integrity().expect("should verify");
        let result_b = bundle_b.verify_integrity().expect("should verify");
        assert!(result_a.valid);
        assert!(result_b.valid);
        assert!(result_a.merkle_valid);
        assert!(result_b.merkle_valid);
    }
}
