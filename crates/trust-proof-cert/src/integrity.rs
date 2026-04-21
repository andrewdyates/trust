// trust-proof-cert cryptographic integrity verification
//
// CertificateDigest: SHA-256 digest of a certificate's content.
// CertificateFingerprint: compact identity hash (VC + result + solver).
// MerkleTree: batch certificate verification via Merkle tree.
// Chain integrity: verify certificate chains from leaf to root.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::{CertError, CertificateChain, ProofCertificate};

/// SHA-256 digest of a proof certificate's canonical content.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub(crate) struct CertificateDigest(pub [u8; 32]);

impl CertificateDigest {
    /// Returns the digest bytes as a hex string.
    pub fn to_hex(&self) -> String {
        self.0.iter().map(|b| format!("{b:02x}")).collect()
    }

    /// Parse from a hex string (64 hex chars).
    pub fn from_hex(hex: &str) -> Result<Self, CertError> {
        if hex.len() != 64 {
            return Err(CertError::VerificationFailed {
                reason: format!("digest hex must be 64 chars, got {}", hex.len()),
            });
        }
        let mut bytes = [0u8; 32];
        for i in 0..32 {
            bytes[i] = u8::from_str_radix(&hex[i * 2..i * 2 + 2], 16).map_err(|e| {
                CertError::VerificationFailed {
                    reason: format!("invalid hex at position {}: {e}", i * 2),
                }
            })?;
        }
        Ok(CertificateDigest(bytes))
    }
}

/// A compact fingerprint that identifies a certificate by its core verification
/// content: the VC hash, solver result (name + version + strength), and
/// certification status.
///
/// Two certificates with the same fingerprint verified the same VC with the
/// same solver configuration and reached the same status. This is useful for
/// deduplication and cache lookups without comparing the full certificate.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub(crate) struct CertificateFingerprint(pub [u8; 32]);

impl CertificateFingerprint {
    /// Returns the fingerprint bytes as a hex string.
    pub fn to_hex(&self) -> String {
        self.0.iter().map(|b| format!("{b:02x}")).collect()
    }
}

/// Compute a fingerprint from a certificate's core verification content.
///
/// The fingerprint covers: vc_hash + solver name + solver version +
/// solver strength + certification status. It intentionally excludes
/// the timestamp and proof trace so that equivalent re-verifications
/// produce the same fingerprint.
pub(crate) fn compute_fingerprint(cert: &ProofCertificate) -> CertificateFingerprint {
    let mut hasher = Sha256::new();
    hasher.update(cert.vc_hash);
    hasher.update(b"|");
    hasher.update(cert.solver.name.as_bytes());
    hasher.update(b":");
    hasher.update(cert.solver.version.as_bytes());
    hasher.update(b":");
    hasher.update(format!("{:?}", cert.solver.strength).as_bytes());
    hasher.update(b"|");
    hasher.update(format!("{:?}", cert.status).as_bytes());
    CertificateFingerprint(hasher.finalize().into())
}

/// Compute the SHA-256 digest of a certificate's canonical content.
///
/// The digest covers: function name, function hash, vc_hash, solver info,
/// proof trace, timestamp, and status. This provides tamper detection.
pub(crate) fn compute_digest(cert: &ProofCertificate) -> CertificateDigest {
    let mut hasher = Sha256::new();
    hasher.update(cert.function.as_bytes());
    hasher.update(b"|");
    hasher.update(cert.function_hash.0.as_bytes());
    hasher.update(b"|");
    hasher.update(cert.vc_hash);
    hasher.update(b"|");
    hasher.update(cert.solver.name.as_bytes());
    hasher.update(b":");
    hasher.update(cert.solver.version.as_bytes());
    hasher.update(b":");
    hasher.update(cert.solver.time_ms.to_le_bytes());
    hasher.update(b"|");
    hasher.update(&cert.proof_trace);
    hasher.update(b"|");
    hasher.update(cert.timestamp.as_bytes());
    hasher.update(b"|");
    hasher.update(format!("{:?}", cert.status).as_bytes());
    CertificateDigest(hasher.finalize().into())
}

/// Verify that a certificate matches an expected digest.
pub(crate) fn verify_digest(cert: &ProofCertificate, expected: &CertificateDigest) -> bool {
    compute_digest(cert) == *expected
}

/// Result of a full integrity check on a single certificate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct IntegrityReport {
    /// Whether the VC hash in the cert matches its VC snapshot.
    pub vc_hash_valid: bool,
    /// Whether proof steps form a well-ordered trace.
    pub proof_steps_valid: bool,
    /// Whether the certificate chain is intact (hashes link).
    pub chain_valid: bool,
    /// The computed digest.
    pub digest: CertificateDigest,
    /// The computed fingerprint.
    pub fingerprint: CertificateFingerprint,
    /// Overall pass/fail.
    pub valid: bool,
}

/// Run a full integrity check on a certificate: VC hash, proof steps,
/// chain integrity, and compute digest + fingerprint.
pub(crate) fn check_integrity(cert: &ProofCertificate) -> IntegrityReport {
    let vc_hash_valid = cert.verify_vc_hash();
    let proof_steps_valid = cert.verify_proof_steps().is_ok();
    let chain_valid = cert.chain.verify_integrity().is_ok();
    let digest = compute_digest(cert);
    let fingerprint = compute_fingerprint(cert);
    let valid = vc_hash_valid && proof_steps_valid && chain_valid;
    IntegrityReport { vc_hash_valid, proof_steps_valid, chain_valid, digest, fingerprint, valid }
}

/// Verify a certificate chain from leaf (first step) to root (last step),
/// checking that output hashes link to input hashes at each transition.
///
/// Returns `Ok(())` if the chain is intact, or a `CertError` identifying the
/// broken link.
pub(crate) fn verify_chain_integrity(chain: &CertificateChain) -> Result<(), CertError> {
    chain.verify_integrity()
}

/// Batch-verify a slice of certificates, returning an integrity report for each.
pub(crate) fn batch_check_integrity(certs: &[ProofCertificate]) -> Vec<IntegrityReport> {
    certs.iter().map(check_integrity).collect()
}

/// A Merkle inclusion proof: the path from a leaf to the root.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct MerkleProof {
    /// The leaf index in the original certificate list.
    pub leaf_index: usize,
    /// Sibling hashes along the path to the root, with direction flags.
    /// `true` means the sibling is on the right; `false` means left.
    pub path: Vec<(bool, [u8; 32])>,
    /// The Merkle root this proof validates against.
    pub root: [u8; 32],
    /// Whether this proof successfully verified.
    pub verified: bool,
}

/// A Merkle tree over certificate digests for batch verification.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct MerkleTree {
    /// All nodes in the tree, stored level by level (leaves first).
    /// Length is `2 * leaf_count.next_power_of_two() - 1` (padded).
    nodes: Vec<[u8; 32]>,
    /// Number of actual leaves (certificates).
    leaf_count: usize,
}

impl MerkleTree {
    /// Returns the Merkle root hash.
    pub fn root(&self) -> [u8; 32] {
        if self.nodes.is_empty() {
            return [0u8; 32];
        }
        self.nodes[self.nodes.len() - 1]
    }

    /// Returns the number of leaves (certificates).
    pub fn leaf_count(&self) -> usize {
        self.leaf_count
    }

    /// Generate an inclusion proof for the certificate at `leaf_index`.
    pub fn prove_inclusion(&self, leaf_index: usize) -> Option<MerkleProof> {
        if leaf_index >= self.leaf_count {
            return None;
        }

        let padded = self.leaf_count.next_power_of_two();
        let mut path = Vec::new();
        let mut idx = leaf_index;
        let mut level_start = 0;
        let mut level_size = padded;

        while level_size > 1 {
            let sibling = if idx.is_multiple_of(2) { idx + 1 } else { idx - 1 };
            let is_right = idx.is_multiple_of(2); // sibling is on the right
            path.push((is_right, self.nodes[level_start + sibling]));
            idx /= 2;
            level_start += level_size;
            level_size /= 2;
        }

        let root = self.root();
        // Verify the proof while building it
        let verified = verify_merkle_path(&self.nodes[leaf_index], &path, &root);

        Some(MerkleProof { leaf_index, path, root, verified })
    }
}

/// Verify a Merkle proof path against a root.
fn verify_merkle_path(leaf: &[u8; 32], path: &[(bool, [u8; 32])], root: &[u8; 32]) -> bool {
    let mut current = *leaf;
    for &(sibling_is_right, ref sibling) in path {
        let mut hasher = Sha256::new();
        if sibling_is_right {
            hasher.update(current);
            hasher.update(sibling);
        } else {
            hasher.update(sibling);
            hasher.update(current);
        }
        current = hasher.finalize().into();
    }
    current == *root
}

/// Hash two child nodes together to produce a parent node.
fn hash_pair(left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(left);
    hasher.update(right);
    hasher.finalize().into()
}

/// Build a Merkle tree from a slice of proof certificates.
///
/// The tree is padded to the next power of two with zero-hashes.
/// Returns an empty tree if the input is empty.
pub(crate) fn build_merkle_tree(certs: &[ProofCertificate]) -> MerkleTree {
    if certs.is_empty() {
        return MerkleTree { nodes: Vec::new(), leaf_count: 0 };
    }

    let leaf_count = certs.len();
    let padded = leaf_count.next_power_of_two();

    // Compute leaf hashes (certificate digests)
    let mut leaves: Vec<[u8; 32]> = certs.iter().map(|c| compute_digest(c).0).collect();
    // Pad with zero hashes
    leaves.resize(padded, [0u8; 32]);

    let mut nodes = leaves;

    // Build tree bottom-up
    let mut level_start = 0;
    let mut level_size = padded;
    while level_size > 1 {
        let mut parents = Vec::with_capacity(level_size / 2);
        for i in (0..level_size).step_by(2) {
            parents.push(hash_pair(&nodes[level_start + i], &nodes[level_start + i + 1]));
        }
        level_start += level_size;
        level_size /= 2;
        nodes.extend_from_slice(&parents);
    }

    MerkleTree { nodes, leaf_count }
}

/// Verify that a certificate is included in a Merkle tree.
///
/// Computes the certificate's digest, finds it in the tree's leaves,
/// and returns a `MerkleProof`.
pub(crate) fn verify_inclusion(tree: &MerkleTree, cert: &ProofCertificate) -> MerkleProof {
    let digest = compute_digest(cert);

    // Find the leaf index
    let padded = if tree.leaf_count == 0 { 0 } else { tree.leaf_count.next_power_of_two() };
    let leaf_index = (0..padded).find(|&i| tree.nodes.get(i) == Some(&digest.0));

    match leaf_index {
        Some(idx) if idx < tree.leaf_count => tree.prove_inclusion(idx).unwrap_or_else(|| {
            MerkleProof { leaf_index: idx, path: Vec::new(), root: tree.root(), verified: false }
        }),
        _ => MerkleProof {
            leaf_index: usize::MAX,
            path: Vec::new(),
            root: tree.root(),
            verified: false,
        },
    }
}

#[cfg(test)]
mod tests {
    use trust_types::ProofStrength;

    use super::*;
    use crate::chain::{ChainStep, ChainStepType};
    use crate::{FunctionHash, SolverInfo, VcSnapshot};

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

    fn make_cert_with_chain(function: &str, timestamp: &str) -> ProofCertificate {
        let mut cert = make_cert(function, timestamp);
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
        cert.chain = chain;
        cert
    }

    // --- Digest tests (existing) ---

    #[test]
    fn test_digest_deterministic() {
        let cert = make_cert("crate::foo", "2026-03-28T00:00:00Z");
        let d1 = compute_digest(&cert);
        let d2 = compute_digest(&cert);
        assert_eq!(d1, d2);
    }

    #[test]
    fn test_digest_different_certs() {
        let cert1 = make_cert("crate::foo", "2026-03-28T00:00:00Z");
        let cert2 = make_cert("crate::bar", "2026-03-28T00:00:00Z");
        assert_ne!(compute_digest(&cert1), compute_digest(&cert2));
    }

    #[test]
    fn test_verify_digest_valid() {
        let cert = make_cert("crate::foo", "2026-03-28T00:00:00Z");
        let digest = compute_digest(&cert);
        assert!(verify_digest(&cert, &digest));
    }

    #[test]
    fn test_verify_digest_tampered() {
        let cert = make_cert("crate::foo", "2026-03-28T00:00:00Z");
        let mut digest = compute_digest(&cert);
        digest.0[0] ^= 0xFF; // flip a byte
        assert!(!verify_digest(&cert, &digest));
    }

    #[test]
    fn test_digest_hex_string() {
        let cert = make_cert("crate::foo", "2026-03-28T00:00:00Z");
        let digest = compute_digest(&cert);
        let hex = digest.to_hex();
        assert_eq!(hex.len(), 64);
        assert!(hex.chars().all(|c| c.is_ascii_hexdigit()));
    }

    #[test]
    fn test_digest_hex_roundtrip() {
        let cert = make_cert("crate::foo", "2026-03-28T00:00:00Z");
        let digest = compute_digest(&cert);
        let hex = digest.to_hex();
        let restored = CertificateDigest::from_hex(&hex).expect("should parse hex");
        assert_eq!(restored, digest);
    }

    #[test]
    fn test_digest_from_hex_invalid_length() {
        let result = CertificateDigest::from_hex("abcd");
        assert!(result.is_err());
    }

    #[test]
    fn test_digest_from_hex_invalid_chars() {
        let bad = "zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz";
        let result = CertificateDigest::from_hex(bad);
        assert!(result.is_err());
    }

    // --- Fingerprint tests ---

    #[test]
    fn test_fingerprint_deterministic() {
        let cert = make_cert("crate::foo", "2026-03-28T00:00:00Z");
        let f1 = compute_fingerprint(&cert);
        let f2 = compute_fingerprint(&cert);
        assert_eq!(f1, f2);
    }

    #[test]
    fn test_fingerprint_same_for_equivalent_certs() {
        // Two certs for the same function but different timestamps should have
        // the same fingerprint (fingerprint excludes timestamp).
        let cert1 = make_cert("crate::foo", "2026-03-28T00:00:00Z");
        let cert2 = make_cert("crate::foo", "2026-03-28T00:00:01Z");
        assert_eq!(compute_fingerprint(&cert1), compute_fingerprint(&cert2));
    }

    #[test]
    fn test_fingerprint_differs_for_different_vc_content() {
        // Fingerprint is based on VC hash, so different VC content produces
        // different fingerprints (even if function names differ with same VC,
        // fingerprints would match since function name is not in fingerprint).
        let vc1 = VcSnapshot {
            kind: "Assertion".to_string(),
            formula_json: "true".to_string(),
            location: None,
        };
        let vc2 = VcSnapshot {
            kind: "Overflow".to_string(),
            formula_json: "x + y < MAX".to_string(),
            location: None,
        };
        let solver = SolverInfo {
            name: "z4".to_string(),
            version: "1.0.0".to_string(),
            time_ms: 10,
            strength: ProofStrength::smt_unsat(),
            evidence: None,
        };
        let cert1 = ProofCertificate::new_trusted(
            "crate::foo".to_string(),
            FunctionHash::from_bytes(b"foo-body"),
            vc1,
            solver.clone(),
            vec![1, 2, 3],
            "2026-03-28T00:00:00Z".to_string(),
        );
        let cert2 = ProofCertificate::new_trusted(
            "crate::foo".to_string(),
            FunctionHash::from_bytes(b"foo-body"),
            vc2,
            solver,
            vec![1, 2, 3],
            "2026-03-28T00:00:00Z".to_string(),
        );
        assert_ne!(compute_fingerprint(&cert1), compute_fingerprint(&cert2));
    }

    #[test]
    fn test_fingerprint_differs_after_upgrade() {
        let certifier_key = crate::CertSigningKey::generate(crate::TrustLevel::Certifier);
        let cert1 = make_cert("crate::foo", "2026-03-28T00:00:00Z");
        let mut cert2 = make_cert("crate::foo", "2026-03-28T00:00:00Z");
        cert2.upgrade_to_certified(&certifier_key).expect("upgrade should succeed");
        assert_ne!(compute_fingerprint(&cert1), compute_fingerprint(&cert2));
    }

    #[test]
    fn test_fingerprint_hex_string() {
        let cert = make_cert("crate::foo", "2026-03-28T00:00:00Z");
        let fp = compute_fingerprint(&cert);
        let hex = fp.to_hex();
        assert_eq!(hex.len(), 64);
        assert!(hex.chars().all(|c| c.is_ascii_hexdigit()));
    }

    // --- Integrity check tests ---

    #[test]
    fn test_check_integrity_valid() {
        let cert = make_cert_with_chain("crate::foo", "2026-03-28T00:00:00Z");
        let report = check_integrity(&cert);
        assert!(
            report.valid,
            "cert with valid chain should pass: vc={}, steps={}, chain={}",
            report.vc_hash_valid, report.proof_steps_valid, report.chain_valid
        );
        assert!(report.vc_hash_valid);
        assert!(report.proof_steps_valid);
        assert!(report.chain_valid);
    }

    #[test]
    fn test_check_integrity_bad_vc_hash() {
        let mut cert = make_cert("crate::foo", "2026-03-28T00:00:00Z");
        cert.vc_hash[0] ^= 0xFF; // corrupt VC hash
        let report = check_integrity(&cert);
        assert!(!report.valid);
        assert!(!report.vc_hash_valid);
    }

    #[test]
    fn test_check_integrity_empty_chain_is_invalid() {
        // tRust #762 F7: empty chain now fails integrity check
        let cert = make_cert("crate::foo", "2026-03-28T00:00:00Z");
        let report = check_integrity(&cert);
        assert!(!report.valid);
        assert!(!report.chain_valid);
    }

    #[test]
    fn test_batch_check_integrity() {
        let certs = vec![
            make_cert_with_chain("crate::foo", "2026-03-28T00:00:00Z"),
            make_cert_with_chain("crate::bar", "2026-03-28T00:00:01Z"),
        ];
        let reports = batch_check_integrity(&certs);
        assert_eq!(reports.len(), 2);
        assert!(reports.iter().all(|r| r.valid));
    }

    #[test]
    fn test_batch_check_integrity_mixed() {
        let good = make_cert_with_chain("crate::foo", "2026-03-28T00:00:00Z");
        let mut bad = make_cert("crate::bar", "2026-03-28T00:00:01Z");
        bad.vc_hash[0] ^= 0xFF;
        let reports = batch_check_integrity(&[good, bad]);
        assert!(reports[0].valid);
        assert!(!reports[1].valid);
    }

    // --- Chain integrity tests ---

    #[test]
    fn test_verify_chain_integrity_valid() {
        let cert = make_cert_with_chain("crate::foo", "2026-03-28T00:00:00Z");
        assert!(verify_chain_integrity(&cert.chain).is_ok());
    }

    #[test]
    fn test_verify_chain_integrity_broken() {
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
            input_hash: "WRONG-hash".to_string(),
            output_hash: "proof-hash".to_string(),
            time_ms: 42,
            timestamp: "2026-03-27T00:00:01Z".to_string(),
        });
        assert!(verify_chain_integrity(&chain).is_err());
    }

    // --- Merkle tree tests (existing) ---

    #[test]
    fn test_merkle_tree_single_cert() {
        let cert = make_cert("crate::foo", "2026-03-28T00:00:00Z");
        let tree = build_merkle_tree(std::slice::from_ref(&cert));
        assert_eq!(tree.leaf_count(), 1);
        // Root should be the hash of (leaf_digest, zero_hash)
        assert_ne!(tree.root(), [0u8; 32]);
    }

    #[test]
    fn test_merkle_tree_empty() {
        let tree = build_merkle_tree(&[]);
        assert_eq!(tree.leaf_count(), 0);
        assert_eq!(tree.root(), [0u8; 32]);
    }

    #[test]
    fn test_merkle_tree_two_certs() {
        let c1 = make_cert("crate::foo", "2026-03-28T00:00:00Z");
        let c2 = make_cert("crate::bar", "2026-03-28T00:00:01Z");
        let tree = build_merkle_tree(&[c1.clone(), c2.clone()]);
        assert_eq!(tree.leaf_count(), 2);

        // Both should be verifiable
        let proof1 = verify_inclusion(&tree, &c1);
        assert!(proof1.verified, "first cert should be included");
        let proof2 = verify_inclusion(&tree, &c2);
        assert!(proof2.verified, "second cert should be included");
    }

    #[test]
    fn test_merkle_tree_four_certs() {
        let certs: Vec<_> = (0..4)
            .map(|i| make_cert(&format!("crate::fn{i}"), &format!("2026-03-28T00:00:0{i}Z")))
            .collect();
        let tree = build_merkle_tree(&certs);
        assert_eq!(tree.leaf_count(), 4);

        for cert in &certs {
            let proof = verify_inclusion(&tree, cert);
            assert!(proof.verified, "cert {} should be included", cert.function);
        }
    }

    #[test]
    fn test_merkle_tree_three_certs_padding() {
        let certs: Vec<_> = (0..3)
            .map(|i| make_cert(&format!("crate::fn{i}"), &format!("2026-03-28T00:00:0{i}Z")))
            .collect();
        let tree = build_merkle_tree(&certs);
        assert_eq!(tree.leaf_count(), 3);
        // Padded to 4 leaves internally

        for cert in &certs {
            let proof = verify_inclusion(&tree, cert);
            assert!(proof.verified, "cert {} should be included", cert.function);
        }
    }

    #[test]
    fn test_merkle_tree_non_member() {
        let c1 = make_cert("crate::foo", "2026-03-28T00:00:00Z");
        let c2 = make_cert("crate::bar", "2026-03-28T00:00:01Z");
        let tree = build_merkle_tree(&[c1]);

        let proof = verify_inclusion(&tree, &c2);
        assert!(!proof.verified, "non-member should not verify");
    }

    #[test]
    fn test_merkle_tree_root_deterministic() {
        let certs: Vec<_> = (0..3)
            .map(|i| make_cert(&format!("crate::fn{i}"), &format!("2026-03-28T00:00:0{i}Z")))
            .collect();
        let tree1 = build_merkle_tree(&certs);
        let tree2 = build_merkle_tree(&certs);
        assert_eq!(tree1.root(), tree2.root());
    }

    #[test]
    fn test_merkle_proof_path_length() {
        // For 4 leaves, proof path should have log2(4) = 2 entries
        let certs: Vec<_> = (0..4)
            .map(|i| make_cert(&format!("crate::fn{i}"), &format!("2026-03-28T00:00:0{i}Z")))
            .collect();
        let tree = build_merkle_tree(&certs);
        let proof = tree.prove_inclusion(0).expect("should produce proof");
        assert_eq!(proof.path.len(), 2);
    }
}
