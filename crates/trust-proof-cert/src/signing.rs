// tRust: Ed25519 cryptographic signing for proof certificates (#689)
//
// Prevents certificate forgery by signing the canonical certificate content
// with Ed25519. Without a valid signature, certificates cannot be upgraded
// to Certified status.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use ed25519_dalek::{Signature, Signer, SigningKey, Verifier, VerifyingKey};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::{CertError, ProofCertificate};

/// Trust level for signing keys, controlling what operations they authorize.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum TrustLevel {
    /// Solver-produced proof (z4, sunder, etc.). Can create Trusted certificates.
    Solver,
    /// Independent verifier (lean5). Can upgrade to Certified.
    Certifier,
    /// Root trust anchor. Can sign any certificate.
    Root,
}

/// An Ed25519 signing key with an associated trust level.
pub struct CertSigningKey {
    key: SigningKey,
    trust_level: TrustLevel,
}

impl CertSigningKey {
    /// Generate a new random signing key at the given trust level.
    pub fn generate(trust_level: TrustLevel) -> Self {
        let mut rng = rand::thread_rng();
        let key = SigningKey::generate(&mut rng);
        CertSigningKey { key, trust_level }
    }

    /// Create from raw key bytes (32 bytes).
    pub fn from_bytes(bytes: &[u8; 32], trust_level: TrustLevel) -> Self {
        let key = SigningKey::from_bytes(bytes);
        CertSigningKey { key, trust_level }
    }

    /// Export the raw secret key bytes.
    pub fn to_bytes(&self) -> [u8; 32] {
        self.key.to_bytes()
    }

    /// Get the trust level.
    pub fn trust_level(&self) -> TrustLevel {
        self.trust_level
    }

    /// Get the corresponding public verifying key.
    pub fn verifying_key(&self) -> CertVerifyingKey {
        CertVerifyingKey {
            key: self.key.verifying_key(),
            trust_level: self.trust_level,
        }
    }

    /// Sign a proof certificate. Produces a `CertificateSignature` that
    /// covers the canonical certificate content (function, vc_hash, solver,
    /// status, version).
    pub fn sign(&self, cert: &ProofCertificate) -> CertificateSignature {
        let canonical = canonical_bytes(cert, self.trust_level);
        let sig = self.key.sign(&canonical);
        CertificateSignature {
            signature_bytes: sig.to_bytes().to_vec(),
            public_key_bytes: self.key.verifying_key().to_bytes().to_vec(),
            trust_level: self.trust_level,
        }
    }
}

/// An Ed25519 public verifying key with an associated trust level.
#[derive(Debug, Clone)]
pub struct CertVerifyingKey {
    key: VerifyingKey,
    trust_level: TrustLevel,
}

impl CertVerifyingKey {
    /// Create from raw public key bytes (32 bytes).
    pub fn from_bytes(bytes: &[u8; 32], trust_level: TrustLevel) -> Result<Self, CertError> {
        let key = VerifyingKey::from_bytes(bytes).map_err(|e| CertError::VerificationFailed {
            reason: format!("invalid Ed25519 public key: {e}"),
        })?;
        Ok(CertVerifyingKey { key, trust_level })
    }

    /// Get the trust level.
    pub fn trust_level(&self) -> TrustLevel {
        self.trust_level
    }

    /// Get the raw public key bytes.
    pub fn to_bytes(&self) -> [u8; 32] {
        self.key.to_bytes()
    }

    /// Verify a certificate signature against this public key.
    pub fn verify_signature(
        &self,
        cert: &ProofCertificate,
        sig: &CertificateSignature,
    ) -> Result<(), CertError> {
        let canonical = canonical_bytes(cert, self.trust_level);
        let signature = Signature::from_slice(&sig.signature_bytes).map_err(|e| {
            CertError::VerificationFailed {
                reason: format!("invalid signature bytes: {e}"),
            }
        })?;
        self.key.verify(&canonical, &signature).map_err(|e| CertError::VerificationFailed {
            reason: format!("Ed25519 signature verification failed: {e}"),
        })
    }
}

/// A cryptographic signature over a proof certificate's canonical content.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CertificateSignature {
    /// Raw Ed25519 signature bytes (64 bytes).
    pub signature_bytes: Vec<u8>,
    /// Public key of the signer (32 bytes).
    pub public_key_bytes: Vec<u8>,
    /// Trust level of the signer.
    pub trust_level: TrustLevel,
}

impl CertificateSignature {
    /// Verify this signature against the given certificate.
    /// Reconstructs the verifying key from the embedded public key bytes.
    pub fn verify(&self, cert: &ProofCertificate) -> Result<(), CertError> {
        let pk_bytes: [u8; 32] =
            self.public_key_bytes.clone().try_into().map_err(|_| CertError::VerificationFailed {
                reason: format!(
                    "public key must be 32 bytes, got {}",
                    self.public_key_bytes.len()
                ),
            })?;
        let vk = CertVerifyingKey::from_bytes(&pk_bytes, self.trust_level)?;
        vk.verify_signature(cert, self)
    }
}

/// A keystore holding signing keys at different trust levels.
pub struct Keystore {
    keys: Vec<CertSigningKey>,
}

impl Keystore {
    /// Create an empty keystore.
    pub fn new() -> Self {
        Keystore { keys: Vec::new() }
    }

    /// Add a signing key.
    pub fn add_key(&mut self, key: CertSigningKey) {
        self.keys.push(key);
    }

    /// Get the first key at the given trust level.
    pub fn key_for_level(&self, level: TrustLevel) -> Option<&CertSigningKey> {
        self.keys.iter().find(|k| k.trust_level == level)
    }

    /// Generate and add a key at the given trust level.
    pub fn generate_key(&mut self, level: TrustLevel) -> &CertSigningKey {
        self.keys.push(CertSigningKey::generate(level));
        self.keys.last().expect("just pushed")
    }

    /// Number of keys in the keystore.
    pub fn len(&self) -> usize {
        self.keys.len()
    }

    /// Whether the keystore is empty.
    pub fn is_empty(&self) -> bool {
        self.keys.is_empty()
    }
}

impl Default for Keystore {
    fn default() -> Self {
        Self::new()
    }
}

/// Compute the canonical bytes of a certificate for signing/verification.
///
/// This covers the security-critical fields that an attacker would want to forge:
/// function identity, VC content, solver identity, certification status, version,
/// and trust level.
///
/// tRust #803 P0-4: `trust_level` is now included in the signed data. Previously
/// it was stored in `CertificateSignature` but NOT covered by the signature,
/// allowing an attacker to escalate trust level (e.g., Solver -> Root) without
/// invalidating the signature.
pub(crate) fn canonical_bytes(cert: &ProofCertificate, trust_level: TrustLevel) -> Vec<u8> {
    let mut hasher = Sha256::new();
    // Trust level (tRust #803 P0-4: must be first to prevent prefix collisions)
    hasher.update(format!("{trust_level:?}").as_bytes());
    hasher.update(b"|");
    // Function identity
    hasher.update(cert.function.as_bytes());
    hasher.update(b"|");
    // Function hash
    hasher.update(cert.function_hash.0.as_bytes());
    hasher.update(b"|");
    // VC hash (the 32-byte content hash)
    hasher.update(cert.vc_hash);
    hasher.update(b"|");
    // Solver identity
    hasher.update(cert.solver.name.as_bytes());
    hasher.update(b":");
    hasher.update(cert.solver.version.as_bytes());
    hasher.update(b"|");
    // Certification status
    let status_byte = match cert.status {
        crate::CertificationStatus::Trusted => 0u8,
        crate::CertificationStatus::Certified => 1u8,
    };
    hasher.update([status_byte]);
    hasher.update(b"|");
    // Version
    hasher.update(cert.version.to_le_bytes());
    hasher.update(b"|");
    // Timestamp
    hasher.update(cert.timestamp.as_bytes());

    hasher.finalize().to_vec()
}

/// Sign a certificate in place, attaching the signature.
pub fn sign_certificate(cert: &mut ProofCertificate, key: &CertSigningKey) {
    cert.signature = Some(key.sign(cert));
}

/// Verify a certificate's signature. Returns Ok(()) if signature is valid,
/// Err if missing or invalid.
pub fn verify_certificate_signature(cert: &ProofCertificate) -> Result<(), CertError> {
    match &cert.signature {
        None => Err(CertError::VerificationFailed {
            reason: "certificate has no cryptographic signature".to_string(),
        }),
        Some(sig) => sig.verify(cert),
    }
}

#[cfg(test)]
mod tests {
    use trust_types::ProofStrength;

    use super::*;
    use crate::{FunctionHash, SolverInfo, VcSnapshot};

    fn make_test_cert() -> ProofCertificate {
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
            "crate::test_fn".to_string(),
            FunctionHash::from_bytes(b"test-body"),
            vc_snapshot,
            solver,
            vec![],
            "2026-03-28T00:00:00Z".to_string(),
        )
    }

    #[test]
    fn test_sign_and_verify() {
        let key = CertSigningKey::generate(TrustLevel::Solver);
        let cert = make_test_cert();
        let sig = key.sign(&cert);
        assert!(sig.verify(&cert).is_ok());
    }

    #[test]
    fn test_sign_certificate_in_place() {
        let key = CertSigningKey::generate(TrustLevel::Solver);
        let mut cert = make_test_cert();
        sign_certificate(&mut cert, &key);
        assert!(cert.signature.is_some());
        assert!(verify_certificate_signature(&cert).is_ok());
    }

    #[test]
    fn test_unsigned_certificate_fails_verification() {
        let cert = make_test_cert();
        let result = verify_certificate_signature(&cert);
        assert!(result.is_err());
        let err_msg = result.unwrap_err().to_string();
        assert!(err_msg.contains("no cryptographic signature"));
    }

    #[test]
    fn test_tampered_certificate_fails_verification() {
        let key = CertSigningKey::generate(TrustLevel::Solver);
        let mut cert = make_test_cert();
        let sig = key.sign(&cert);
        cert.signature = Some(sig);

        // Tamper with the function name
        cert.function = "crate::tampered_fn".to_string();

        let result = verify_certificate_signature(&cert);
        assert!(result.is_err());
        let err_msg = result.unwrap_err().to_string();
        assert!(err_msg.contains("signature verification failed"));
    }

    #[test]
    fn test_wrong_key_fails_verification() {
        let key1 = CertSigningKey::generate(TrustLevel::Solver);
        let key2 = CertSigningKey::generate(TrustLevel::Solver);
        let cert = make_test_cert();
        let sig = key1.sign(&cert);

        // Verify with wrong key's public key
        let vk2 = key2.verifying_key();
        let result = vk2.verify_signature(&cert, &sig);
        assert!(result.is_err());
    }

    #[test]
    fn test_keystore_basic() {
        let mut ks = Keystore::new();
        assert!(ks.is_empty());
        assert_eq!(ks.len(), 0);

        ks.generate_key(TrustLevel::Solver);
        ks.generate_key(TrustLevel::Certifier);
        assert_eq!(ks.len(), 2);

        assert!(ks.key_for_level(TrustLevel::Solver).is_some());
        assert!(ks.key_for_level(TrustLevel::Certifier).is_some());
        assert!(ks.key_for_level(TrustLevel::Root).is_none());
    }

    #[test]
    fn test_trust_levels() {
        let solver_key = CertSigningKey::generate(TrustLevel::Solver);
        let certifier_key = CertSigningKey::generate(TrustLevel::Certifier);
        let root_key = CertSigningKey::generate(TrustLevel::Root);

        assert_eq!(solver_key.trust_level(), TrustLevel::Solver);
        assert_eq!(certifier_key.trust_level(), TrustLevel::Certifier);
        assert_eq!(root_key.trust_level(), TrustLevel::Root);
    }

    #[test]
    fn test_key_serialization_roundtrip() {
        let key = CertSigningKey::generate(TrustLevel::Root);
        let bytes = key.to_bytes();
        let restored = CertSigningKey::from_bytes(&bytes, TrustLevel::Root);
        assert_eq!(key.verifying_key().to_bytes(), restored.verifying_key().to_bytes());
    }

    #[test]
    fn test_verifying_key_from_bytes() {
        let key = CertSigningKey::generate(TrustLevel::Solver);
        let pk_bytes = key.verifying_key().to_bytes();
        let vk = CertVerifyingKey::from_bytes(&pk_bytes, TrustLevel::Solver);
        assert!(vk.is_ok());
    }

    #[test]
    fn test_verifying_key_from_bad_bytes() {
        let bad_bytes = [0u8; 32]; // all zeros is not a valid Ed25519 point
        // Note: all-zeros may or may not be a valid point depending on impl.
        // Use a clearly invalid approach:
        let result = CertVerifyingKey::from_bytes(&bad_bytes, TrustLevel::Solver);
        // Either succeeds or fails; just ensuring no panic
        let _ = result;
    }

    #[test]
    fn test_canonical_bytes_deterministic() {
        let cert = make_test_cert();
        let b1 = canonical_bytes(&cert, TrustLevel::Solver);
        let b2 = canonical_bytes(&cert, TrustLevel::Solver);
        assert_eq!(b1, b2);
    }

    #[test]
    fn test_canonical_bytes_differ_on_change() {
        let cert1 = make_test_cert();
        let mut cert2 = make_test_cert();
        cert2.function = "crate::other_fn".to_string();
        assert_ne!(canonical_bytes(&cert1, TrustLevel::Solver), canonical_bytes(&cert2, TrustLevel::Solver));
    }

    #[test]
    fn test_canonical_bytes_differ_on_trust_level() {
        // tRust #803 P0-4: trust_level must affect canonical bytes
        let cert = make_test_cert();
        let solver_bytes = canonical_bytes(&cert, TrustLevel::Solver);
        let root_bytes = canonical_bytes(&cert, TrustLevel::Root);
        assert_ne!(solver_bytes, root_bytes, "different trust levels must produce different canonical bytes");
    }

    #[test]
    fn test_trust_level_forgery_detected() {
        let solver_key = CertSigningKey::generate(TrustLevel::Solver);
        let cert = make_test_cert();
        let sig = solver_key.sign(&cert);

        let forged_sig = CertificateSignature { trust_level: TrustLevel::Root, ..sig.clone() };

        assert_eq!(forged_sig.signature_bytes, sig.signature_bytes);
        assert_eq!(forged_sig.public_key_bytes, sig.public_key_bytes);

        let result = forged_sig.verify(&cert);
        assert!(result.is_err());
        let err_msg = result.unwrap_err().to_string();
        assert!(err_msg.contains("signature verification failed"));
    }

    #[test]
    fn test_trust_level_matches_between_sign_and_verify() {
        let cert = make_test_cert();

        let root_key = CertSigningKey::generate(TrustLevel::Root);
        let root_sig = root_key.sign(&cert);
        assert!(root_sig.verify(&cert).is_ok());

        let solver_key = CertSigningKey::generate(TrustLevel::Solver);
        let solver_sig = solver_key.sign(&cert);
        let forged_sig = CertificateSignature {
            trust_level: TrustLevel::Root,
            ..solver_sig.clone()
        };

        let result = forged_sig.verify(&cert);
        assert!(result.is_err());
        let err_msg = result.unwrap_err().to_string();
        assert!(err_msg.contains("signature verification failed"));
    }

    #[test]
    fn test_signature_serde_roundtrip() {
        let key = CertSigningKey::generate(TrustLevel::Solver);
        let cert = make_test_cert();
        let sig = key.sign(&cert);

        let json = serde_json::to_string(&sig).expect("should serialize");
        let restored: CertificateSignature =
            serde_json::from_str(&json).expect("should deserialize");
        assert_eq!(sig, restored);
        assert!(restored.verify(&cert).is_ok());
    }

    #[test]
    fn test_upgrade_requires_signature() {
        let solver_key = CertSigningKey::generate(TrustLevel::Solver);
        let certifier_key = CertSigningKey::generate(TrustLevel::Certifier);

        let mut cert = make_test_cert();
        // Sign with solver key first
        sign_certificate(&mut cert, &solver_key);

        // Upgrade should require Certifier or Root trust level
        let result = cert.upgrade_to_certified(&certifier_key);
        assert!(result.is_ok());
        assert_eq!(cert.status, crate::CertificationStatus::Certified);
    }

    #[test]
    fn test_upgrade_rejects_solver_level() {
        let solver_key = CertSigningKey::generate(TrustLevel::Solver);
        let mut cert = make_test_cert();
        sign_certificate(&mut cert, &solver_key);

        let result = cert.upgrade_to_certified(&solver_key);
        assert!(result.is_err());
        let err_msg = result.unwrap_err().to_string();
        assert!(err_msg.contains("Certifier or Root"));
    }
}
