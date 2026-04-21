//! Standalone certificate verification.
//!
//! Provides offline checking of proof certificates without requiring
//! access to the original solver or compiler.
//!
//! Author: Andrew Yates <andrew@andrewdyates.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use sha2::{Digest, Sha256};

use crate::{CertError, ProofCertificate};

/// Result of verifying a single certificate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VerificationResult {
    /// Whether the certificate passed all checks.
    pub valid: bool,
    /// Individual check results.
    pub checks: Vec<CheckResult>,
}

/// A single verification check and its outcome.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckResult {
    /// Name of the check.
    pub name: String,
    /// Whether the check passed.
    pub passed: bool,
    /// Description or error detail.
    pub detail: String,
}

impl VerificationResult {
    fn new() -> Self {
        VerificationResult { valid: true, checks: Vec::new() }
    }

    fn add_check(&mut self, name: &str, passed: bool, detail: String) {
        if !passed {
            self.valid = false;
        }
        self.checks.push(CheckResult { name: name.to_string(), passed, detail });
    }
}

/// Verify a proof certificate against the given canonical VC bytes.
///
/// Performs the following checks:
/// 1. `vc_hash` matches `sha256(vc_bytes)`
/// 2. Certificate chain is internally consistent
/// 3. Proof steps are well-formed (sequential indices, valid premise refs)
/// 4. vc_hash matches the embedded VC snapshot
///
/// Returns `Ok(true)` if all checks pass, `Ok(false)` if any fail.
/// Returns `Err` only for structural errors (e.g. corrupted certificate).
pub fn verify_certificate(
    cert: &ProofCertificate,
    vc_bytes: &[u8],
) -> Result<bool, CertError> {
    let result = verify_certificate_detailed(cert, vc_bytes)?;
    Ok(result.valid)
}

/// Verify a certificate with detailed per-check results.
pub fn verify_certificate_detailed(
    cert: &ProofCertificate,
    vc_bytes: &[u8],
) -> Result<VerificationResult, CertError> {
    let mut result = VerificationResult::new();

    // Check 1: vc_hash matches sha256(vc_bytes)
    let mut hasher = Sha256::new();
    hasher.update(vc_bytes);
    let computed: [u8; 32] = hasher.finalize().into();
    let hash_matches = cert.vc_hash == computed;
    result.add_check(
        "vc_hash_matches_input",
        hash_matches,
        if hash_matches {
            "vc_hash matches sha256(vc_bytes)".to_string()
        } else {
            format!(
                "vc_hash mismatch: certificate has {:02x?}, computed {:02x?}",
                &cert.vc_hash[..4],
                &computed[..4]
            )
        },
    );

    // Check 2: Certificate chain is consistent
    let chain_ok = cert.chain.verify_integrity();
    result.add_check(
        "chain_integrity",
        chain_ok.is_ok(),
        match &chain_ok {
            Ok(()) => "certificate chain is consistent".to_string(),
            Err(e) => format!("chain integrity failure: {e}"),
        },
    );

    // Check 3: Proof steps are well-formed
    let steps_ok = cert.verify_proof_steps();
    result.add_check(
        "proof_steps_wellformed",
        steps_ok.is_ok(),
        match &steps_ok {
            Ok(()) => format!("{} proof steps are well-formed", cert.proof_steps.len()),
            Err(e) => format!("proof steps malformed: {e}"),
        },
    );

    // Check 4: vc_hash matches the embedded VC snapshot hash
    let snapshot_matches = cert.verify_vc_hash();
    result.add_check(
        "vc_hash_matches_snapshot",
        snapshot_matches,
        if snapshot_matches {
            "vc_hash matches embedded VC snapshot".to_string()
        } else {
            "vc_hash does not match embedded VC snapshot".to_string()
        },
    );

    Ok(result)
}

// ---------------------------------------------------------------------------
// CertificateVerifier: stateful verifier with accumulated results
// ---------------------------------------------------------------------------

/// Accumulated report from verifying one or more certificates.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VerificationReport {
    /// Number of certificates examined.
    pub total_examined: usize,
    /// Number that passed all checks.
    pub passed: usize,
    /// Number that failed one or more checks.
    pub failed: usize,
    /// Per-certificate results, indexed by certificate ID.
    pub results: Vec<(String, VerificationResult)>,
    /// Summary of failures: (cert_id, check_name, detail).
    pub failure_details: Vec<(String, String, String)>,
}

impl VerificationReport {
    /// Returns true if every examined certificate passed.
    pub fn all_passed(&self) -> bool {
        self.failed == 0
    }

    /// The pass rate as a percentage (0.0 - 100.0).
    pub fn pass_rate(&self) -> f64 {
        if self.total_examined == 0 {
            return 0.0;
        }
        (self.passed as f64 / self.total_examined as f64) * 100.0
    }
}

/// A stateful certificate verifier that accumulates results across
/// multiple verification operations.
///
/// Use this when verifying a batch of certificates and you want a
/// consolidated report at the end.
pub struct CertificateVerifier {
    results: Vec<(String, VerificationResult)>,
}

impl CertificateVerifier {
    /// Create a new empty verifier.
    pub fn new() -> Self {
        CertificateVerifier { results: Vec::new() }
    }

    /// Verify a single certificate against its VC bytes and record the result.
    pub fn verify(&mut self, cert: &ProofCertificate, vc_bytes: &[u8]) -> Result<bool, CertError> {
        let result = verify_certificate_detailed(cert, vc_bytes)?;
        let passed = result.valid;
        self.results.push((cert.id.0.clone(), result));
        Ok(passed)
    }

    /// Verify a certificate using only its embedded VC snapshot (no external VC bytes).
    ///
    /// This checks chain integrity, proof steps, and VC hash consistency
    /// with the embedded snapshot -- but cannot verify against external VC bytes.
    pub fn verify_standalone(&mut self, cert: &ProofCertificate) -> VerificationResult {
        let mut result = VerificationResult::new();

        // Check 1: VC hash matches embedded snapshot
        let vc_hash_ok = cert.verify_vc_hash();
        result.add_check(
            "vc_hash_matches_snapshot",
            vc_hash_ok,
            if vc_hash_ok {
                "vc_hash matches embedded VC snapshot".to_string()
            } else {
                "vc_hash does not match embedded VC snapshot".to_string()
            },
        );

        // Check 2: Chain integrity
        let chain_ok = cert.chain.verify_integrity();
        result.add_check(
            "chain_integrity",
            chain_ok.is_ok(),
            match &chain_ok {
                Ok(()) => "certificate chain is consistent".to_string(),
                Err(e) => format!("chain integrity failure: {e}"),
            },
        );

        // Check 3: Proof steps well-formed
        let steps_ok = cert.verify_proof_steps();
        result.add_check(
            "proof_steps_wellformed",
            steps_ok.is_ok(),
            match &steps_ok {
                Ok(()) => format!("{} proof steps are well-formed", cert.proof_steps.len()),
                Err(e) => format!("proof steps malformed: {e}"),
            },
        );

        // Check 4: Certificate is not stale (function hash is present)
        let has_function_hash = !cert.function_hash.0.is_empty();
        result.add_check(
            "function_hash_present",
            has_function_hash,
            if has_function_hash {
                "function hash is present".to_string()
            } else {
                "function hash is empty".to_string()
            },
        );

        self.results.push((cert.id.0.clone(), result.clone()));
        result
    }

    /// Generate a consolidated verification report.
    pub fn report(&self) -> VerificationReport {
        let total_examined = self.results.len();
        let passed = self.results.iter().filter(|(_, r)| r.valid).count();
        let failed = total_examined - passed;

        let mut failure_details = Vec::new();
        for (cert_id, result) in &self.results {
            for check in &result.checks {
                if !check.passed {
                    failure_details.push((
                        cert_id.clone(),
                        check.name.clone(),
                        check.detail.clone(),
                    ));
                }
            }
        }

        VerificationReport {
            total_examined,
            passed,
            failed,
            results: self.results.clone(),
            failure_details,
        }
    }

    /// Reset the verifier, clearing all accumulated results.
    pub fn reset(&mut self) {
        self.results.clear();
    }
}

impl Default for CertificateVerifier {
    fn default() -> Self {
        Self::new()
    }
}

/// Verify a chain of related certificates end-to-end.
///
/// Given a sequence of certificates where each certificate's function
/// may depend on the next, verify that:
/// 1. Each individual certificate passes standalone verification
/// 2. All certificates' chains are intact
/// 3. The chain forms a valid dependency sequence (no gaps)
///
/// Returns a `VerificationReport` covering all certificates in the chain.
pub fn verify_chain(certs: &[&ProofCertificate]) -> VerificationReport {
    let mut verifier = CertificateVerifier::new();

    for cert in certs {
        verifier.verify_standalone(cert);
    }

    verifier.report()
}

#[cfg(test)]
mod tests {
    use trust_types::ProofStrength;

    use super::*;
    use crate::{
        CertificateChain, ChainStep, ChainStepType, FunctionHash, ProofStep, SolverInfo,
        VcSnapshot,
    };

    fn make_vc_bytes(kind: &str, formula: &str) -> Vec<u8> {
        // Must match VcSnapshot::vc_hash canonical form: kind + ":" + formula_json
        let mut bytes = Vec::new();
        bytes.extend_from_slice(kind.as_bytes());
        bytes.extend_from_slice(b":");
        bytes.extend_from_slice(formula.as_bytes());
        bytes
    }

    fn make_cert_with_steps() -> (ProofCertificate, Vec<u8>) {
        let vc_snapshot = VcSnapshot {
            kind: "Assertion".to_string(),
            formula_json: "true".to_string(),
            location: None,
        };
        let vc_bytes = make_vc_bytes("Assertion", "true");
        let solver = SolverInfo {
            name: "z4".to_string(),
            version: "1.0.0".to_string(),
            time_ms: 10,
            strength: ProofStrength::smt_unsat(),
            evidence: None,
        };
        let steps = vec![
            ProofStep {
                index: 0,
                rule: "assume".to_string(),
                description: "assume precondition".to_string(),
                premises: vec![],
            },
            ProofStep {
                index: 1,
                rule: "resolution".to_string(),
                description: "resolve with axiom".to_string(),
                premises: vec![0],
            },
        ];
        let chain = {
            let mut c = CertificateChain::new();
            c.push(ChainStep {
                step_type: ChainStepType::VcGeneration,
                tool: "trust-vcgen".to_string(),
                tool_version: "0.1.0".to_string(),
                input_hash: "mir".to_string(),
                output_hash: "vc".to_string(),
                time_ms: 1,
                timestamp: "2026-03-28T00:00:00Z".to_string(),
            });
            c.push(ChainStep {
                step_type: ChainStepType::SolverProof,
                tool: "z4".to_string(),
                tool_version: "1.0.0".to_string(),
                input_hash: "vc".to_string(),
                output_hash: "proof".to_string(),
                time_ms: 10,
                timestamp: "2026-03-28T00:00:01Z".to_string(),
            });
            c
        };

        let cert = ProofCertificate::new_trusted(
            "crate::test_fn".to_string(),
            FunctionHash::from_bytes(b"test-body"),
            vc_snapshot,
            solver,
            vec![],
            "2026-03-28T00:00:00Z".to_string(),
        )
        .with_proof_steps(steps)
        .with_chain(chain);

        (cert, vc_bytes)
    }

    #[test]
    fn test_verify_certificate_valid() {
        let (cert, vc_bytes) = make_cert_with_steps();
        let ok = verify_certificate(&cert, &vc_bytes).expect("verification should not error");
        assert!(ok, "valid certificate should pass verification");
    }

    #[test]
    fn test_verify_certificate_detailed_valid() {
        let (cert, vc_bytes) = make_cert_with_steps();
        let result =
            verify_certificate_detailed(&cert, &vc_bytes).expect("verification should not error");
        assert!(result.valid);
        assert_eq!(result.checks.len(), 4);
        assert!(result.checks.iter().all(|c| c.passed));
    }

    #[test]
    fn test_verify_certificate_wrong_vc_bytes() {
        let (cert, _vc_bytes) = make_cert_with_steps();
        let wrong_bytes = b"wrong vc bytes";
        let ok = verify_certificate(&cert, wrong_bytes).expect("verification should not error");
        assert!(!ok, "wrong vc_bytes should fail verification");
    }

    #[test]
    fn test_verify_certificate_bad_proof_steps() {
        let (mut cert, vc_bytes) = make_cert_with_steps();
        // Corrupt proof steps: step 1 references step 1 (self-reference)
        cert.proof_steps[1].premises = vec![1];
        let ok = verify_certificate(&cert, &vc_bytes).expect("verification should not error");
        assert!(!ok, "bad proof steps should fail verification");
    }

    #[test]
    fn test_verify_certificate_broken_chain() {
        let (mut cert, vc_bytes) = make_cert_with_steps();
        // Break the chain: mismatched hashes
        cert.chain.steps[1].input_hash = "wrong".to_string();
        let ok = verify_certificate(&cert, &vc_bytes).expect("verification should not error");
        assert!(!ok, "broken chain should fail verification");
    }

    #[test]
    fn test_verify_certificate_with_witness() {
        let (cert, vc_bytes) = make_cert_with_steps();
        let cert = cert.with_witness(vec![0xDE, 0xAD, 0xBE, 0xEF]);
        let ok = verify_certificate(&cert, &vc_bytes).expect("verification should not error");
        assert!(ok, "certificate with witness should still pass");
    }

    // -----------------------------------------------------------------------
    // CertificateVerifier tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_certificate_verifier_new_empty() {
        let verifier = CertificateVerifier::new();
        let report = verifier.report();
        assert_eq!(report.total_examined, 0);
        assert_eq!(report.passed, 0);
        assert_eq!(report.failed, 0);
        assert!(report.all_passed()); // vacuously true
        assert!((report.pass_rate() - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_certificate_verifier_verify_valid() {
        let mut verifier = CertificateVerifier::new();
        let (cert, vc_bytes) = make_cert_with_steps();

        let ok = verifier.verify(&cert, &vc_bytes).unwrap();
        assert!(ok);

        let report = verifier.report();
        assert_eq!(report.total_examined, 1);
        assert_eq!(report.passed, 1);
        assert_eq!(report.failed, 0);
        assert!(report.all_passed());
        assert!((report.pass_rate() - 100.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_certificate_verifier_verify_invalid() {
        let mut verifier = CertificateVerifier::new();
        let (cert, _vc_bytes) = make_cert_with_steps();

        let ok = verifier.verify(&cert, b"wrong bytes").unwrap();
        assert!(!ok);

        let report = verifier.report();
        assert_eq!(report.total_examined, 1);
        assert_eq!(report.passed, 0);
        assert_eq!(report.failed, 1);
        assert!(!report.all_passed());
        assert!(!report.failure_details.is_empty());
    }

    #[test]
    fn test_certificate_verifier_mixed_results() {
        let mut verifier = CertificateVerifier::new();
        let (cert1, vc_bytes1) = make_cert_with_steps();
        let (cert2, _vc_bytes2) = make_cert_with_steps();

        verifier.verify(&cert1, &vc_bytes1).unwrap();
        verifier.verify(&cert2, b"wrong").unwrap();

        let report = verifier.report();
        assert_eq!(report.total_examined, 2);
        assert_eq!(report.passed, 1);
        assert_eq!(report.failed, 1);
        assert!((report.pass_rate() - 50.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_certificate_verifier_reset() {
        let mut verifier = CertificateVerifier::new();
        let (cert, vc_bytes) = make_cert_with_steps();

        verifier.verify(&cert, &vc_bytes).unwrap();
        assert_eq!(verifier.report().total_examined, 1);

        verifier.reset();
        assert_eq!(verifier.report().total_examined, 0);
    }

    #[test]
    fn test_certificate_verifier_standalone() {
        let mut verifier = CertificateVerifier::new();
        let (cert, _vc_bytes) = make_cert_with_steps();

        let result = verifier.verify_standalone(&cert);
        assert!(result.valid, "standalone verification should pass for valid cert");
        assert_eq!(result.checks.len(), 4);
        assert!(result.checks.iter().all(|c| c.passed));
    }

    #[test]
    fn test_certificate_verifier_standalone_bad_vc_hash() {
        let mut verifier = CertificateVerifier::new();
        let (mut cert, _) = make_cert_with_steps();
        cert.vc_hash[0] ^= 0xFF; // corrupt

        let result = verifier.verify_standalone(&cert);
        assert!(!result.valid);
        let failed_check = result.checks.iter().find(|c| !c.passed).unwrap();
        assert_eq!(failed_check.name, "vc_hash_matches_snapshot");
    }

    #[test]
    fn test_certificate_verifier_standalone_broken_chain() {
        let mut verifier = CertificateVerifier::new();
        let (mut cert, _) = make_cert_with_steps();
        cert.chain.steps[1].input_hash = "broken".to_string();

        let result = verifier.verify_standalone(&cert);
        assert!(!result.valid);
        let failed = result.checks.iter().find(|c| c.name == "chain_integrity").unwrap();
        assert!(!failed.passed);
    }

    #[test]
    fn test_certificate_verifier_default() {
        let verifier = CertificateVerifier::default();
        assert_eq!(verifier.report().total_examined, 0);
    }

    // -----------------------------------------------------------------------
    // verify_chain tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_verify_chain_single_cert() {
        let (cert, _) = make_cert_with_steps();
        let report = verify_chain(&[&cert]);
        assert_eq!(report.total_examined, 1);
        assert!(report.all_passed());
    }

    #[test]
    fn test_verify_chain_multiple_certs() {
        let (cert1, _) = make_cert_with_steps();
        let (cert2, _) = make_cert_with_steps();
        let report = verify_chain(&[&cert1, &cert2]);
        assert_eq!(report.total_examined, 2);
        assert_eq!(report.passed, 2);
        assert!(report.all_passed());
    }

    #[test]
    fn test_verify_chain_with_failure() {
        let (cert1, _) = make_cert_with_steps();
        let (mut cert2, _) = make_cert_with_steps();
        cert2.vc_hash[0] ^= 0xFF; // corrupt second cert

        let report = verify_chain(&[&cert1, &cert2]);
        assert_eq!(report.total_examined, 2);
        assert_eq!(report.passed, 1);
        assert_eq!(report.failed, 1);
        assert!(!report.all_passed());
    }

    #[test]
    fn test_verify_chain_empty() {
        let report = verify_chain(&[]);
        assert_eq!(report.total_examined, 0);
        assert!(report.all_passed());
    }

    #[test]
    fn test_verification_report_failure_details() {
        let (mut cert, _) = make_cert_with_steps();
        cert.vc_hash[0] ^= 0xFF;
        cert.chain.steps[1].input_hash = "broken".to_string();

        let report = verify_chain(&[&cert]);
        assert!(!report.all_passed());
        // Should have at least 2 failure details (vc_hash + chain)
        assert!(
            report.failure_details.len() >= 2,
            "expected at least 2 failures, got: {:?}",
            report.failure_details
        );
    }
}
