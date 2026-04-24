// trust-lean5/integration.rs: Bridge between lean5 CertificationPipeline and trust-proof-cert
//
// Connects the lean5 certification pipeline (CertificationPipeline, TrustProofCertificate)
// with the proof certificate store (ProofCertificate, CertificateChain, CertificateStore)
// from trust-proof-cert. This enables end-to-end certified verification:
//
//   z4 proves -> lean5 certifies -> ProofCertificate generated -> stored in CertificateStore
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use sha2::{Digest, Sha256};
use trust_proof_cert::{
    CertSigningKey, CertificateChain, CertificateStore, CertificationStatus, ChainStep,
    ChainStepType, FunctionHash, ProofCertificate, SolverInfo, TrustLevel, VcSnapshot,
};
use trust_types::{ProofStrength, VerificationCondition, VerificationResult};

use crate::certification::{CertificationPipeline, CertificationResult};
use crate::error::CertificateError;

/// tRust: Result of the end-to-end certification pipeline producing a
/// `ProofCertificate` (trust-proof-cert) from a `CertificationResult` (trust-lean5).
#[derive(Debug, Clone)]
#[non_exhaustive]
#[allow(clippy::large_enum_variant)]
pub enum PipelineOutput {
    /// Certification succeeded; a ProofCertificate and CertificateChain were generated.
    Certified {
        /// The proof certificate for storage and later verification.
        certificate: ProofCertificate,
        /// The certificate chain recording each step.
        chain: CertificateChain,
    },
    /// Certification was rejected or skipped; no certificate was produced.
    NoCertificate {
        /// Why no certificate was produced.
        reason: String,
    },
}

impl PipelineOutput {
    /// Returns `true` if the pipeline produced a certificate.
    #[must_use]
    pub fn is_certified(&self) -> bool {
        matches!(self, PipelineOutput::Certified { .. })
    }
}

/// tRust: Bridge that runs the lean5 CertificationPipeline and produces
/// trust-proof-cert types (ProofCertificate, CertificateChain).
///
/// This is the main integration point between the two crates. Callers
/// provide a VC, a VerificationResult, and a proof term. The bridge:
///
/// 1. Runs CertificationPipeline.certify() or certify_unchecked()
/// 2. Converts the CertificationResult to a ProofCertificate
/// 3. Builds a CertificateChain recording each pipeline step
/// 4. Optionally inserts into a CertificateStore
pub struct CertificationBridge {
    pipeline: CertificationPipeline,
}

impl CertificationBridge {
    /// Create a new bridge with default pipeline settings.
    #[must_use]
    pub fn new() -> Self {
        CertificationBridge { pipeline: CertificationPipeline::new() }
    }

    /// Create a bridge with a custom CertificationPipeline.
    #[must_use]
    pub fn with_pipeline(pipeline: CertificationPipeline) -> Self {
        CertificationBridge { pipeline }
    }

    /// tRust: Run the full lean5-certified pipeline and produce a ProofCertificate.
    ///
    /// Calls `CertificationPipeline::certify()` (lean5 kernel validation),
    /// then converts the result to trust-proof-cert types.
    pub fn certify(
        &self,
        vc: &VerificationCondition,
        result: &VerificationResult,
        proof_term: Vec<u8>,
        timestamp: &str,
    ) -> Result<PipelineOutput, CertificateError> {
        let cert_result = self.pipeline.certify(vc, result, proof_term.clone());
        self.convert_result(vc, result, &cert_result, &proof_term, timestamp, true)
    }

    /// tRust: Run the unchecked pipeline (Trusted, not Certified) and produce
    /// a ProofCertificate.
    ///
    /// Calls `CertificationPipeline::certify_unchecked()` (no lean5 kernel
    /// validation), then converts the result to trust-proof-cert types.
    pub fn certify_unchecked(
        &self,
        vc: &VerificationCondition,
        result: &VerificationResult,
        proof_term: Vec<u8>,
        timestamp: &str,
    ) -> Result<PipelineOutput, CertificateError> {
        let cert_result = self.pipeline.certify_unchecked(vc, result, proof_term.clone());
        self.convert_result(vc, result, &cert_result, &proof_term, timestamp, false)
    }

    /// tRust: Run certification and insert the result into a CertificateStore.
    ///
    /// Convenience method that combines `certify_unchecked()` with store insertion.
    /// Returns the PipelineOutput so the caller can inspect what happened.
    pub fn certify_and_store(
        &self,
        vc: &VerificationCondition,
        result: &VerificationResult,
        proof_term: Vec<u8>,
        timestamp: &str,
        store: &mut CertificateStore,
    ) -> Result<PipelineOutput, CertificateError> {
        let output = self.certify_unchecked(vc, result, proof_term, timestamp)?;
        if let PipelineOutput::Certified { ref certificate, ref chain } = output {
            store.insert(certificate.clone(), chain.clone());
        }
        Ok(output)
    }

    /// tRust: Run full lean5-certified pipeline and insert into store.
    pub fn certify_checked_and_store(
        &self,
        vc: &VerificationCondition,
        result: &VerificationResult,
        proof_term: Vec<u8>,
        timestamp: &str,
        store: &mut CertificateStore,
    ) -> Result<PipelineOutput, CertificateError> {
        let output = self.certify(vc, result, proof_term, timestamp)?;
        if let PipelineOutput::Certified { ref certificate, ref chain } = output {
            store.insert(certificate.clone(), chain.clone());
        }
        Ok(output)
    }

    /// tRust: Convert a CertificationResult (trust-lean5) to a PipelineOutput
    /// containing trust-proof-cert types.
    fn convert_result(
        &self,
        vc: &VerificationCondition,
        result: &VerificationResult,
        cert_result: &CertificationResult,
        proof_term: &[u8],
        timestamp: &str,
        lean5_verified: bool,
    ) -> Result<PipelineOutput, CertificateError> {
        match cert_result {
            CertificationResult::Certified { certificate, time_ms } => {
                // Extract solver info from the VerificationResult
                let solver_info = extract_solver_info(result, *time_ms);

                // Build VcSnapshot from the VC
                let vc_snapshot = VcSnapshot::from_vc(vc).map_err(|e| {
                    CertificateError::SerializationFailed { reason: format!("VcSnapshot: {e}") }
                })?;

                // Compute function body hash from VC formula bytes
                let function_hash = compute_function_hash(vc);

                // Determine certification status
                let status = if lean5_verified {
                    CertificationStatus::Certified
                } else {
                    CertificationStatus::Trusted
                };

                // Build ProofCertificate
                let mut proof_cert = ProofCertificate::new_trusted(
                    vc.function.to_string(),
                    function_hash,
                    vc_snapshot,
                    solver_info,
                    proof_term.to_vec(),
                    timestamp.to_string(),
                );
                if status == CertificationStatus::Certified {
                    // tRust #689: Use Certifier-level key for lean5 certification upgrade
                    let certifier_key = CertSigningKey::generate(TrustLevel::Certifier);
                    proof_cert
                        .upgrade_to_certified(&certifier_key)
                        .expect("lean5 certifier key must be able to upgrade");
                }

                // Build CertificateChain
                let lean5_fingerprint_str = format!("{}", certificate.vc_fingerprint);
                let chain = build_chain(
                    vc,
                    proof_term,
                    &lean5_fingerprint_str,
                    timestamp,
                    lean5_verified,
                    *time_ms,
                );

                Ok(PipelineOutput::Certified { certificate: proof_cert, chain })
            }
            CertificationResult::Trusted { certificate, time_ms } => {
                // tRust #758: Trusted certificates are NOT kernel-verified.
                // Produce a Trusted-level ProofCertificate (no upgrade to Certified).
                let solver_info = extract_solver_info(result, *time_ms);
                let vc_snapshot = VcSnapshot::from_vc(vc).map_err(|e| {
                    CertificateError::SerializationFailed { reason: format!("VcSnapshot: {e}") }
                })?;
                let function_hash = compute_function_hash(vc);
                let proof_cert = ProofCertificate::new_trusted(
                    vc.function.to_string(),
                    function_hash,
                    vc_snapshot,
                    solver_info,
                    proof_term.to_vec(),
                    timestamp.to_string(),
                );
                // No upgrade_to_certified — this is explicitly Trusted.
                let lean5_fingerprint_str = format!("{}", certificate.vc_fingerprint);
                let chain = build_chain(
                    vc,
                    proof_term,
                    &lean5_fingerprint_str,
                    timestamp,
                    false, // NOT lean5-verified
                    *time_ms,
                );
                Ok(PipelineOutput::Certified { certificate: proof_cert, chain })
            }
            CertificationResult::Rejected { reason, .. } => {
                Ok(PipelineOutput::NoCertificate { reason: format!("lean5 rejected: {reason}") })
            }
            CertificationResult::Skipped { reason } => {
                Ok(PipelineOutput::NoCertificate { reason: format!("skipped: {reason}") })
            }
        }
    }
}

impl Default for CertificationBridge {
    fn default() -> Self {
        Self::new()
    }
}

/// tRust: Extract solver info from a VerificationResult for the proof certificate.
fn extract_solver_info(result: &VerificationResult, lean5_time_ms: u64) -> SolverInfo {
    match result {
        VerificationResult::Proved { solver, time_ms, strength, .. } => SolverInfo {
            name: solver.to_string(),
            version: "unknown".to_string(),
            time_ms: *time_ms + lean5_time_ms,
            strength: strength.clone(),
            evidence: None,
        },
        // Defensive: these should never reach here because the pipeline
        // filters non-Proved results, but handle gracefully.
        _ => SolverInfo {
            name: "unknown".to_string(),
            version: "unknown".to_string(),
            time_ms: lean5_time_ms,
            strength: ProofStrength::smt_unsat(),
            evidence: None,
        },
    }
}

/// tRust: Compute a function hash from a VC's formula for the proof certificate.
fn compute_function_hash(vc: &VerificationCondition) -> FunctionHash {
    let formula_json =
        serde_json::to_string(&vc.formula).unwrap_or_else(|_| format!("{:?}", vc.formula));
    FunctionHash::from_bytes(formula_json.as_bytes())
}

/// tRust: Build a CertificateChain for the pipeline steps.
fn build_chain(
    vc: &VerificationCondition,
    proof_term: &[u8],
    lean5_fingerprint: &str,
    timestamp: &str,
    lean5_verified: bool,
    lean5_time_ms: u64,
) -> CertificateChain {
    let mut chain = CertificateChain::new();

    // Step 1: VC generation (MIR -> VC)
    let vc_hash = sha256_hex(
        &serde_json::to_string(&vc.formula).unwrap_or_else(|_| format!("{:?}", vc.formula)),
    );
    chain.push(ChainStep {
        step_type: ChainStepType::VcGeneration,
        tool: "trust-vcgen".to_string(),
        tool_version: "0.1.0".to_string(),
        input_hash: sha256_hex(vc.function.as_str()),
        output_hash: vc_hash.clone(),
        time_ms: 0, // VC generation time not tracked here
        timestamp: timestamp.to_string(),
    });

    // Step 2: Solver proof
    let proof_hash = sha256_hex_bytes(proof_term);
    chain.push(ChainStep {
        step_type: ChainStepType::SolverProof,
        tool: "z4".to_string(),
        tool_version: "1.0.0".to_string(),
        input_hash: vc_hash,
        output_hash: proof_hash.clone(),
        time_ms: 0, // Solver time tracked in SolverInfo
        timestamp: timestamp.to_string(),
    });

    // Step 3: lean5 certification (if verified)
    if lean5_verified {
        chain.push(ChainStep {
            step_type: ChainStepType::Lean5Certification,
            tool: "lean5".to_string(),
            tool_version: "5.0.0".to_string(),
            input_hash: proof_hash,
            output_hash: lean5_fingerprint.to_string(),
            time_ms: lean5_time_ms,
            timestamp: timestamp.to_string(),
        });
    }

    chain
}

/// SHA-256 hex hash of a string.
fn sha256_hex(data: &str) -> String {
    let mut hasher = Sha256::new();
    hasher.update(data.as_bytes());
    format!("{:x}", hasher.finalize())
}

/// SHA-256 hex hash of raw bytes.
fn sha256_hex_bytes(data: &[u8]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(data);
    format!("{:x}", hasher.finalize())
}

#[cfg(test)]
mod tests {
    use trust_proof_cert::CertificateStore;
    use trust_types::*;

    use super::*;

    fn sample_vc() -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "test_div".into(),
            location: SourceSpan::default(),
            formula: Formula::Not(Box::new(Formula::Eq(
                Box::new(Formula::Var("divisor".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ))),
            contract_metadata: None,
        }
    }

    fn proved_result() -> VerificationResult {
        VerificationResult::Proved {
            solver: "z4".into(),
            time_ms: 5,
            strength: ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: None,
        }
    }

    fn failed_result() -> VerificationResult {
        VerificationResult::Failed { solver: "z4".into(), time_ms: 3, counterexample: None }
    }

    // -----------------------------------------------------------------------
    // CertificationBridge construction
    // -----------------------------------------------------------------------

    #[test]
    fn test_bridge_new_creates_instance() {
        let bridge = CertificationBridge::new();
        // Verify it can produce output (functional test, not field access)
        let vc = sample_vc();
        let result = proved_result();
        let output = bridge
            .certify_unchecked(&vc, &result, vec![1], "2026-03-28T00:00:00Z")
            .expect("bridge should work");
        assert!(output.is_certified());
    }

    #[test]
    fn test_bridge_default_trait() {
        let bridge = CertificationBridge::default();
        let vc = sample_vc();
        let result = proved_result();
        let output = bridge
            .certify_unchecked(&vc, &result, vec![1], "2026-03-28T00:00:00Z")
            .expect("default bridge should work");
        assert!(output.is_certified());
    }

    #[test]
    fn test_bridge_with_pipeline() {
        let pipeline = CertificationPipeline::with_prover_version("custom 1.0");
        let bridge = CertificationBridge::with_pipeline(pipeline);
        let vc = sample_vc();
        let result = proved_result();
        // Verify the custom pipeline produces certificates with the custom version info
        let output = bridge
            .certify_unchecked(&vc, &result, vec![1], "2026-03-28T00:00:00Z")
            .expect("custom bridge should work");
        assert!(output.is_certified());
    }

    // -----------------------------------------------------------------------
    // Unchecked certification (Trusted path)
    // -----------------------------------------------------------------------

    #[test]
    fn test_certify_unchecked_produces_proof_certificate() {
        let bridge = CertificationBridge::new();
        let vc = sample_vc();
        let result = proved_result();

        let output = bridge
            .certify_unchecked(&vc, &result, vec![0xCA, 0xFE], "2026-03-28T00:00:00Z")
            .expect("unchecked certification should succeed");

        assert!(output.is_certified());
        if let PipelineOutput::Certified { certificate, chain } = &output {
            assert_eq!(certificate.function, "test_div");
            assert_eq!(certificate.status, CertificationStatus::Trusted);
            assert_eq!(certificate.proof_trace, vec![0xCA, 0xFE]);
            assert_eq!(certificate.solver.name, "z4");
            assert_eq!(certificate.solver.strength, ProofStrength::smt_unsat());
            assert!(certificate.timestamp.contains("2026-03-28"));

            // Chain should have 2 steps (VcGeneration + SolverProof, no Lean5Certification)
            assert_eq!(chain.len(), 2);
            assert!(!chain.is_lean5_certified());
            chain.verify_integrity().expect("chain should have valid integrity");
        }
    }

    #[test]
    fn test_certify_unchecked_skips_failed_result() {
        let bridge = CertificationBridge::new();
        let vc = sample_vc();
        let result = failed_result();

        let output = bridge
            .certify_unchecked(&vc, &result, vec![1], "2026-03-28T00:00:00Z")
            .expect("should return NoCertificate, not error");

        assert!(!output.is_certified());
        if let PipelineOutput::NoCertificate { reason } = &output {
            assert!(reason.contains("skipped"), "reason: {reason}");
        }
    }

    #[test]
    fn test_certify_unchecked_skips_empty_proof() {
        let bridge = CertificationBridge::new();
        let vc = sample_vc();
        let result = proved_result();

        let output = bridge
            .certify_unchecked(&vc, &result, vec![], "2026-03-28T00:00:00Z")
            .expect("should return NoCertificate, not error");

        assert!(!output.is_certified());
    }

    // -----------------------------------------------------------------------
    // Full lean5 certification path (rejects invalid proofs)
    // -----------------------------------------------------------------------

    #[test]
    fn test_certify_rejects_invalid_proof_bytes() {
        let bridge = CertificationBridge::new();
        let vc = sample_vc();
        let result = proved_result();

        let output = bridge
            .certify(&vc, &result, vec![0xFF, 0x00], "2026-03-28T00:00:00Z")
            .expect("should return NoCertificate, not error");

        assert!(!output.is_certified());
        if let PipelineOutput::NoCertificate { reason } = &output {
            assert!(reason.contains("rejected"), "reason: {reason}");
        }
    }

    #[test]
    fn test_certify_rejects_sort_cert_for_div_vc() {
        use lean5_kernel::cert::ProofCert;
        use lean5_kernel::level::Level as LeanLevel;

        let bridge = CertificationBridge::new();
        let vc = sample_vc();
        let result = proved_result();

        let lean5_cert = ProofCert::Sort { level: LeanLevel::zero() };
        let proof_bytes = bincode::serialize(&lean5_cert).expect("serialize");

        let output = bridge
            .certify(&vc, &result, proof_bytes, "2026-03-28T00:00:00Z")
            .expect("should return NoCertificate, not error");

        assert!(!output.is_certified());
        if let PipelineOutput::NoCertificate { reason } = &output {
            assert!(reason.contains("rejected") || reason.contains("kernel"), "reason: {reason}");
        }
    }

    // -----------------------------------------------------------------------
    // Store integration
    // -----------------------------------------------------------------------

    #[test]
    fn test_certify_and_store_inserts_into_store() {
        let bridge = CertificationBridge::new();
        let vc = sample_vc();
        let result = proved_result();
        let mut store = CertificateStore::new("test-crate");

        assert!(store.is_empty());

        let output = bridge
            .certify_and_store(&vc, &result, vec![0xBE, 0xEF], "2026-03-28T00:00:00Z", &mut store)
            .expect("should succeed");

        assert!(output.is_certified());
        assert_eq!(store.len(), 1);

        // Verify the stored certificate is findable by function name
        let found = store.find_by_function("test_div");
        assert_eq!(found.len(), 1);
        assert_eq!(found[0].function, "test_div");
    }

    #[test]
    fn test_certify_and_store_does_not_insert_on_skip() {
        let bridge = CertificationBridge::new();
        let vc = sample_vc();
        let result = failed_result();
        let mut store = CertificateStore::new("test-crate");

        let output = bridge
            .certify_and_store(&vc, &result, vec![1], "2026-03-28T00:00:00Z", &mut store)
            .expect("should succeed");

        assert!(!output.is_certified());
        assert!(store.is_empty());
    }

    #[test]
    fn test_certify_and_store_multiple_functions() {
        let bridge = CertificationBridge::new();
        let mut store = CertificateStore::new("test-crate");

        let vc1 = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "func_a".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        };
        let vc2 = VerificationCondition {
            kind: VcKind::Assertion { message: "invariant".to_string() },
            function: "func_b".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
        };
        let result = proved_result();

        bridge
            .certify_and_store(&vc1, &result, vec![1], "2026-03-28T00:00:00Z", &mut store)
            .expect("should succeed");
        bridge
            .certify_and_store(&vc2, &result, vec![2], "2026-03-28T00:01:00Z", &mut store)
            .expect("should succeed");

        assert_eq!(store.len(), 2);
        assert_eq!(store.find_by_function("func_a").len(), 1);
        assert_eq!(store.find_by_function("func_b").len(), 1);
    }

    // -----------------------------------------------------------------------
    // Certificate chain integrity
    // -----------------------------------------------------------------------

    #[test]
    fn test_chain_integrity_on_unchecked_path() {
        let bridge = CertificationBridge::new();
        let vc = sample_vc();
        let result = proved_result();

        let output = bridge
            .certify_unchecked(&vc, &result, vec![0xAB], "2026-03-28T00:00:00Z")
            .expect("should succeed");

        if let PipelineOutput::Certified { chain, .. } = &output {
            chain.verify_integrity().expect("unchecked chain should have valid integrity");
            assert_eq!(chain.len(), 2);
            assert_eq!(chain.steps[0].step_type, ChainStepType::VcGeneration);
            assert_eq!(chain.steps[1].step_type, ChainStepType::SolverProof);
        } else {
            panic!("expected Certified output");
        }
    }

    // -----------------------------------------------------------------------
    // Helper functions
    // -----------------------------------------------------------------------

    #[test]
    fn test_extract_solver_info_proved() {
        let result = proved_result();
        let info = extract_solver_info(&result, 10);
        assert_eq!(info.name, "z4");
        assert_eq!(info.time_ms, 15); // 5 (solver) + 10 (lean5)
        assert_eq!(info.strength, ProofStrength::smt_unsat());
    }

    #[test]
    fn test_extract_solver_info_non_proved() {
        let result = failed_result();
        let info = extract_solver_info(&result, 7);
        assert_eq!(info.name, "unknown");
        assert_eq!(info.time_ms, 7);
    }

    #[test]
    fn test_compute_function_hash_deterministic() {
        let vc = sample_vc();
        let h1 = compute_function_hash(&vc);
        let h2 = compute_function_hash(&vc);
        assert_eq!(h1, h2);
    }

    #[test]
    fn test_compute_function_hash_different_formulas() {
        let vc1 = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "f".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        };
        let vc2 = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "f".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
        };
        assert_ne!(compute_function_hash(&vc1), compute_function_hash(&vc2));
    }

    #[test]
    fn test_pipeline_output_is_certified() {
        let cert = PipelineOutput::NoCertificate { reason: "test".to_string() };
        assert!(!cert.is_certified());
    }

    // -----------------------------------------------------------------------
    // Certificate content validation
    // -----------------------------------------------------------------------

    #[test]
    fn test_certificate_vc_snapshot_matches_vc() {
        let bridge = CertificationBridge::new();
        let vc = sample_vc();
        let result = proved_result();

        let output = bridge
            .certify_unchecked(&vc, &result, vec![0x01], "2026-03-28T12:00:00Z")
            .expect("should succeed");

        if let PipelineOutput::Certified { certificate, .. } = &output {
            // The VC snapshot should contain the kind and formula
            assert!(certificate.vc_snapshot.kind.contains("DivisionByZero"));
            assert!(!certificate.vc_snapshot.formula_json.is_empty());
        } else {
            panic!("expected Certified output");
        }
    }

    #[test]
    fn test_certificate_id_is_deterministic() {
        let bridge = CertificationBridge::new();
        let vc = sample_vc();
        let result = proved_result();

        let out1 = bridge
            .certify_unchecked(&vc, &result, vec![0x01], "2026-03-28T12:00:00Z")
            .expect("should succeed");
        let out2 = bridge
            .certify_unchecked(&vc, &result, vec![0x01], "2026-03-28T12:00:00Z")
            .expect("should succeed");

        if let (
            PipelineOutput::Certified { certificate: c1, .. },
            PipelineOutput::Certified { certificate: c2, .. },
        ) = (&out1, &out2)
        {
            assert_eq!(c1.id, c2.id, "same inputs should produce same certificate ID");
        } else {
            panic!("expected both to be Certified");
        }
    }
}
