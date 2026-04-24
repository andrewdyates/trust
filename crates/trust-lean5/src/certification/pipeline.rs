// trust-lean5/certification/pipeline.rs: CertificationPipeline struct
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{VerificationCondition, VerificationResult};

use crate::certificate::{generate_certificate, generate_certificate_unchecked};
use crate::error::CertificateError;
use crate::logic_classification::{
    CertificationScope, classify_formula, degradation_strategy, scope_from_logic,
};
use crate::reconstruction::{SolverProof, reconstruct};
use crate::{TrustProofCertificate, lean5_bridge};

use super::result::CertificationResult;
use super::result_status_name;

/// tRust: The certification pipeline.
///
/// Takes verification results that are Proved/Trusted and attempts to
/// upgrade them to Certified by running the proof through lean5's kernel.
///
/// The pipeline uses the lean5-kernel library directly (not subprocess).
/// It translates the VC formula to a lean5 theorem expression, then
/// type-checks the proof term against it.
///
/// Supports proof term generation from structured solver proofs for QF_LIA
/// and QF_UF theories (#355). For other theories, callers must provide
/// pre-built lean5 proof term bytes.
pub struct CertificationPipeline {
    /// tRust: Default prover version string for certificates.
    pub(crate) default_prover_version: String,
}

impl CertificationPipeline {
    /// Create a new certification pipeline.
    #[must_use]
    pub fn new() -> Self {
        CertificationPipeline { default_prover_version: "lean5-kernel 0.1.0".to_string() }
    }

    /// Create a pipeline with a custom prover version string.
    #[must_use]
    pub fn with_prover_version(prover_version: &str) -> Self {
        CertificationPipeline { default_prover_version: prover_version.to_string() }
    }

    /// tRust: Attempt to certify a proved verification result.
    ///
    /// Only operates on `Proved` results. Other results return `Skipped`.
    ///
    /// The proof term bytes must be provided separately — the `VerificationResult`
    /// does not carry them (proof terms are heavy and solver-specific).
    ///
    /// # Arguments
    ///
    /// * `vc` - The verification condition that was proved
    /// * `result` - The solver's verification result (must be `Proved`)
    /// * `proof_term` - Serialized lean5 proof term bytes from the solver
    pub fn certify(
        &self,
        vc: &VerificationCondition,
        result: &VerificationResult,
        proof_term: Vec<u8>,
    ) -> CertificationResult {
        // tRust: Only attempt certification for proved results
        let VerificationResult::Proved { solver, strength, .. } = result else {
            return CertificationResult::Skipped {
                reason: format!(
                    "only Proved results can be certified, got {}",
                    result_status_name(result)
                ),
            };
        };

        if proof_term.is_empty() {
            return CertificationResult::Skipped {
                reason: "empty proof term — solver did not produce a lean5 certificate".to_string(),
            };
        }

        let prover_version = self.make_prover_version(solver.as_str(), strength);

        // tRust: Run the full certification pipeline with lean5 kernel validation
        let start = std::time::Instant::now();
        match generate_certificate(vc, result, proof_term, &prover_version) {
            Ok(certificate) => {
                let elapsed_ms = start.elapsed().as_millis() as u64;
                CertificationResult::Certified { certificate, time_ms: elapsed_ms }
            }
            Err(e) => {
                let elapsed_ms = start.elapsed().as_millis() as u64;
                CertificationResult::Rejected { reason: format!("{e}"), time_ms: elapsed_ms }
            }
        }
    }

    /// tRust: Generate an unchecked certificate (Trusted, not Certified).
    ///
    /// Builds the certificate structure and stores the proof term bytes,
    /// but does NOT validate them against the lean5 kernel. Use this when
    /// the proof term comes from a solver that doesn't produce lean5-compatible
    /// certificates (e.g., raw z4 SMT proofs before lean5 translation).
    ///
    /// Certificates generated this way remain `Trusted` (not `Certified`).
    pub fn certify_unchecked(
        &self,
        vc: &VerificationCondition,
        result: &VerificationResult,
        proof_term: Vec<u8>,
    ) -> CertificationResult {
        let VerificationResult::Proved { solver, strength, .. } = result else {
            return CertificationResult::Skipped {
                reason: format!(
                    "only Proved results can be certified, got {}",
                    result_status_name(result)
                ),
            };
        };

        if proof_term.is_empty() {
            return CertificationResult::Skipped { reason: "empty proof term".to_string() };
        }

        let prover_version = self.make_prover_version(solver.as_str(), strength);

        let start = std::time::Instant::now();
        match generate_certificate_unchecked(vc, result, proof_term, &prover_version) {
            Ok(certificate) => {
                let elapsed_ms = start.elapsed().as_millis() as u64;
                // tRust: Unchecked certificates are NOT Certified — they are Trusted.
                // The certificate was NOT lean5-kernel-verified (F2 fix: #758).
                CertificationResult::Trusted { certificate, time_ms: elapsed_ms }
            }
            Err(e) => CertificationResult::Rejected {
                reason: format!("{e}"),
                time_ms: start.elapsed().as_millis() as u64,
            },
        }
    }

    /// tRust: Certify from a structured solver proof (#355).
    ///
    /// Takes a `SolverProof` (structured sequence of inference steps) instead
    /// of raw proof bytes. The pipeline:
    ///
    /// 1. Classifies the VC formula into an SMT logic fragment
    /// 2. Checks if the logic is certifiable (QF_LIA or QF_UF)
    /// 3. Reconstructs a lean5 proof term from the solver proof steps
    /// 4. Serializes the proof term to bytes
    /// 5. Generates an unchecked certificate with the serialized proof
    ///
    /// This method bridges structured solver output to the certificate pipeline
    /// without requiring the solver to produce lean5-native proof terms.
    ///
    /// # Arguments
    ///
    /// * `vc` - The verification condition that was proved
    /// * `result` - The solver's verification result (must be `Proved`)
    /// * `solver_proof` - Structured proof output from the solver
    pub fn certify_from_solver_proof(
        &self,
        vc: &VerificationCondition,
        result: &VerificationResult,
        solver_proof: &SolverProof,
    ) -> CertificationResult {
        let VerificationResult::Proved { solver, strength, .. } = result else {
            return CertificationResult::Skipped {
                reason: format!(
                    "only Proved results can be certified, got {}",
                    result_status_name(result)
                ),
            };
        };

        if solver_proof.steps.is_empty() {
            return CertificationResult::Skipped {
                reason: "solver proof has no steps".to_string(),
            };
        }

        // tRust: Classify the formula and check certifiability (#355)
        let logic = classify_formula(&vc.formula);
        let strategy = degradation_strategy(&logic);

        if strategy.is_none() {
            return CertificationResult::Skipped {
                reason: format!(
                    "logic {} is not certifiable: no certification strategy available",
                    logic.name()
                ),
            };
        }

        // tRust: Reconstruct lean5 proof term from solver proof steps
        let proof_term = match reconstruct(solver_proof, vc) {
            Ok(term) => term,
            Err(e) => {
                return CertificationResult::Rejected {
                    reason: format!("proof reconstruction failed: {e}"),
                    time_ms: 0,
                };
            }
        };

        // tRust #429: Serialize the reconstructed proof term as the certificate payload.
        // Use the lean5 bridge serialization for kernel-compatible bytes.
        let proof_bytes = lean5_bridge::serialize_proof_cert_from_lean_term(&proof_term);

        let prover_version = self.make_prover_version(solver.as_str(), strength);

        // tRust #429: Use kernel-checked path (generate_certificate) instead of
        // generate_certificate_unchecked. This means the lean5 kernel validates
        // the proof term, upgrading the result from Trusted to genuinely Certified.
        // Falls back to unchecked if the kernel rejects the proof term (e.g.,
        // theory lemma steps that the kernel cannot yet verify).
        let start = std::time::Instant::now();
        match generate_certificate(vc, result, proof_bytes.clone(), &prover_version) {
            Ok(certificate) => {
                let elapsed_ms = start.elapsed().as_millis() as u64;
                CertificationResult::Certified { certificate, time_ms: elapsed_ms }
            }
            Err(_kernel_err) => {
                // Fallback: kernel rejected the proof term (likely theory lemma or
                // unsupported construct). Use unchecked path to still produce a
                // Trusted certificate rather than failing entirely (F1 fix: #758).
                match generate_certificate_unchecked(vc, result, proof_bytes, &prover_version) {
                    Ok(certificate) => {
                        let elapsed_ms = start.elapsed().as_millis() as u64;
                        CertificationResult::Trusted { certificate, time_ms: elapsed_ms }
                    }
                    Err(e) => CertificationResult::Rejected {
                        reason: format!("{e}"),
                        time_ms: start.elapsed().as_millis() as u64,
                    },
                }
            }
        }
    }

    /// tRust #199: Certify from a solver proof with graceful degradation.
    ///
    /// Like `certify_from_solver_proof`, but returns both the `CertificationResult`
    /// and the `CertificationScope` describing why certification succeeded, partially
    /// succeeded, or was not possible.
    ///
    /// For supported theories (QF_LIA, QF_UF, QF_LIA+UF), produces full
    /// Alethe-to-lean5 certificates. For unsupported theories, produces an
    /// "uncertified" marker with reasons instead of failing the build.
    ///
    /// # Returns
    ///
    /// `(CertificationResult, CertificationScope)` — the scope tells callers
    /// exactly what level of certification was achieved and why.
    pub fn certify_with_scope(
        &self,
        vc: &VerificationCondition,
        result: &VerificationResult,
        solver_proof: &SolverProof,
    ) -> (CertificationResult, CertificationScope) {
        let VerificationResult::Proved { .. } = result else {
            return (
                CertificationResult::Skipped {
                    reason: format!(
                        "only Proved results can be certified, got {}",
                        result_status_name(result)
                    ),
                },
                CertificationScope::Uncertified { reason: "result is not Proved".to_string() },
            );
        };

        if solver_proof.steps.is_empty() {
            return (
                CertificationResult::Skipped { reason: "solver proof has no steps".to_string() },
                CertificationScope::Uncertified { reason: "solver proof has no steps".to_string() },
            );
        }

        // tRust #199: Classify the formula and determine scope
        let logic = classify_formula(&vc.formula);
        let scope = scope_from_logic(&logic);

        // tRust #199: Graceful degradation — for uncertifiable logics, return
        // the scope information instead of failing the build
        match &scope {
            CertificationScope::FullyCertified => {
                // Fully certifiable: proceed with reconstruction
                let cert_result = self.certify_from_solver_proof(vc, result, solver_proof);
                (cert_result, scope)
            }
            CertificationScope::PartiallyCertified { logic, reason } => {
                // Partially certifiable: attempt reconstruction but tag as partial
                let cert_result = self.certify_from_solver_proof(vc, result, solver_proof);
                // Even if reconstruction succeeds, the scope records what
                // parts could not be certified
                (
                    cert_result,
                    CertificationScope::PartiallyCertified {
                        logic: logic.clone(),
                        reason: reason.clone(),
                    },
                )
            }
            CertificationScope::Uncertified { reason } => {
                // Not certifiable: skip gracefully instead of failing
                (
                    CertificationResult::Skipped {
                        reason: format!(
                            "graceful degradation: logic {} is not certifiable — {}",
                            logic.name(),
                            reason
                        ),
                    },
                    CertificationScope::Uncertified { reason: reason.clone() },
                )
            }
        }
    }

    /// tRust: Verify an existing certificate against a VC.
    ///
    /// Re-checks a previously generated certificate: validates fingerprint
    /// freshness, then runs lean5 kernel type-checking. Returns `Ok(())` if
    /// the certificate is still valid and lean5 confirms it.
    pub fn verify_existing(
        &self,
        vc: &VerificationCondition,
        certificate: &TrustProofCertificate,
    ) -> Result<(), CertificateError> {
        crate::certificate::verify_certificate(vc, certificate)
    }

    /// tRust: Translate a VC's formula to a lean5 theorem expression.
    ///
    /// Useful for debugging: inspect what lean5 sees before certification.
    pub fn translate_to_lean5(vc: &VerificationCondition) -> lean5_kernel::Expr {
        lean5_bridge::translate_vc_to_lean5_theorem(&vc.kind, &vc.formula)
    }

    /// tRust: Build a prover version string from solver info and pipeline config.
    fn make_prover_version(&self, solver: &str, strength: &trust_types::ProofStrength) -> String {
        format!(
            "{solver} via {backend} (strength: {strength:?})",
            backend = self.default_prover_version,
        )
    }
}

impl Default for CertificationPipeline {
    fn default() -> Self {
        Self::new()
    }
}
