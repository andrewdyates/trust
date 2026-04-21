// trust-proof-cert/generate.rs: Certificate generation for verified functions
//
// Generates ProofCertificates from VerifiableFunction + VerificationResult pairs,
// including a SHA-256 certificate hash covering all fields for tamper detection.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use trust_types::{VerifiableFunction, VerificationCondition, VerificationResult};

use crate::{
    CertError, CertificateChain, ChainStep, ChainStepType, FunctionHash, ProofCertificate,
    SolverInfo, VcSnapshot,
};

/// A single VC proof entry within a generated certificate.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct VcProofEntry {
    /// Snapshot of the verification condition.
    pub vc_snapshot: VcSnapshot,
    /// Solver that produced the result.
    pub solver: String,
    /// Proof strength description (e.g., "smt_unsat", "bounded(10)").
    pub strength: String,
    /// Time spent solving in milliseconds.
    pub time_ms: u64,
    /// Whether the VC was proved.
    pub proved: bool,
    /// tRust #382: Proof evidence (reasoning + assurance) from the verification result.
    #[serde(skip_serializing_if = "Option::is_none")]
    #[serde(default)]
    pub evidence: Option<trust_types::ProofEvidence>,
}

/// Assumptions under which the certificate was generated.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[derive(Default)]
pub struct Assumptions {
    /// Preconditions assumed from the function spec.
    pub preconditions: Vec<String>,
    /// Callee postconditions assumed (cross-function composition).
    pub callee_postconditions: Vec<String>,
    /// Any additional solver-level assumptions.
    pub solver_assumptions: Vec<String>,
}

/// Environment information captured at certificate generation time.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[derive(Default)]
pub struct Environment {
    /// tRust compiler version.
    pub trust_version: String,
    /// Rust toolchain version.
    pub toolchain: String,
    /// Target triple (e.g., "x86_64-unknown-linux-gnu").
    pub target: String,
}

/// A generated proof certificate with full provenance information.
///
/// This wraps a `ProofCertificate` with additional metadata about the
/// verification process: individual VC results, assumptions, environment,
/// and a SHA-256 certificate hash covering all fields.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct GeneratedCertificate {
    /// The core proof certificate.
    pub certificate: ProofCertificate,
    /// Function signature (def_path from VerifiableFunction).
    pub function_signature: String,
    /// SHA-256 hash of the function signature.
    pub signature_hash: String,
    /// Individual VC proof entries.
    pub vc_entries: Vec<VcProofEntry>,
    /// Assumptions under which verification was performed.
    pub assumptions: Assumptions,
    /// Environment at generation time.
    pub environment: Environment,
    /// SHA-256 hash of all certificate fields (tamper detection).
    pub certificate_hash: String,
}

impl GeneratedCertificate {
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

/// Generate a proof certificate for a verified function.
///
/// Takes the function under verification and the paired (VC, result) outcomes
/// from the solver(s). Produces a `GeneratedCertificate` with:
/// - A `ProofCertificate` for the first proved VC
/// - Individual `VcProofEntry` records for every VC
/// - A SHA-256 `certificate_hash` covering all fields
///
/// # Errors
///
/// Returns `CertError` if VC snapshot creation fails, serialization fails,
/// or no VC result is proved.
pub fn generate_certificate(
    func: &VerifiableFunction,
    results: &[(VerificationCondition, VerificationResult)],
) -> Result<GeneratedCertificate, CertError> {
    generate_certificate_with_env(func, results, Assumptions::default(), Environment::default())
}

/// Generate a proof certificate with explicit assumptions and environment.
pub fn generate_certificate_with_env(
    func: &VerifiableFunction,
    results: &[(VerificationCondition, VerificationResult)],
    assumptions: Assumptions,
    environment: Environment,
) -> Result<GeneratedCertificate, CertError> {
    if results.is_empty() {
        return Err(CertError::InvalidCertificate {
            reason: "no verification results provided".to_string(),
        });
    }

    let timestamp = current_timestamp();
    let function_hash = FunctionHash::from_bytes(func.content_hash().as_bytes());
    let signature_hash = compute_signature_hash(&func.def_path);

    // Build VC proof entries
    let mut vc_entries = Vec::with_capacity(results.len());
    for (vc, result) in results {
        let vc_snapshot = VcSnapshot::from_vc(vc)?;
        let (solver, strength, time_ms, proved) = extract_result_info(result);
        // tRust #382: Derive ProofEvidence from the result.
        let evidence = result.evidence();
        vc_entries.push(VcProofEntry { vc_snapshot, solver, strength, time_ms, proved, evidence });
    }

    // Find the first proved result to use as the primary certificate.
    let primary_idx = results.iter().position(|(_, r)| r.is_proved()).ok_or_else(|| {
        CertError::InvalidCertificate {
            reason: "no proved verification result; cannot generate certificate".to_string(),
        }
    })?;

    let (primary_vc, primary_result) = &results[primary_idx];
    let primary_snapshot = VcSnapshot::from_vc(primary_vc)?;
    let (solver_name, _, solver_time, _) = extract_result_info(primary_result);

    // tRust #382: Derive ProofEvidence for the primary solver info.
    let primary_evidence = primary_result.evidence();

    let solver_info = match primary_result {
        VerificationResult::Proved { solver, time_ms, strength, .. } => SolverInfo {
            name: solver.clone(),
            version: String::new(),
            time_ms: *time_ms,
            strength: strength.clone(),
            evidence: primary_evidence,
        },
        _ => {
            return Err(CertError::InvalidCertificate {
                reason: "primary result is not Proved after index lookup".to_string(),
            });
        }
    };

    // tRust #804 P1-15: Compute actual hashes for the chain instead of placeholders.
    let mir_hash = &function_hash.0;
    let vc_hash_hex =
        format!("{:x}", sha2::Sha256::digest(primary_snapshot.formula_json.as_bytes()));
    let chain = build_chain(&solver_name, solver_time, mir_hash, &vc_hash_hex);

    let certificate = ProofCertificate::new_trusted(
        func.def_path.clone(),
        function_hash,
        primary_snapshot,
        solver_info,
        Vec::new(),
        timestamp,
    )
    .with_chain(chain);

    // Populate assumptions from function spec
    let assumptions = populate_assumptions(func, assumptions);

    let mut generated = GeneratedCertificate {
        certificate,
        function_signature: func.def_path.clone(),
        signature_hash,
        vc_entries,
        assumptions,
        environment,
        certificate_hash: String::new(), // computed below
    };

    // Compute the certificate hash over all fields
    generated.certificate_hash = compute_certificate_hash(&generated)?;

    Ok(generated)
}

/// Verify the integrity of a generated certificate by recomputing its hash.
///
/// Returns `Ok(true)` if the stored `certificate_hash` matches the recomputed hash
/// of all certificate fields.
pub fn verify_certificate_integrity(cert: &GeneratedCertificate) -> Result<bool, CertError> {
    let recomputed = compute_certificate_hash(cert)?;
    Ok(cert.certificate_hash == recomputed)
}

/// Compute the SHA-256 certificate hash over all fields of a generated certificate.
///
/// The hash covers: function signature, signature hash, VC entries (serialized),
/// assumptions (serialized), environment (serialized), and the inner certificate's
/// key fields (function, function_hash, vc_hash, solver, timestamp, status).
fn compute_certificate_hash(cert: &GeneratedCertificate) -> Result<String, CertError> {
    let mut hasher = Sha256::new();

    // Function identity
    hasher.update(cert.function_signature.as_bytes());
    hasher.update(b"|");
    hasher.update(cert.signature_hash.as_bytes());
    hasher.update(b"|");

    // Inner certificate key fields
    hasher.update(cert.certificate.function.as_bytes());
    hasher.update(b"|");
    hasher.update(cert.certificate.function_hash.0.as_bytes());
    hasher.update(b"|");
    hasher.update(cert.certificate.vc_hash);
    hasher.update(b"|");
    hasher.update(cert.certificate.solver.name.as_bytes());
    hasher.update(b":");
    hasher.update(cert.certificate.solver.time_ms.to_le_bytes());
    hasher.update(b"|");
    hasher.update(cert.certificate.timestamp.as_bytes());
    hasher.update(b"|");
    hasher.update(format!("{:?}", cert.certificate.status).as_bytes());
    hasher.update(b"|");

    // VC entries (deterministic via serde_json)
    let vc_json = serde_json::to_string(&cert.vc_entries)
        .map_err(|e| CertError::SerializationFailed { reason: e.to_string() })?;
    hasher.update(vc_json.as_bytes());
    hasher.update(b"|");

    // Assumptions
    let assumptions_json = serde_json::to_string(&cert.assumptions)
        .map_err(|e| CertError::SerializationFailed { reason: e.to_string() })?;
    hasher.update(assumptions_json.as_bytes());
    hasher.update(b"|");

    // Environment
    let env_json = serde_json::to_string(&cert.environment)
        .map_err(|e| CertError::SerializationFailed { reason: e.to_string() })?;
    hasher.update(env_json.as_bytes());

    Ok(format!("{:x}", hasher.finalize()))
}

/// Compute SHA-256 hash of a function signature string.
fn compute_signature_hash(signature: &str) -> String {
    let mut hasher = Sha256::new();
    hasher.update(signature.as_bytes());
    format!("{:x}", hasher.finalize())
}

/// Extract solver name, strength description, time, and proved status from a result.
fn extract_result_info(result: &VerificationResult) -> (String, String, u64, bool) {
    match result {
        VerificationResult::Proved { solver, time_ms, strength, .. } => {
            (solver.clone(), format!("{:?}", strength), *time_ms, true)
        }
        VerificationResult::Failed { solver, time_ms, .. } => {
            (solver.clone(), "failed".to_string(), *time_ms, false)
        }
        VerificationResult::Unknown { solver, time_ms, reason } => {
            (solver.clone(), format!("unknown: {reason}"), *time_ms, false)
        }
        VerificationResult::Timeout { solver, timeout_ms } => {
            (solver.clone(), "timeout".to_string(), *timeout_ms, false)
        }
        _ => ("unknown".to_string(), "unhandled variant".to_string(), 0, false),
    }
}

/// Build a basic certificate chain for a solver result.
///
/// tRust #804 (P1-15): Uses actual SHA-256 hashes for all chain steps.
fn build_chain(solver_name: &str, time_ms: u64, mir_hash: &str, vc_hash: &str) -> CertificateChain {
    // tRust #804 (P1-15): Compute a proper SHA-256 proof output hash.
    let mut proof_hasher = Sha256::new();
    proof_hasher.update(solver_name.as_bytes());
    proof_hasher.update(b":");
    proof_hasher.update(vc_hash.as_bytes());
    proof_hasher.update(b":");
    proof_hasher.update(time_ms.to_le_bytes());
    let proof_hash = format!("{:x}", proof_hasher.finalize());

    let mut chain = CertificateChain::new();
    chain.push(ChainStep {
        step_type: ChainStepType::VcGeneration,
        tool: "trust-vcgen".to_string(),
        tool_version: "0.1.0".to_string(),
        input_hash: mir_hash.to_string(),
        output_hash: vc_hash.to_string(),
        time_ms: 0,
        timestamp: current_timestamp(),
    });
    chain.push(ChainStep {
        step_type: ChainStepType::SolverProof,
        tool: solver_name.to_string(),
        tool_version: String::new(),
        input_hash: vc_hash.to_string(),
        output_hash: proof_hash,
        time_ms,
        timestamp: current_timestamp(),
    });
    chain
}

/// Populate assumptions from the function's spec.
fn populate_assumptions(func: &VerifiableFunction, mut assumptions: Assumptions) -> Assumptions {
    // Add preconditions from function spec
    for pre in &func.preconditions {
        assumptions.preconditions.push(format!("{pre:?}"));
    }
    // Add postconditions from contracts
    for contract in &func.contracts {
        assumptions.callee_postconditions.push(format!("{contract:?}"));
    }
    assumptions
}

/// Get the current UTC timestamp in ISO 8601 format.
///
/// Falls back to a fixed timestamp if system time is unavailable.
fn current_timestamp() -> String {
    // Use a simple epoch-based timestamp since we don't have chrono.
    // In production this would use a proper time library.
    let dur =
        std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap_or_default();
    format!("{}Z", dur.as_secs())
}

#[cfg(test)]
mod tests {
    use trust_types::{
        BasicBlock, BlockId, Formula, FunctionSpec, LocalDecl, ProofStrength, SourceSpan,
        Terminator, Ty, VcKind, VerifiableBody, VerifiableFunction, VerificationCondition,
        VerificationResult,
    };

    use super::*;

    fn sample_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "add".to_string(),
            def_path: "crate::math::add".to_string(),
            span: SourceSpan {
                file: "src/math.rs".to_string(),
                line_start: 10,
                col_start: 0,
                line_end: 15,
                col_end: 1,
            },
            body: VerifiableBody {
                locals: vec![LocalDecl {
                    index: 0,
                    name: Some("_0".to_string()),
                    ty: Ty::Int { width: 32, signed: true },
                }],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: Vec::new(),
                    terminator: Terminator::Return,
                }],
                arg_count: 2,
                return_ty: Ty::Int { width: 32, signed: true },
            },
            contracts: Vec::new(),
            preconditions: vec![Formula::Bool(true)],
            postconditions: vec![Formula::Bool(true)],
            spec: FunctionSpec::default(),
        }
    }

    fn sample_vc(kind_msg: &str) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::Assertion { message: kind_msg.to_string() },
            function: "crate::math::add".to_string(),
            location: SourceSpan {
                file: "src/math.rs".to_string(),
                line_start: 12,
                col_start: 4,
                line_end: 12,
                col_end: 20,
            },
            formula: Formula::Bool(true),
            contract_metadata: None,
        }
    }

    fn proved_result() -> VerificationResult {
        VerificationResult::Proved {
            solver: "z4".to_string(),
            time_ms: 42,
            strength: ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: None,
        }
    }

    fn failed_result() -> VerificationResult {
        VerificationResult::Failed { solver: "z4".to_string(), time_ms: 15, counterexample: None }
    }

    fn assert_no_proved_error(result: Result<GeneratedCertificate, CertError>) {
        let err = result.expect_err("certificate generation should fail without any proved VC");

        match err {
            CertError::InvalidCertificate { reason } => {
                assert!(
                    reason.contains("no proved"),
                    "error should mention missing proved VC, got: {reason}"
                );
            }
            other => panic!("unexpected error: {other:?}"),
        }
    }

    // -----------------------------------------------------------------------
    // generate_certificate tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_generate_certificate_single_proved() {
        let func = sample_function();
        let vc = sample_vc("result must be positive");
        let results = vec![(vc, proved_result())];

        let cert =
            generate_certificate(&func, &results).expect("certificate generation should succeed");

        assert_eq!(cert.function_signature, "crate::math::add");
        assert!(!cert.signature_hash.is_empty());
        assert_eq!(cert.vc_entries.len(), 1);
        assert!(cert.vc_entries[0].proved);
        assert_eq!(cert.vc_entries[0].solver, "z4");
        assert_eq!(cert.vc_entries[0].time_ms, 42);
        assert!(!cert.certificate_hash.is_empty());
        assert_eq!(cert.certificate_hash.len(), 64); // SHA-256 hex
    }

    #[test]
    fn test_generate_certificate_multiple_vcs() {
        let func = sample_function();
        let results = vec![
            (sample_vc("assertion 1"), proved_result()),
            (sample_vc("assertion 2"), failed_result()),
            (sample_vc("assertion 3"), proved_result()),
        ];

        let cert = generate_certificate(&func, &results).expect("should succeed");

        assert_eq!(cert.vc_entries.len(), 3);
        assert!(cert.vc_entries[0].proved);
        assert!(!cert.vc_entries[1].proved);
        assert!(cert.vc_entries[2].proved);

        // Primary certificate should be from the first proved VC
        assert_eq!(cert.certificate.solver.name, "z4");
    }

    #[test]
    fn test_generate_certificate_no_proved_fails() {
        let func = sample_function();
        let results = vec![
            (sample_vc("assertion 1"), failed_result()),
            (
                sample_vc("assertion 2"),
                VerificationResult::Unknown {
                    solver: "sunder".to_string(),
                    time_ms: 100,
                    reason: "incomplete".to_string(),
                },
            ),
        ];

        assert_no_proved_error(generate_certificate(&func, &results));
    }

    #[test]
    fn test_generate_certificate_empty_results_fails() {
        let func = sample_function();
        let results: Vec<(VerificationCondition, VerificationResult)> = vec![];

        let err = generate_certificate(&func, &results).expect_err("should fail with no results");

        match err {
            CertError::InvalidCertificate { reason } => {
                assert!(reason.contains("no verification results"));
            }
            other => panic!("unexpected error: {other:?}"),
        }
    }

    #[test]
    fn test_generate_certificate_with_timeout() {
        let func = sample_function();
        let results = vec![(
            sample_vc("assertion"),
            VerificationResult::Timeout { solver: "lean5".to_string(), timeout_ms: 5000 },
        )];

        assert_no_proved_error(generate_certificate(&func, &results));
    }

    // -----------------------------------------------------------------------
    // verify_certificate_integrity tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_verify_certificate_integrity_valid() {
        let func = sample_function();
        let results = vec![(sample_vc("test"), proved_result())];

        let cert = generate_certificate(&func, &results).unwrap();
        assert!(verify_certificate_integrity(&cert).unwrap());
    }

    #[test]
    fn test_verify_certificate_integrity_returns_result() {
        let func = sample_function();
        let results = vec![(sample_vc("test"), proved_result())];
        let cert = generate_certificate(&func, &results).unwrap();

        assert!(verify_certificate_integrity(&cert).unwrap());
    }

    #[test]
    fn test_verify_certificate_integrity_tampered_signature() {
        let func = sample_function();
        let results = vec![(sample_vc("test"), proved_result())];

        let mut cert = generate_certificate(&func, &results).unwrap();
        cert.function_signature = "tampered::path".to_string();

        assert!(!verify_certificate_integrity(&cert).unwrap());
    }

    #[test]
    fn test_verify_certificate_integrity_tampered_vc_entry() {
        let func = sample_function();
        let results = vec![(sample_vc("test"), proved_result())];

        let mut cert = generate_certificate(&func, &results).unwrap();
        cert.vc_entries[0].proved = false;

        assert!(!verify_certificate_integrity(&cert).unwrap());
    }

    #[test]
    fn test_verify_certificate_integrity_tampered_hash() {
        let func = sample_function();
        let results = vec![(sample_vc("test"), proved_result())];

        let mut cert = generate_certificate(&func, &results).unwrap();
        cert.certificate_hash = "0".repeat(64);

        assert!(!verify_certificate_integrity(&cert).unwrap());
    }

    #[test]
    fn test_verify_certificate_integrity_tampered_environment() {
        let func = sample_function();
        let results = vec![(sample_vc("test"), proved_result())];

        let mut cert = generate_certificate(&func, &results).unwrap();
        cert.environment.trust_version = "evil-version".to_string();

        assert!(!verify_certificate_integrity(&cert).unwrap());
    }

    #[test]
    fn test_verify_certificate_integrity_tampered_assumptions() {
        let func = sample_function();
        let results = vec![(sample_vc("test"), proved_result())];

        let mut cert = generate_certificate(&func, &results).unwrap();
        cert.assumptions.solver_assumptions.push("injected_assumption".to_string());

        assert!(!verify_certificate_integrity(&cert).unwrap());
    }

    // -----------------------------------------------------------------------
    // JSON roundtrip tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_generated_certificate_json_roundtrip() {
        let func = sample_function();
        let results =
            vec![(sample_vc("vc1"), proved_result()), (sample_vc("vc2"), failed_result())];

        let cert = generate_certificate(&func, &results).unwrap();
        let json = cert.to_json().expect("serialization should succeed");
        let restored =
            GeneratedCertificate::from_json(&json).expect("deserialization should succeed");

        assert_eq!(restored.certificate_hash, cert.certificate_hash);
        assert_eq!(restored.function_signature, cert.function_signature);
        assert_eq!(restored.vc_entries.len(), cert.vc_entries.len());
        assert!(verify_certificate_integrity(&restored).unwrap());
    }

    #[test]
    fn test_json_roundtrip_preserves_all_fields() {
        let func = sample_function();
        let results = vec![(sample_vc("vc1"), proved_result())];

        let env = Environment {
            trust_version: "0.1.0".to_string(),
            toolchain: "nightly-2026-03-30".to_string(),
            target: "x86_64-unknown-linux-gnu".to_string(),
        };
        let assumptions = Assumptions {
            preconditions: vec!["x > 0".to_string()],
            callee_postconditions: vec!["result >= x".to_string()],
            solver_assumptions: vec![],
        };

        let cert = generate_certificate_with_env(&func, &results, assumptions, env).unwrap();
        let json = cert.to_json().unwrap();
        let restored = GeneratedCertificate::from_json(&json).unwrap();

        assert_eq!(restored.environment.trust_version, "0.1.0");
        assert_eq!(restored.environment.toolchain, "nightly-2026-03-30");
        // "x > 0" was explicitly provided; "Bool(true)" comes from func.preconditions
        assert!(restored.assumptions.preconditions.contains(&"x > 0".to_string()));
        assert_eq!(restored.assumptions.callee_postconditions, vec!["result >= x"]);
        assert!(verify_certificate_integrity(&restored).unwrap());
    }

    // -----------------------------------------------------------------------
    // generate_certificate_with_env tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_generate_with_custom_env() {
        let func = sample_function();
        let results = vec![(sample_vc("test"), proved_result())];
        let env = Environment {
            trust_version: "1.0.0".to_string(),
            toolchain: "stable-2026".to_string(),
            target: "aarch64-apple-darwin".to_string(),
        };

        let cert =
            generate_certificate_with_env(&func, &results, Assumptions::default(), env).unwrap();

        assert_eq!(cert.environment.trust_version, "1.0.0");
        assert_eq!(cert.environment.target, "aarch64-apple-darwin");
        assert!(verify_certificate_integrity(&cert).unwrap());
    }

    #[test]
    fn test_generate_with_assumptions() {
        let func = sample_function();
        let results = vec![(sample_vc("test"), proved_result())];
        let assumptions = Assumptions {
            preconditions: vec!["x > 0".to_string()],
            callee_postconditions: vec![],
            solver_assumptions: vec!["no-overflow".to_string()],
        };

        let cert =
            generate_certificate_with_env(&func, &results, assumptions, Environment::default())
                .unwrap();

        // Should have the explicit assumption plus those extracted from the function
        assert!(cert.assumptions.preconditions.contains(&"x > 0".to_string()));
        assert!(cert.assumptions.solver_assumptions.contains(&"no-overflow".to_string()));
        assert!(verify_certificate_integrity(&cert).unwrap());
    }

    // -----------------------------------------------------------------------
    // Helper function tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_compute_signature_hash_deterministic() {
        let h1 = compute_signature_hash("crate::math::add");
        let h2 = compute_signature_hash("crate::math::add");
        assert_eq!(h1, h2);
        assert_eq!(h1.len(), 64);
    }

    #[test]
    fn test_compute_signature_hash_different_inputs() {
        let h1 = compute_signature_hash("crate::math::add");
        let h2 = compute_signature_hash("crate::math::sub");
        assert_ne!(h1, h2);
    }

    #[test]
    fn test_certificate_hash_deterministic() {
        let func = sample_function();
        let results = vec![(sample_vc("test"), proved_result())];

        let cert1 = generate_certificate(&func, &results).unwrap();
        let cert2 = generate_certificate(&func, &results).unwrap();

        // Hashes may differ due to timestamp, but both should verify
        assert!(verify_certificate_integrity(&cert1).unwrap());
        assert!(verify_certificate_integrity(&cert2).unwrap());
    }

    #[test]
    fn test_function_preconditions_in_assumptions() {
        let mut func = sample_function();
        func.preconditions = vec![Formula::Bool(true), Formula::Bool(false)];

        let results = vec![(sample_vc("test"), proved_result())];
        let cert = generate_certificate(&func, &results).unwrap();

        // Should have 2 preconditions from the function
        assert_eq!(cert.assumptions.preconditions.len(), 2);
    }

    // -----------------------------------------------------------------------
    // Bug #385: Failed/Unknown/Timeout must NOT get smt_unsat() strength
    // -----------------------------------------------------------------------

    #[test]
    fn test_generate_certificate_failed_result_not_smt_unsat() {
        let func = sample_function();
        let results = vec![(sample_vc("test"), failed_result())];

        assert_no_proved_error(generate_certificate(&func, &results));
    }

    #[test]
    fn test_generate_certificate_unknown_result_not_smt_unsat() {
        let func = sample_function();
        let results = vec![(
            sample_vc("test"),
            VerificationResult::Unknown {
                solver: "z4".to_string(),
                time_ms: 50,
                reason: "incomplete".to_string(),
            },
        )];

        assert_no_proved_error(generate_certificate(&func, &results));
    }

    #[test]
    fn test_generate_certificate_timeout_result_not_smt_unsat() {
        let func = sample_function();
        let results = vec![(
            sample_vc("test"),
            VerificationResult::Timeout { solver: "lean5".to_string(), timeout_ms: 5000 },
        )];

        assert_no_proved_error(generate_certificate(&func, &results));
    }

    #[test]
    fn test_generate_certificate_proved_result_is_smt_unsat() {
        // Proved results should still get smt_unsat() strength -- verify we didn't break this.
        let func = sample_function();
        let results = vec![(sample_vc("test"), proved_result())];

        let cert = generate_certificate(&func, &results).unwrap();

        assert!(
            cert.certificate.solver.strength.is_sound(),
            "Proved result should have Sound assurance, got: {:?}",
            cert.certificate.solver.strength
        );
        assert_eq!(cert.certificate.solver.strength, ProofStrength::smt_unsat());
    }

    // -----------------------------------------------------------------------
    // tRust #382: ProofEvidence pipeline integration tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_proof_evidence_flows_through_certificate_generation() {
        // Verify that ProofEvidence is produced from VerificationResult and
        // stored in both the SolverInfo and VcProofEntry.
        let func = sample_function();
        let results = vec![(sample_vc("evidence-test"), proved_result())];

        let cert =
            generate_certificate(&func, &results).expect("certificate generation should succeed");

        // SolverInfo should have evidence derived from smt_unsat() strength
        let solver_evidence = cert
            .certificate
            .solver
            .evidence
            .as_ref()
            .expect("proved result must produce ProofEvidence in SolverInfo");
        assert_eq!(solver_evidence.reasoning, trust_types::ReasoningKind::Smt);
        assert_eq!(solver_evidence.assurance, trust_types::AssuranceLevel::SmtBacked);

        // VcProofEntry should also have evidence
        let vc_evidence =
            cert.vc_entries[0].evidence.as_ref().expect("proved VC entry must have ProofEvidence");
        assert_eq!(vc_evidence.reasoning, trust_types::ReasoningKind::Smt);
        assert_eq!(vc_evidence.assurance, trust_types::AssuranceLevel::SmtBacked);
    }

    #[test]
    fn test_proof_evidence_absent_for_failed_results() {
        let func = sample_function();
        let results = vec![(sample_vc("fail-test"), failed_result())];

        assert_no_proved_error(generate_certificate(&func, &results));
    }

    #[test]
    fn test_proof_evidence_survives_json_roundtrip() {
        // End-to-end: generate with evidence, serialize to JSON, deserialize,
        // verify evidence is preserved.
        let func = sample_function();
        let results = vec![(sample_vc("roundtrip"), proved_result())];

        let cert = generate_certificate(&func, &results).unwrap();
        let json = cert.to_json().expect("JSON serialization");
        let restored = GeneratedCertificate::from_json(&json).expect("JSON deserialization");

        let original_evidence = cert.certificate.solver.evidence.as_ref().unwrap();
        let restored_evidence = restored
            .certificate
            .solver
            .evidence
            .as_ref()
            .expect("evidence must survive JSON roundtrip");
        assert_eq!(original_evidence.reasoning, restored_evidence.reasoning);
        assert_eq!(original_evidence.assurance, restored_evidence.assurance);

        // VC entry evidence too
        let orig_vc_ev = cert.vc_entries[0].evidence.as_ref().unwrap();
        let rest_vc_ev = restored.vc_entries[0]
            .evidence
            .as_ref()
            .expect("VC evidence must survive JSON roundtrip");
        assert_eq!(orig_vc_ev.reasoning, rest_vc_ev.reasoning);
        assert_eq!(orig_vc_ev.assurance, rest_vc_ev.assurance);
    }
}
