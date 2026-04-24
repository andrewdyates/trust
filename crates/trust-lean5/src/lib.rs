// dead_code audit: crate-level suppression removed (#939)
//! trust-lean5: Certificate pipeline for lean5 proof verification
//!
//! Bridges tRust verification conditions to lean5 proof certificates.
//! The certificate chain is: solver -> certificate -> lean5 kernel.
//! If lean5 accepts the certificate, the proof is machine-checked and
//! the result upgrades from Trusted to Certified.
//!
//! Author: Andrew Yates <andrew@andrewdyates.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

pub(crate) mod bundle;
pub(crate) mod canonical;
pub(crate) mod certificate;
pub mod certification;
pub(crate) mod composition_transfer;
pub mod error;
pub(crate) mod fingerprint;
pub mod integration;
pub(crate) mod kernel_check;
pub mod lean5_bridge;
pub(crate) mod logic_classification;
pub(crate) mod obligation;
pub(crate) mod proof_transfer;
// tRust #611: Bridge composition DAG to lean5 proof transfer (similarity search)
pub(crate) mod reconstruction;
pub(crate) mod replay;
pub(crate) mod tactic_gen;
pub(crate) mod tactics;
pub(crate) mod transfer_bridge;
pub(crate) mod v1_reuse;
pub(crate) mod z4_proof_bridge;

#[cfg(test)]
mod e2e_tests;

pub use bundle::{
    TRUST_CERT_BUNDLE_FORMAT_VERSION, TrustProofCertificateBundle,
    TrustProofCertificateBundleMetadata, deserialize_certificate_bundle, read_certificate_bundle,
    serialize_certificate_bundle, write_certificate_bundle,
};
pub use canonical::canonical_vc_bytes;
pub use certificate::{
    TrustProofCertificate, generate_certificate, generate_certificate_unchecked, verify_certificate,
};
// tRust: Certification pipeline — post-verification lean5 kernel certification
// tRust #355: Enhanced with proof term generation for QF_LIA and QF_UF theories
// tRust #199: Added classify_vc_scope for scope-aware certification
pub use certification::{
    CertificationPipeline, CertificationResult, ProofGeneration, ProofTheory,
    classify_vc_for_certification, classify_vc_scope, generate_proof_term, qf_lia_axiom,
    qf_uf_axiom,
};
// tRust: Logic classification for Alethe→lean5 certification scoping (#199)
pub use logic_classification::{
    CertificationScope, CertificationStrategy, SmtLogic, TheoryClassifier, classify_formula,
    degradation_strategy, is_certifiable, scope_from_logic,
};
// tRust: Integration bridge — connects lean5 pipeline to trust-proof-cert
pub use error::CertificateError;
pub use fingerprint::{Fingerprint, compute_vc_fingerprint};
pub use integration::{CertificationBridge, PipelineOutput};
pub use lean5_bridge::{
    deserialize_proof_cert, serialize_proof_cert, translate_formula, translate_vc_to_lean5_theorem,
    verify_proof_cert,
};
// tRust: Proof reconstruction from solver certificates
pub use reconstruction::{
    LeanProofTerm, ProofReconstructor, ProofStep, ReconstructionError, SolverProof, reconstruct,
    validate_reconstruction,
};
// tRust: Automated tactic generation from VC structure (#279)
pub use tactic_gen::{
    Difficulty, TacticHint, TacticSequence, estimate_difficulty, format_lean5_proof,
    generate_tactics, tactic_for_arithmetic, tactic_for_induction,
};
// tRust: Tactic script generation for lean5 proofs
pub use tactics::{
    Tactic, TacticScript, arithmetic_strategy, case_split_strategy, compose_tactics,
    generate_tactic_script, induction_strategy,
};
// tRust: Proof replay engine for verifying proof certificates
pub use replay::{
    FailureDiagnosis, ProofContext, ProofReplayer, ReplayCertificate, ReplayCheckpoint,
    ReplayDiagnostics, ReplayResult, ReplayRule, ReplayStep, SuggestedFix,
    certificate_from_proof_term, checkpoint_replay, diagnose_failure, suggest_fix,
};
// tRust: Proof transfer between lemmas (#309)
pub use proof_transfer::{
    Adaptation, LemmaSignature, TransferCandidate, TransferResult, adapt_proof, find_transferable,
    similarity_score,
};
// tRust: Lean5 proof transfer integration with composition DAG (#611)
pub use composition_transfer::{
    Lean5ProofTransfer, ProofStatus, ProofStatusRegistry, TransferObligation,
};
// tRust #611: Similarity-based proof transfer search over composition DAG
pub use transfer_bridge::{
    AdaptedObligation, TransferProvenance, apply_transfer, build_transfer_provenance,
    cert_to_lemma_signature, find_transfer_candidates, find_transfer_candidates_from_certs,
};
// tRust: Proof obligation management
pub use obligation::{
    ObligationId, ObligationSet, ObligationSource, ObligationStatus, ProofObligation,
    split_obligation,
};
// tRust: Lean5 kernel proof checking interface (#328)
pub use kernel_check::{
    ContextEntry, KernelContext, KernelQuery, KernelResult, ProofTerm, check_proof, infer_type,
    is_definitionally_equal, substitute,
};
// tRust: Z4 proof bridge — translates z4 proof certificates to SolverProof (#429)
pub use z4_proof_bridge::translate_z4_proof;
// tRust: v1 lean5 proof reuse — indexes and matches v1 theorems (#450)
pub use v1_reuse::{LoweringError, TheoremCategory, TheoremLibrary, V1Theorem, lower_proof_term};
