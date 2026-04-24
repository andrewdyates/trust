// trust-lean5/certification/mod.rs: Post-verification certification via lean5 kernel
//
// The certification pipeline is a post-processing step that takes Proved
// verification results (Trusted status) and attempts to upgrade them to
// Certified by running the proof through lean5's kernel type-checker.
//
// Flow: z4 proves -> lean5 certifies -> Certified status
//
// Supports proof term generation from structured solver proofs for:
// - QF_LIA (quantifier-free linear integer arithmetic)
// - QF_UF (quantifier-free uninterpreted functions / equality logic)
//
// Only Certified results can later enable codegen check elision. This keeps
// the compiler TCB minimal: rustc + lean5 kernel.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

mod generation;
mod pipeline;
mod result;
mod types;

#[cfg(test)]
mod tests;

use trust_types::VerificationResult;

// Re-export public API
pub use generation::{
    classify_vc_for_certification, classify_vc_scope, generate_proof_term, qf_lia_axiom,
    qf_uf_axiom,
};
pub use pipeline::CertificationPipeline;
pub use result::CertificationResult;
pub use types::{ProofGeneration, ProofTheory};

// Re-export types used by tests (visible within the crate)
#[allow(unused_imports)]
pub(crate) use crate::error::CertificateError;
#[allow(unused_imports)]
pub(crate) use crate::logic_classification::{CertificationScope, SmtLogic};
#[allow(unused_imports)]
pub(crate) use crate::reconstruction::{LeanProofTerm, ProofStep, SolverProof};

/// tRust: Helper to get a human-readable name for a verification result status.
fn result_status_name(result: &VerificationResult) -> &'static str {
    match result {
        VerificationResult::Proved { .. } => "Proved",
        VerificationResult::Failed { .. } => "Failed",
        VerificationResult::Unknown { .. } => "Unknown",
        VerificationResult::Timeout { .. } => "Timeout",
        _ => "unknown",
    }
}
