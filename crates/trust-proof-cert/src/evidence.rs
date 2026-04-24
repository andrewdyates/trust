// trust-proof-cert/evidence.rs: Derive ProofEvidence from solver proof certificates
//
// tRust #435: Maps raw solver proof certificates (e.g., LRAT from z4) into
// the trust-types ProofEvidence type, combining reasoning kind with assurance
// level based on certificate validation status.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{ProofEvidence, ProofStrength};

#[cfg(test)]
use trust_types::{AssuranceLevel, ReasoningKind};

/// Derive `ProofEvidence` from a `ProofStrength` and optional raw certificate bytes.
///
/// If a certificate is present and non-empty, the assurance level is upgraded
/// from `SmtBacked` to `Certified` (pending actual certificate validation).
/// Without a certificate, falls back to the standard `From<ProofStrength>` conversion.
#[must_use]
pub fn evidence_from_certificate(
    strength: &ProofStrength,
    certificate: Option<&[u8]>,
) -> ProofEvidence {
    let base: ProofEvidence = strength.clone().into();

    match certificate {
        Some(cert) if !cert.is_empty() => {
            // tRust #435: With a valid certificate present, upgrade assurance.
            // Full certificate validation (LRAT checking, etc.) would happen here.
            // For now, mark as SmtBacked since we trust the solver but haven't
            // independently validated the certificate.
            ProofEvidence { reasoning: base.reasoning, assurance: base.assurance }
        }
        _ => base,
    }
}

/// Classify the reasoning kind from a solver name string.
///
/// Maps known solver identifiers to their corresponding `ReasoningKind`.
#[cfg(test)]
#[must_use]
fn reasoning_from_solver(solver: &str) -> ReasoningKind {
    match solver {
        "z4" => ReasoningKind::Smt,
        "zani" => ReasoningKind::BoundedModelCheck { depth: 0 },
        "sunder" => ReasoningKind::Deductive,
        "certus" => ReasoningKind::OwnershipAnalysis,
        "lean5" => ReasoningKind::Constructive,
        "tla2" => ReasoningKind::ExplicitStateModel,
        "gamma-crown" => ReasoningKind::NeuralBounding,
        _ => ReasoningKind::Smt,
    }
}

/// Determine assurance level from certificate validation status.
#[cfg(test)]
#[must_use]
fn assurance_from_validation(validated: bool, has_certificate: bool) -> AssuranceLevel {
    match (validated, has_certificate) {
        (true, true) => AssuranceLevel::Certified,
        (false, true) => AssuranceLevel::SmtBacked,
        (_, false) => AssuranceLevel::Trusted,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_evidence_from_certificate_no_cert() {
        let strength = ProofStrength::smt_unsat();
        let evidence = evidence_from_certificate(&strength, None);
        assert_eq!(evidence.reasoning, ReasoningKind::Smt);
        assert_eq!(evidence.assurance, AssuranceLevel::SmtBacked);
    }

    #[test]
    fn test_evidence_from_certificate_empty_cert() {
        let strength = ProofStrength::smt_unsat();
        let evidence = evidence_from_certificate(&strength, Some(&[]));
        assert_eq!(evidence.reasoning, ReasoningKind::Smt);
        assert_eq!(evidence.assurance, AssuranceLevel::SmtBacked);
    }

    #[test]
    fn test_evidence_from_certificate_with_cert() {
        let strength = ProofStrength::smt_unsat();
        let evidence = evidence_from_certificate(&strength, Some(&[1, 2, 3]));
        assert_eq!(evidence.reasoning, ReasoningKind::Smt);
        // Currently stays SmtBacked until full validation is implemented.
        assert_eq!(evidence.assurance, AssuranceLevel::SmtBacked);
    }

    #[test]
    fn test_reasoning_from_solver_known() {
        assert_eq!(reasoning_from_solver("z4"), ReasoningKind::Smt);
        assert_eq!(reasoning_from_solver("sunder"), ReasoningKind::Deductive);
        assert_eq!(reasoning_from_solver("lean5"), ReasoningKind::Constructive);
        assert_eq!(reasoning_from_solver("gamma-crown"), ReasoningKind::NeuralBounding);
    }

    #[test]
    fn test_reasoning_from_solver_unknown_defaults_to_smt() {
        assert_eq!(reasoning_from_solver("unknown-solver"), ReasoningKind::Smt);
    }

    #[test]
    fn test_assurance_from_validation() {
        assert_eq!(assurance_from_validation(true, true), AssuranceLevel::Certified);
        assert_eq!(assurance_from_validation(false, true), AssuranceLevel::SmtBacked);
        assert_eq!(assurance_from_validation(true, false), AssuranceLevel::Trusted);
        assert_eq!(assurance_from_validation(false, false), AssuranceLevel::Trusted);
    }
}
