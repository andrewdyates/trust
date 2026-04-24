// trust-proof-cert proof composition checkers
//
// Composability checks, proof composition, transitive closure,
// weakening, and strengthening operations.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet};

use crate::formula_norm::formula_subsumes;
use crate::{CertificateId, CertificationStatus, ProofCertificate, SolverInfo};

use super::types::{
    ComposabilityResult, ComposedProof, CompositionError, FunctionStrength, Property,
};

/// Check if two certificates can be composed together.
///
/// Two certificates are composable if:
/// 1. They are not for the same function+VC (would be redundant)
/// 2. Neither is revoked/invalid (caller must check this separately)
/// 3. Their VC assumptions don't contradict each other
///
/// Returns `Err(CompositionError::FormulaDeserializationFailed)` if either
/// certificate's `formula_json` is corrupted and cannot be deserialized
/// during the semantic fallback check.
pub fn check_composability(
    a: &ProofCertificate,
    b: &ProofCertificate,
) -> Result<ComposabilityResult, CompositionError> {
    let mut issues = Vec::new();
    let mut shared_deps = Vec::new();

    // Check for same function + same VC kind (redundant composition)
    if a.function == b.function && a.vc_snapshot.kind == b.vc_snapshot.kind {
        issues.push(format!(
            "both certificates prove the same VC kind ({}) for function `{}`",
            a.vc_snapshot.kind, a.function
        ));
    }

    // Check for contradictory VC assumptions by examining the formula JSON.
    // If one proves P and the other proves NOT P for the same scope, they conflict.
    // This is a conservative syntactic check; semantic checking would require SMT.
    if a.function == b.function
        && a.vc_snapshot.formula_json == negate_formula_json(&b.vc_snapshot.formula_json)
    {
        issues.push(format!(
            "contradictory formulas for function `{}`: one proves negation of the other",
            a.function
        ));
    }

    // Track shared function dependencies
    if a.function == b.function {
        shared_deps.push(a.function.clone());
    }

    let result = ComposabilityResult { composable: issues.is_empty(), issues, shared_deps };

    // If syntactic check passes, return immediately.
    // If it fails, try semantic fallback for formula-level implication.
    if result.composable {
        return Ok(result);
    }

    // Attempt semantic composability as a fallback.
    // Only applies when the syntactic contradiction check fired — if the formulas
    // are semantically compatible (one subsumes the other), they can compose.
    check_composability_semantic(a, b)
}

/// Semantic composability check using formula-level implication.
///
/// When the syntactic `check_composability` detects a potential conflict
/// (e.g., formula JSON negation match), this function deserializes the
/// formulas and uses `formula_subsumes` from `formula_norm.rs` to check
/// whether the callee's conclusion logically implies the caller's assumption
/// (or vice versa). Semantically equivalent but syntactically different
/// formulas will pass this check.
///
/// Returns `Ok(ComposabilityResult)` with `composable = true` if semantic
/// subsumption holds in either direction, or if the formulas are for
/// different functions/VCs. Returns `Err(CompositionError::FormulaDeserializationFailed)`
/// if either certificate's `formula_json` cannot be deserialized.
pub(crate) fn check_composability_semantic(
    a: &ProofCertificate,
    b: &ProofCertificate,
) -> Result<ComposabilityResult, CompositionError> {
    use trust_types::Formula;

    let mut issues = Vec::new();
    let mut shared_deps = Vec::new();

    // Track shared function dependencies
    if a.function == b.function {
        shared_deps.push(a.function.clone());
    }

    // Same function + same VC kind is redundant regardless of semantics
    if a.function == b.function && a.vc_snapshot.kind == b.vc_snapshot.kind {
        issues.push(format!(
            "both certificates prove the same VC kind ({}) for function `{}`",
            a.vc_snapshot.kind, a.function
        ));
        return Ok(ComposabilityResult { composable: false, issues, shared_deps });
    }

    // Deserialize formulas for semantic comparison — propagate errors instead
    // of silently dropping them (tRust #756).
    let formula_a: Formula = serde_json::from_str(&a.vc_snapshot.formula_json).map_err(|e| {
        CompositionError::FormulaDeserializationFailed {
            function: a.function.clone(),
            reason: e.to_string(),
        }
    })?;
    let formula_b: Formula = serde_json::from_str(&b.vc_snapshot.formula_json).map_err(|e| {
        CompositionError::FormulaDeserializationFailed {
            function: b.function.clone(),
            reason: e.to_string(),
        }
    })?;

    // Check semantic compatibility: if either subsumes the other,
    // they are logically consistent (not contradictory).
    // Also check if they are not direct negations at the formula level.
    let a_subsumes_b = formula_subsumes(&formula_a, &formula_b);
    let b_subsumes_a = formula_subsumes(&formula_b, &formula_a);

    if a_subsumes_b || b_subsumes_a {
        // Formulas are semantically compatible — one implies the other
        Ok(ComposabilityResult { composable: true, issues: Vec::new(), shared_deps })
    } else {
        // Cannot determine semantic compatibility; check for contradiction
        // via implication of negation: if fa => NOT fb (or vice versa),
        // they are contradictory.
        let neg_fb = Formula::Not(Box::new(formula_b.clone()));
        let neg_fa = Formula::Not(Box::new(formula_a.clone()));
        if formula_subsumes(&formula_a, &neg_fb) || formula_subsumes(&formula_b, &neg_fa) {
            issues.push(format!(
                "semantic contradiction detected for function `{}`: formulas are mutually exclusive",
                a.function
            ));
        } else {
            // Formulas are neither subsuming nor contradictory at the
            // structural level — conservatively allow composition
            // (no evidence of conflict).
        }

        Ok(ComposabilityResult { composable: issues.is_empty(), issues, shared_deps })
    }
}

/// Compose multiple proof certificates into a single composed proof.
///
/// All certificates must be pairwise composable. Returns a `ComposedProof`
/// that summarizes the combined verification coverage.
pub fn compose_proofs(certs: &[&ProofCertificate]) -> Result<ComposedProof, CompositionError> {
    if certs.is_empty() {
        return Err(CompositionError::CompositionFailed {
            reason: "cannot compose zero certificates".to_string(),
        });
    }

    if certs.len() == 1 {
        let cert = certs[0];
        return Ok(ComposedProof {
            constituent_ids: vec![cert.id.0.clone()],
            functions: vec![cert.function.clone()],
            combined_strength: cert.solver.strength.clone(),
            combined_status: cert.status,
            total_time_ms: cert.solver.time_ms,
            is_consistent: true,
            call_edges: Vec::new(),
            function_strengths: vec![FunctionStrength {
                function: cert.function.clone(),
                strength: cert.solver.strength.clone(),
                status: cert.status,
            }],
        });
    }

    // Check pairwise composability
    for i in 0..certs.len() {
        for j in (i + 1)..certs.len() {
            let result = check_composability(certs[i], certs[j])?;
            if !result.composable {
                return Err(CompositionError::IncompatibleAssumptions {
                    cert_a: certs[i].id.0.clone(),
                    cert_b: certs[j].id.0.clone(),
                    detail: result.issues.join("; "),
                });
            }
        }
    }

    // Gather constituent data
    let constituent_ids: Vec<String> = certs.iter().map(|c| c.id.0.clone()).collect();

    let mut functions: Vec<String> = certs.iter().map(|c| c.function.clone()).collect();
    functions.sort();
    functions.dedup();

    let combined_strength = weakest_strength(certs.iter().map(|c| &c.solver));
    let combined_status = if certs.iter().all(|c| c.status == CertificationStatus::Certified) {
        CertificationStatus::Certified
    } else {
        CertificationStatus::Trusted
    };

    let total_time_ms: u64 = certs.iter().map(|c| c.solver.time_ms).sum();
    let function_strengths: Vec<FunctionStrength> = certs
        .iter()
        .map(|c| FunctionStrength {
            function: c.function.clone(),
            strength: c.solver.strength.clone(),
            status: c.status,
        })
        .collect();

    Ok(ComposedProof {
        constituent_ids,
        functions,
        combined_strength,
        combined_status,
        total_time_ms,
        is_consistent: true,
        call_edges: Vec::new(),
        function_strengths,
    })
}

/// Compute the transitive closure of provable facts from a set of certificates.
///
/// Given certificates that prove properties about functions, derive which
/// functions are transitively verified. For example, if we have proofs for
/// `foo` (which calls `bar`) and `bar`, then `foo` is transitively verified.
///
/// Returns the set of function names that are fully covered (all callees proved).
// tRust: BTreeMap for deterministic certificate output (#827)
pub fn transitive_closure(
    certs: &[&ProofCertificate],
    call_graph: &BTreeMap<String, Vec<String>>,
) -> BTreeSet<String> {
    // Build the set of proved functions
    let mut proved: BTreeSet<String> = certs.iter().map(|c| c.function.clone()).collect();
    let directly_proved: BTreeSet<String> = proved.clone();

    // Iterative fixed-point: a function is transitively verified if all its callees
    // are also in the proved set.
    let mut changed = true;
    while changed {
        changed = false;
        let current = proved.clone();
        for (caller, callees) in call_graph {
            if current.contains(caller) {
                continue;
            }
            if !callees.is_empty() && callees.iter().all(|callee| current.contains(callee)) {
                // All callees are proved, so the caller is transitively verified
                proved.insert(caller.clone());
                changed = true;
            }
        }

        // Remove functions from proved set whose callees are NOT all proved,
        // BUT never remove functions that have direct proof certificates.
        let mut to_remove = Vec::new();
        for func in &proved {
            if directly_proved.contains(func) {
                continue; // Never remove directly-proved functions
            }
            if let Some(callees) = call_graph.get(func)
                && !callees.iter().all(|callee| current.contains(callee))
            {
                to_remove.push(func.clone());
                changed = true;
            }
        }
        for func in to_remove {
            proved.remove(&func);
        }
    }

    proved
}

/// Weaken a certificate to a less precise property.
///
/// This creates a derived certificate that claims a weaker property than
/// the original. The original certificate logically implies the weaker one.
///
/// For now, weakening is checked syntactically by property name inclusion.
/// In production, this would involve formula implication checking via SMT.
pub fn weakening(
    cert: &ProofCertificate,
    weaker_property: &Property,
) -> Result<ProofCertificate, CompositionError> {
    // Check that the weaker property is a valid weakening
    // Conservative check: the weaker property name must be a prefix or
    // substring of the original VC kind (syntactic approximation).
    let original_kind = &cert.vc_snapshot.kind;
    if !is_valid_weakening(original_kind, &weaker_property.0) {
        return Err(CompositionError::WeakeningFailed {
            target_property: weaker_property.0.clone(),
        });
    }

    // Create a derived certificate with the weaker property
    let mut derived = cert.clone();
    // Mark as derived by appending weakening info to the VC kind
    derived.vc_snapshot.kind = format!("Weakened({})", weaker_property.0);
    // Regenerate ID since content changed
    derived.id =
        CertificateId::generate(&derived.function, &format!("{}-weakened", derived.timestamp));

    Ok(derived)
}

/// Check if a certificate can prove a stronger property.
///
/// Returns Ok(()) if the certificate's proof logically implies the stronger property.
/// Returns Err(StrengtheningFailed) otherwise.
///
/// In production, this would dispatch to an SMT solver to check implication.
/// For now, it checks syntactic containment.
pub fn strengthening_check(
    cert: &ProofCertificate,
    stronger_property: &Property,
) -> Result<(), CompositionError> {
    let original_kind = &cert.vc_snapshot.kind;

    // A certificate can prove a stronger property if the stronger property
    // is exactly what's proved, OR if what's proved is a more specific variant
    // of the stronger property (i.e., the cert proves something at least as
    // strong). We use structural prefix matching, not string containment.
    //
    // Example: cert proves "Assertion { message: \"x > 0\" }" which is at least
    // as strong as "Assertion" (the general category).
    if original_kind == &stronger_property.0 {
        return Ok(());
    }

    // Check if what's proved is a more specific variant of the target property.
    // If the original kind starts with the stronger property as a structural prefix,
    // then the cert proves a specific instance of the broader category.
    if original_kind.starts_with(&stronger_property.0) {
        let rest = &original_kind[stronger_property.0.len()..];
        if rest.is_empty() {
            return Ok(());
        }
        if let Some(ch) = rest.chars().next()
            && (ch == ' ' || ch == '{' || ch == '(' || ch == '<')
        {
            return Ok(());
        }
    }

    Err(CompositionError::StrengtheningFailed {
        cert_id: cert.id.0.clone(),
        target_property: stronger_property.0.clone(),
    })
}

/// Determine the weakest proof strength from a set of solver infos.
pub(crate) fn weakest_strength<'a>(
    solvers: impl Iterator<Item = &'a SolverInfo>,
) -> trust_types::ProofStrength {
    let mut weakest = trust_types::ProofStrength::constructive();

    for solver in solvers {
        let rank = strength_rank(&solver.strength);
        if rank < strength_rank(&weakest) {
            weakest = solver.strength.clone();
        }
    }

    weakest
}

/// Rank proof strengths from weakest (0) to strongest (4).
///
/// Ranking is based on the reasoning technique used. Bounded proofs rank
/// lowest, followed by SMT, deductive, inductive, and constructive.
pub(crate) fn strength_rank(s: &trust_types::ProofStrength) -> u8 {
    use trust_types::ReasoningKind;
    match &s.reasoning {
        ReasoningKind::BoundedModelCheck { .. } => 0,
        ReasoningKind::Smt => 1,
        ReasoningKind::Deductive => 2,
        ReasoningKind::Inductive | ReasoningKind::Pdr | ReasoningKind::ChcSpacer => 3,
        ReasoningKind::Constructive => 4,
        _ => 1, // default to SMT-level for unknown future variants
    }
}

/// Structural check for valid weakening.
///
/// Returns true if the weaker property is logically implied by the original.
/// A property is a valid weakening if:
/// - It is exactly equal to the original kind (identity weakening)
/// - It is a known category that generalizes the original (e.g., "Assertion"
///   generalizes "Assertion { message: ... }")
/// - The original kind starts with the weaker property followed by a structural
///   delimiter (space, '{', '('), indicating a more specific variant
///
/// Does NOT use arbitrary substring containment, which would allow nonsensical
/// weakenings like "sert" matching "Assertion".
fn is_valid_weakening(original_kind: &str, weaker: &str) -> bool {
    // Exact match (identity weakening is always valid)
    if original_kind == weaker {
        return true;
    }

    // The weaker property is a structural prefix of the original kind.
    // e.g., "Assertion" weakens "Assertion { message: ... }"
    // The original must start with the weaker string AND the next character
    // must be a structural delimiter (not a continuation of a word).
    if let Some(rest) = original_kind.strip_prefix(weaker) {
        if rest.is_empty() {
            return true;
        }
        // The character after the prefix must be a structural delimiter
        if let Some(ch) = rest.chars().next()
            && (ch == ' ' || ch == '{' || ch == '(' || ch == '<')
        {
            return true;
        }
    }

    false
}

/// Structural negation of a JSON-serialized [`Formula`].
///
/// Deserializes the formula, wraps it in [`Formula::Not`], and re-serializes.
/// Falls back to a conservative string wrapper if deserialization fails
/// (which means it will never spuriously match, only miss real contradictions).
pub(crate) fn negate_formula_json(formula: &str) -> String {
    use trust_types::Formula;

    match serde_json::from_str::<Formula>(formula) {
        Ok(f) => {
            let negated = Formula::Not(Box::new(f));
            // Serialization of a valid Formula should not fail.
            serde_json::to_string(&negated).unwrap_or_else(|_| format!("Not({formula})"))
        }
        Err(_) => {
            // Conservative fallback: will never match a real serialized formula,
            // so contradiction detection simply becomes a no-op.
            format!("Not({formula})")
        }
    }
}
