//! Text formatting for proof reports.
//!
//! Human-readable text output derived from the canonical JSON report.
//! Includes verdict labels, proof strength labels, and summary formatting.
//!
//! Author: Andrew Yates <andrew@andrewdyates.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::*;

/// Format a JSON proof report as a human-readable summary string.
///
/// This is the text format derived from the canonical JSON.
pub fn format_json_summary(report: &JsonProofReport) -> String {
    let mut lines = Vec::new();

    for func in &report.functions {
        let verdict_tag = function_verdict_label(func.summary.verdict);
        lines.push(format!(
            "  {} [{}] ({} obligations: {} proved, {} runtime-checked, {} failed, {} pending; {}ms; max level: {})",
            func.function,
            verdict_tag,
            func.summary.total_obligations,
            func.summary.proved,
            func.summary.runtime_checked,
            func.summary.failed,
            func.summary.unknown,
            func.summary.total_time_ms,
            proof_level_label(func.summary.max_proof_level)
        ));

        for ob in &func.obligations {
            let status_line = match &ob.outcome {
                ObligationOutcome::Proved { strength } => {
                    format!(
                        "    {} PROVED ({}, {}, {}ms)",
                        ob.description,
                        ob.solver,
                        proof_strength_label(strength),
                        ob.time_ms
                    )
                }
                ObligationOutcome::Failed { counterexample } => {
                    let cex_str = counterexample
                        .as_ref()
                        .map(|c| {
                            let vars: Vec<String> = c
                                .variables
                                .iter()
                                .map(|v| format!("{} = {}", v.name, v.display))
                                .collect();
                            format!(" counterexample: {}", vars.join(", "))
                        })
                        .unwrap_or_default();
                    format!("    {} FAILED ({}){cex_str}", ob.description, ob.solver)
                }
                ObligationOutcome::Unknown { reason } => {
                    format!("    {} UNKNOWN ({}: {})", ob.description, ob.solver, reason)
                }
                ObligationOutcome::RuntimeChecked { note } => {
                    let note_str = note.as_ref().map(|n| format!(": {n}")).unwrap_or_default();
                    format!("    {} RUNTIME CHECKED ({}{})", ob.description, ob.solver, note_str)
                }
                ObligationOutcome::Timeout { timeout_ms } => {
                    format!("    {} TIMEOUT ({}, {}ms)", ob.description, ob.solver, timeout_ms)
                }
                _ => format!("    {} UNKNOWN ({})", ob.description, ob.solver),
            };
            lines.push(status_line);
        }
    }

    lines.push(String::new());
    let s = &report.summary;
    lines.push(format!(
        "  {} functions, {} proved, {} runtime-checked, {} failed, {} unknown",
        s.functions_analyzed,
        s.total_proved,
        s.total_runtime_checked,
        s.total_failed,
        s.total_unknown
    ));

    let verdict_tag = match s.verdict {
        CrateVerdict::Verified => "VERIFIED",
        CrateVerdict::RuntimeChecked => "RUNTIME CHECKED",
        CrateVerdict::HasViolations => "HAS VIOLATIONS",
        CrateVerdict::Inconclusive => "INCONCLUSIVE",
        CrateVerdict::NoObligations => "NO OBLIGATIONS",
        _ => "unknown",
    };
    lines.push(format!("  Verdict: {verdict_tag}"));

    lines.join("\n")
}

/// Human-readable label for a function or crate-level verdict.
pub fn function_verdict_label(verdict: FunctionVerdict) -> &'static str {
    match verdict {
        FunctionVerdict::Verified => "VERIFIED",
        FunctionVerdict::RuntimeChecked => "RUNTIME CHECKED",
        FunctionVerdict::HasViolations => "VIOLATIONS",
        FunctionVerdict::Inconclusive => "INCONCLUSIVE",
        FunctionVerdict::NoObligations => "NO OBLIGATIONS",
        _ => "unknown",
    }
}

/// Human-readable label for a proof strength.
pub fn proof_strength_label(strength: &ProofStrength) -> String {
    use trust_types::ReasoningKind;
    let reasoning = match &strength.reasoning {
        ReasoningKind::Smt => "SMT UNSAT".to_string(),
        ReasoningKind::BoundedModelCheck { depth } => format!("BOUNDED (depth {depth})"),
        ReasoningKind::Inductive => "INDUCTIVE".to_string(),
        ReasoningKind::Deductive => "DEDUCTIVE".to_string(),
        ReasoningKind::Constructive => "CONSTRUCTIVE".to_string(),
        ReasoningKind::Pdr => "PDR".to_string(),
        ReasoningKind::ChcSpacer => "CHC/SPACER".to_string(),
        _ => "UNKNOWN".to_string(),
    };
    if strength.is_bounded()
        && let Some(depth) = strength.bounded_depth()
    {
        return format!("{reasoning} [bounded depth {depth}]");
    }
    reasoning
}

/// Human-readable label for a `ProofEvidence` (the #190 replacement for `ProofStrength`).
///
/// Converts a `ProofStrength` to `ProofEvidence` via `From` and then formats both
/// the reasoning method and assurance level. This is the first downstream caller
/// of `ProofEvidence` outside trust-types (#382).
pub fn proof_evidence_label(strength: &ProofStrength) -> String {
    let evidence: ProofEvidence = strength.clone().into();
    let reasoning = match &evidence.reasoning {
        ReasoningKind::Smt => "SMT UNSAT",
        ReasoningKind::BoundedModelCheck { .. } => "BOUNDED",
        ReasoningKind::Inductive => "INDUCTIVE",
        ReasoningKind::Deductive => "DEDUCTIVE",
        ReasoningKind::Constructive => "CONSTRUCTIVE",
        ReasoningKind::Pdr => "PDR",
        ReasoningKind::ChcSpacer => "CHC/SPACER",
        _ => "UNKNOWN",
    };
    let assurance = match &evidence.assurance {
        AssuranceLevel::Certified => "certified",
        AssuranceLevel::SmtBacked => "smt-backed",
        AssuranceLevel::Trusted => "trusted",
        AssuranceLevel::Unchecked => "unchecked",
        AssuranceLevel::BoundedSound { .. } => "trusted",
        _ => "unknown",
    };
    format!("{reasoning} ({assurance})")
}

/// Human-readable label for the strongest proof level seen in a function.
pub fn proof_level_label(level: Option<ProofLevel>) -> &'static str {
    match level {
        None => "none",
        Some(ProofLevel::L0Safety) => "L0 safety",
        Some(ProofLevel::L1Functional) => "L1 functional",
        Some(ProofLevel::L2Domain) => "L2 domain",
        _ => "unknown",
    }
}
