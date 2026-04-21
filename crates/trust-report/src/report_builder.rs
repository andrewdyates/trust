//! JSON report construction from raw verification results.
//!
//! This module contains the core logic for building the canonical JSON proof
//! report from raw `(VerificationCondition, VerificationResult)` pairs and
//! from proof annotations.
//!
//! Author: Andrew Yates <andrew@andrewdyates.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;

use trust_types::{
    AnnotationStatus, BinOp, Counterexample, CounterexampleValue, ProofLevel, ProofStrength,
    RuntimeCheckPolicy, RuntimeDisposition, SourceSpan, VcKind, VerificationCondition,
    VerificationResult, classify_runtime_disposition, *,
};

use crate::{SCHEMA_VERSION, TRUST_VERSION};

/// Build the canonical JSON proof report from raw verification results.
///
/// This is the primary report builder. The JSON report includes:
/// - Crate-level metadata (schema version, timestamp, timing)
/// - Crate-level summary (aggregated counts, verdict)
/// - Per-function reports with summaries and per-obligation detail
///
/// All other output formats should be derived from a `JsonProofReport`.
pub fn build_json_report(
    crate_name: &str,
    results: &[(VerificationCondition, VerificationResult)],
) -> JsonProofReport {
    build_json_report_with_policy(crate_name, results, RuntimeCheckPolicy::Auto, true)
}

/// Build the canonical JSON proof report from raw verification results using
/// the provided runtime-check policy and overflow-check configuration.
pub fn build_json_report_with_policy(
    crate_name: &str,
    results: &[(VerificationCondition, VerificationResult)],
    policy: RuntimeCheckPolicy,
    overflow_checks: bool,
) -> JsonProofReport {
    let start = std::time::Instant::now();

    let functions = build_function_reports(results, Some(policy), Some(overflow_checks));

    let summary = build_crate_summary(&functions);
    let total_time_ms = start.elapsed().as_millis() as u64
        + functions.iter().map(|f| f.summary.total_time_ms).sum::<u64>();

    JsonProofReport {
        metadata: ReportMetadata {
            schema_version: SCHEMA_VERSION.to_string(),
            trust_version: TRUST_VERSION.to_string(),
            timestamp: now_iso8601(),
            total_time_ms,
        },
        crate_name: crate_name.to_string(),
        summary,
        functions,
    }
}

/// Build the canonical JSON proof report from proof annotations.
///
/// This variant consumes the proof-carrying MIR annotation format emitted by
/// `trust-types` and converts it into the canonical JSON report structure.
pub fn build_json_report_from_annotations(
    crate_name: &str,
    annotations: &[ProofAnnotation],
) -> JsonProofReport {
    let start = std::time::Instant::now();

    let mut functions: Vec<FunctionProofReport> = annotations
        .iter()
        .map(|annotation| {
            let obligations: Vec<ObligationReport> = annotation
                .obligations
                .iter()
                .map(|obligation| {
                    // tRust #382: Derive ProofEvidence from annotation strength.
                    let evidence = obligation.strength.as_ref().map(|s| s.clone().into());
                    ObligationReport {
                        description: obligation.description.clone(),
                        kind: obligation.kind.clone(),
                        proof_level: obligation.proof_level,
                        location: convert_annotation_location(obligation.location.clone()),
                        outcome: convert_annotation_status(
                            obligation.status,
                            obligation.strength.clone(),
                            obligation.counterexample.as_ref(),
                            obligation.time_ms,
                        ),
                        solver: obligation.solver.clone(),
                        time_ms: obligation.time_ms,
                        evidence,
                    }
                })
                .collect();

            let total_time_ms = obligations.iter().map(|obligation| obligation.time_ms).sum();
            let verdict = if annotation.summary.total == 0 {
                FunctionVerdict::NoObligations
            } else if annotation.summary.failed > 0 {
                FunctionVerdict::HasViolations
            } else if annotation.summary.unknown > 0 {
                FunctionVerdict::Inconclusive
            } else if annotation.summary.runtime_checked > 0 {
                FunctionVerdict::RuntimeChecked
            } else {
                FunctionVerdict::Verified
            };

            debug_assert_eq!(annotation.summary.total, obligations.len());

            FunctionProofReport {
                function: if annotation.function_path.is_empty() {
                    annotation.function_name.clone()
                } else {
                    annotation.function_path.clone()
                },
                summary: FunctionSummary {
                    total_obligations: annotation.summary.total,
                    proved: annotation.summary.proved,
                    runtime_checked: annotation.summary.runtime_checked,
                    failed: annotation.summary.failed,
                    unknown: annotation.summary.unknown,
                    total_time_ms,
                    max_proof_level: annotation.summary.max_level,
                    verdict,
                },
                obligations,
            }
        })
        .collect();

    functions.sort_by(|a, b| a.function.cmp(&b.function));

    let summary = build_crate_summary(&functions);
    let total_time_ms = start.elapsed().as_millis() as u64
        + functions.iter().map(|function| function.summary.total_time_ms).sum::<u64>();

    JsonProofReport {
        metadata: ReportMetadata {
            schema_version: SCHEMA_VERSION.to_string(),
            trust_version: TRUST_VERSION.to_string(),
            timestamp: now_iso8601(),
            total_time_ms,
        },
        crate_name: crate_name.to_string(),
        summary,
        functions,
    }
}

/// Build per-function reports from raw (VC, result) pairs.
fn build_function_reports(
    results: &[(VerificationCondition, VerificationResult)],
    policy: Option<RuntimeCheckPolicy>,
    overflow_checks: Option<bool>,
) -> Vec<FunctionProofReport> {
    // Group by function name, preserving insertion order.
    let mut by_function: Vec<(String, Vec<(&VerificationCondition, &VerificationResult)>)> =
        Vec::new();
    let mut index_map: FxHashMap<String, usize> = FxHashMap::default();

    for (vc, result) in results {
        if let Some(&idx) = index_map.get(&vc.function) {
            by_function[idx].1.push((vc, result));
        } else {
            let idx = by_function.len();
            index_map.insert(vc.function.clone(), idx);
            by_function.push((vc.function.clone(), vec![(vc, result)]));
        }
    }

    let mut functions: Vec<FunctionProofReport> = by_function
        .into_iter()
        .map(|(func_name, pairs)| {
            let obligations = build_obligations(&pairs, policy, overflow_checks);
            let summary = build_function_summary(&obligations);
            FunctionProofReport { function: func_name, summary, obligations }
        })
        .collect();

    functions.sort_by(|a, b| a.function.cmp(&b.function));
    functions
}

/// Build per-obligation reports from (VC, result) pairs for one function.
fn build_obligations(
    pairs: &[(&VerificationCondition, &VerificationResult)],
    policy: Option<RuntimeCheckPolicy>,
    overflow_checks: Option<bool>,
) -> Vec<ObligationReport> {
    pairs
        .iter()
        .map(|(vc, result)| {
            let location = span_to_location(&vc.location);
            let (outcome, solver, time_ms) =
                result_to_outcome(&vc.kind, result, policy, overflow_checks);
            // tRust #382: Derive ProofEvidence from the VerificationResult.
            let evidence = result.evidence();

            ObligationReport {
                description: vc.kind.description(),
                kind: vc_kind_tag(&vc.kind),
                proof_level: vc.kind.proof_level(),
                location,
                outcome,
                solver,
                time_ms,
                evidence,
            }
        })
        .collect()
}

/// Convert a SourceSpan to Option<SourceSpan>, returning None for empty spans.
fn span_to_location(span: &SourceSpan) -> Option<SourceSpan> {
    if span.file.is_empty() && span.line_start == 0 {
        return None;
    }
    Some(SourceSpan {
        file: span.file.clone(),
        line_start: span.line_start,
        col_start: span.col_start,
        line_end: span.line_end,
        col_end: span.col_end,
    })
}

/// Convert an annotation status to an obligation outcome.
fn convert_annotation_status(
    status: AnnotationStatus,
    strength: Option<ProofStrength>,
    counterexample: Option<&Counterexample>,
    time_ms: u64,
) -> ObligationOutcome {
    match status {
        AnnotationStatus::Proved => {
            ObligationOutcome::Proved { strength: strength.unwrap_or(ProofStrength::smt_unsat()) }
        }
        AnnotationStatus::Failed => {
            ObligationOutcome::Failed { counterexample: counterexample.map(cex_to_report) }
        }
        AnnotationStatus::Unknown => {
            ObligationOutcome::Unknown { reason: "annotation reported unknown".to_string() }
        }
        AnnotationStatus::RuntimeChecked => ObligationOutcome::RuntimeChecked { note: None },
        AnnotationStatus::Timeout => ObligationOutcome::Timeout { timeout_ms: time_ms },
        _ => ObligationOutcome::Unknown { reason: "unhandled annotation status".to_string() },
    }
}

/// Convert an optional annotation span to an obligation location.
fn convert_annotation_location(location: Option<SourceSpan>) -> Option<SourceSpan> {
    location.as_ref().and_then(span_to_location)
}

/// Convert a VerificationResult to (ObligationOutcome, solver_name, time_ms).
fn result_to_outcome(
    vc_kind: &VcKind,
    result: &VerificationResult,
    policy: Option<RuntimeCheckPolicy>,
    overflow_checks: Option<bool>,
) -> (ObligationOutcome, String, u64) {
    let outcome = match policy {
        Some(policy) => {
            let disposition = classify_runtime_disposition(
                vc_kind,
                result,
                policy,
                overflow_checks.unwrap_or(true),
            );
            disposition_to_outcome(result, disposition)
        }
        None => raw_result_to_outcome(result),
    };

    (outcome, result.solver_name().to_string(), result.time_ms())
}

fn raw_result_to_outcome(result: &VerificationResult) -> ObligationOutcome {
    match result {
        VerificationResult::Proved { strength, .. } => {
            ObligationOutcome::Proved { strength: strength.clone() }
        }
        VerificationResult::Failed { counterexample, .. } => {
            ObligationOutcome::Failed { counterexample: counterexample.as_ref().map(cex_to_report) }
        }
        VerificationResult::Unknown { reason, .. } => {
            ObligationOutcome::Unknown { reason: reason.clone() }
        }
        VerificationResult::Timeout { timeout_ms, .. } => {
            ObligationOutcome::Timeout { timeout_ms: *timeout_ms }
        }
        _ => ObligationOutcome::Unknown { reason: "unhandled verification result variant".to_string() },
    }
}

fn disposition_to_outcome(
    result: &VerificationResult,
    disposition: RuntimeDisposition,
) -> ObligationOutcome {
    match disposition {
        RuntimeDisposition::Proved => match result {
            VerificationResult::Proved { strength, .. } => {
                ObligationOutcome::Proved { strength: strength.clone() }
            }
            _ => ObligationOutcome::Unknown {
                reason: "proved disposition but result is not Proved".to_string(),
            },
        },
        RuntimeDisposition::RuntimeChecked { note } => {
            ObligationOutcome::RuntimeChecked { note: Some(note) }
        }
        RuntimeDisposition::Failed => match result {
            VerificationResult::Failed { counterexample, .. } => ObligationOutcome::Failed {
                counterexample: counterexample.as_ref().map(cex_to_report),
            },
            _ => ObligationOutcome::Unknown {
                reason: "failed disposition but result is not Failed".to_string(),
            },
        },
        RuntimeDisposition::Unknown { reason } => ObligationOutcome::Unknown { reason },
        RuntimeDisposition::Timeout { timeout_ms } => ObligationOutcome::Timeout { timeout_ms },
        RuntimeDisposition::CompileError { reason } => ObligationOutcome::Unknown { reason },
        _ => ObligationOutcome::Unknown { reason: "unhandled verification result variant".to_string() },
    }
}

/// Convert a legacy Counterexample to a CounterexampleReport.
fn cex_to_report(cex: &Counterexample) -> CounterexampleReport {
    CounterexampleReport {
        variables: cex
            .assignments
            .iter()
            .map(|(name, val)| {
                let (value_str, value_type) = match val {
                    CounterexampleValue::Bool(b) => (b.to_string(), "bool"),
                    CounterexampleValue::Int(n) => (n.to_string(), "int"),
                    CounterexampleValue::Uint(n) => (n.to_string(), "uint"),
                    CounterexampleValue::Float(n) => (n.to_string(), "float"),
                    _ => ("unknown".to_string(), "unknown"),
                };
                CounterexampleVariable {
                    name: name.clone(),
                    value: value_str.clone(),
                    value_type: value_type.to_string(),
                    display: val.to_string(),
                }
            })
            .collect(),
    }
}

/// Machine-parseable kind tag string for a VcKind.
pub(crate) fn vc_kind_tag(kind: &VcKind) -> String {
    match kind {
        VcKind::ArithmeticOverflow { op, .. } => format!("arithmetic_overflow_{}", op_tag(op)),
        VcKind::ShiftOverflow { op, .. } => format!("shift_overflow_{}", op_tag(op)),
        VcKind::DivisionByZero => "division_by_zero".to_string(),
        VcKind::RemainderByZero => "remainder_by_zero".to_string(),
        VcKind::IndexOutOfBounds => "index_out_of_bounds".to_string(),
        VcKind::SliceBoundsCheck => "slice_bounds_check".to_string(),
        VcKind::CastOverflow { .. } => "cast_overflow".to_string(),
        VcKind::NegationOverflow { .. } => "negation_overflow".to_string(),
        VcKind::Assertion { .. } => "assertion".to_string(),
        VcKind::Precondition { .. } => "precondition".to_string(),
        VcKind::Postcondition => "postcondition".to_string(),
        VcKind::Unreachable => "unreachable".to_string(),
        VcKind::DeadState { .. } => "dead_state".to_string(),
        VcKind::Deadlock => "deadlock".to_string(),
        VcKind::Temporal { .. } => "temporal".to_string(),
        // tRust: Liveness and fairness kind tags (#49).
        VcKind::Liveness { .. } => "liveness".to_string(),
        VcKind::Fairness { .. } => "fairness".to_string(),
        VcKind::TaintViolation { .. } => "taint_violation".to_string(),
        VcKind::RefinementViolation { .. } => "refinement_violation".to_string(),
        VcKind::ResilienceViolation { .. } => "resilience_violation".to_string(),
        VcKind::ProtocolViolation { .. } => "protocol_violation".to_string(),
        VcKind::NonTermination { .. } => "non_termination".to_string(),
        VcKind::NeuralRobustness { .. } => "neural_robustness".to_string(),
        VcKind::NeuralOutputRange { .. } => "neural_output_range".to_string(),
        VcKind::NeuralLipschitz { .. } => "neural_lipschitz".to_string(),
        VcKind::NeuralMonotonicity { .. } => "neural_monotonicity".to_string(),
        // tRust #203: Data race and memory ordering tags.
        VcKind::DataRace { .. } => "data_race".to_string(),
        VcKind::InsufficientOrdering { .. } => "insufficient_ordering".to_string(),
        // tRust #149: Translation validation tag.
        VcKind::TranslationValidation { .. } => "translation_validation".to_string(),
        // tRust #433: Floating-point operation tags.
        VcKind::FloatDivisionByZero => "float_division_by_zero".to_string(),
        VcKind::FloatOverflowToInfinity { .. } => "float_overflow_to_infinity".to_string(),
        // tRust #438: Rvalue safety VC tags.
        VcKind::InvalidDiscriminant { .. } => "invalid_discriminant".to_string(),
        VcKind::AggregateArrayLengthMismatch { .. } => "aggregate_array_length_mismatch".to_string(),
// tRust #463: Unsafe operation tag.
        VcKind::UnsafeOperation { .. } => "unsafe_operation".to_string(),
_ => "unknown".to_string(),
    }
}

/// Lowercase tag for a BinOp.
fn op_tag(op: &BinOp) -> &'static str {
    match op {
        BinOp::Add => "add",
        BinOp::Sub => "sub",
        BinOp::Mul => "mul",
        BinOp::Div => "div",
        BinOp::Rem => "rem",
        BinOp::Shl => "shl",
        BinOp::Shr => "shr",
        BinOp::Eq => "eq",
        BinOp::Ne => "ne",
        BinOp::Lt => "lt",
        BinOp::Le => "le",
        BinOp::Gt => "gt",
        BinOp::Ge => "ge",
        BinOp::BitAnd => "bitand",
        BinOp::BitOr => "bitor",
        BinOp::BitXor => "bitxor",
        BinOp::Cmp => "cmp",
        _ => "unknown",
    }
}

/// Build a FunctionSummary from a list of obligation reports.
fn build_function_summary(obligations: &[ObligationReport]) -> FunctionSummary {
    let mut proved = 0usize;
    let mut runtime_checked = 0usize;
    let mut failed = 0usize;
    let mut unknown = 0usize;
    let mut total_time_ms = 0u64;
    let mut max_proof_level: Option<ProofLevel> = None;

    for ob in obligations {
        match &ob.outcome {
            ObligationOutcome::Proved { .. } => proved += 1,
            ObligationOutcome::RuntimeChecked { .. } => runtime_checked += 1,
            ObligationOutcome::Failed { .. } => failed += 1,
            ObligationOutcome::Unknown { .. } | ObligationOutcome::Timeout { .. } => unknown += 1,
            _ => { /* future variant -- skip */ }
        }
        total_time_ms += ob.time_ms;
        max_proof_level = Some(match max_proof_level {
            None => ob.proof_level,
            Some(current) => std::cmp::max(current, ob.proof_level),
        });
    }

    let verdict = if obligations.is_empty() {
        FunctionVerdict::NoObligations
    } else if failed > 0 {
        FunctionVerdict::HasViolations
    } else if unknown > 0 {
        FunctionVerdict::Inconclusive
    } else if runtime_checked > 0 {
        FunctionVerdict::RuntimeChecked
    } else {
        FunctionVerdict::Verified
    };

    FunctionSummary {
        total_obligations: obligations.len(),
        proved,
        runtime_checked,
        failed,
        unknown,
        total_time_ms,
        max_proof_level,
        verdict,
    }
}

/// Build a CrateSummary from all function reports.
pub(crate) fn build_crate_summary(functions: &[FunctionProofReport]) -> CrateSummary {
    let mut functions_verified = 0usize;
    let mut functions_runtime_checked = 0usize;
    let mut functions_with_violations = 0usize;
    let mut functions_inconclusive = 0usize;
    let mut total_obligations = 0usize;
    let mut total_proved = 0usize;
    let mut total_runtime_checked = 0usize;
    let mut total_failed = 0usize;
    let mut total_unknown = 0usize;

    for func in functions {
        match func.summary.verdict {
            FunctionVerdict::Verified => functions_verified += 1,
            FunctionVerdict::RuntimeChecked => functions_runtime_checked += 1,
            FunctionVerdict::HasViolations => functions_with_violations += 1,
            FunctionVerdict::Inconclusive => functions_inconclusive += 1,
            FunctionVerdict::NoObligations => {}
            _ => { /* future variant -- skip */ }
        }
        total_obligations += func.summary.total_obligations;
        total_proved += func.summary.proved;
        total_runtime_checked += func.summary.runtime_checked;
        total_failed += func.summary.failed;
        total_unknown += func.summary.unknown;
    }

    let verdict = if functions.is_empty() || total_obligations == 0 {
        CrateVerdict::NoObligations
    } else if total_failed > 0 {
        CrateVerdict::HasViolations
    } else if total_unknown > 0 {
        CrateVerdict::Inconclusive
    } else if total_runtime_checked > 0 {
        CrateVerdict::RuntimeChecked
    } else {
        CrateVerdict::Verified
    };

    CrateSummary {
        functions_analyzed: functions.len(),
        functions_verified,
        functions_runtime_checked,
        functions_with_violations,
        functions_inconclusive,
        total_obligations,
        total_proved,
        total_runtime_checked,
        total_failed,
        total_unknown,
        verdict,
    }
}

/// Get current time as ISO 8601 string.
///
/// Uses a minimal implementation to avoid pulling in chrono/time crates.
pub(crate) fn now_iso8601() -> String {
    // Use SystemTime for a basic ISO 8601 timestamp.
    let now = std::time::SystemTime::now();
    let duration = now.duration_since(std::time::UNIX_EPOCH).unwrap_or_default();
    let secs = duration.as_secs();
    // Simple UTC timestamp: seconds since epoch formatted as pseudo-ISO.
    // For production, replace with a proper time library.
    format!("{secs}")
}
