// trust-lsp/convert.rs: Convert tRust verification results to LSP Diagnostics
//
// Maps ObligationReport outcomes to LSP Diagnostic messages:
//   - Failed -> Error severity, with counterexample in message
//   - Unknown/Timeout -> Warning severity
//   - Proved -> Information severity (green checkmark hint)
//   - RuntimeChecked -> Hint severity
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;
use std::fmt::Write;

use trust_report::diagnostics::{error_code_for_kind, suggested_fix};
use trust_types::{
    JsonProofReport, ObligationOutcome, ObligationReport, ProofStrength, SourceSpan,
};

use crate::protocol::{
    Diagnostic, DiagnosticCode, DiagnosticRelatedInformation, DiagnosticSeverity, Location,
    Position, PublishDiagnosticsParams, Range,
};

/// Convert a `SourceSpan` to an LSP `Range`.
///
/// LSP uses 0-based line/character; tRust `SourceSpan` uses 1-based line/col.
/// Clamps to 0 if the source span has line=0 (default/unknown location).
#[must_use]
pub(crate) fn source_span_to_range(span: &SourceSpan) -> Range {
    Range {
        start: Position {
            line: span.line_start.saturating_sub(1),
            character: span.col_start.saturating_sub(1),
        },
        end: Position {
            line: span.line_end.saturating_sub(1),
            character: span.col_end.saturating_sub(1),
        },
    }
}

/// Convert a file path to a `file://` URI.
///
/// If the path is already a URI, returns it unchanged.
#[must_use]
pub(crate) fn file_to_uri(path: &str) -> String {
    if path.starts_with("file://") {
        return path.to_string();
    }
    if path.starts_with('/') {
        format!("file://{path}")
    } else {
        // Relative path — prefix with file:///
        format!("file:///{path}")
    }
}

/// Convert a single `ObligationReport` to an LSP `Diagnostic`.
///
/// Maps verification outcomes to LSP severity levels:
/// - `Failed` -> `Error` with counterexample details
/// - `Unknown` / `Timeout` -> `Warning`
/// - `Proved` -> `Information` (shows proof strength as inline hint)
/// - `RuntimeChecked` -> `Hint`
#[must_use]
pub(crate) fn obligation_to_diagnostic(obligation: &ObligationReport) -> Diagnostic {
    let error_code = error_code_for_kind(&obligation.kind);

    let (severity, message) = match &obligation.outcome {
        ObligationOutcome::Proved { strength } => {
            let msg = format_proved_message(&obligation.description, strength, obligation.time_ms);
            (DiagnosticSeverity::Information, msg)
        }
        ObligationOutcome::Failed { counterexample } => {
            let msg = format_failed_message(
                error_code.title,
                &obligation.description,
                counterexample.as_ref(),
            );
            (DiagnosticSeverity::Error, msg)
        }
        ObligationOutcome::Unknown { reason } => {
            let msg = format!(
                "{}: {} (solver returned unknown: {})",
                error_code.title, obligation.description, reason
            );
            (DiagnosticSeverity::Warning, msg)
        }
        ObligationOutcome::RuntimeChecked { note } => {
            let msg = match note {
                Some(n) => format!(
                    "Runtime checked: {} ({})",
                    obligation.description, n
                ),
                None => format!("Runtime checked: {}", obligation.description),
            };
            (DiagnosticSeverity::Hint, msg)
        }
        ObligationOutcome::Timeout { timeout_ms } => {
            let msg = format!(
                "{}: {} (timed out after {}ms)",
                error_code.title, obligation.description, timeout_ms
            );
            (DiagnosticSeverity::Warning, msg)
        }
        _ => {
            let msg = format!("{}: {}", error_code.title, obligation.description);
            (DiagnosticSeverity::Warning, msg)
        }
    };

    let range = obligation
        .location
        .as_ref()
        .map(source_span_to_range)
        .unwrap_or(Range {
            start: Position { line: 0, character: 0 },
            end: Position { line: 0, character: 0 },
        });

    // Add suggested fix as related information when applicable.
    let mut related = Vec::new();
    if matches!(
        obligation.outcome,
        ObligationOutcome::Failed { .. }
            | ObligationOutcome::Unknown { .. }
            | ObligationOutcome::Timeout { .. }
    ) {
        let fix = suggested_fix(&obligation.kind);
        if let Some(loc) = &obligation.location {
            related.push(DiagnosticRelatedInformation {
                location: Location {
                    uri: file_to_uri(&loc.file),
                    range: source_span_to_range(loc),
                },
                message: format!("help: {fix}"),
            });
        }
    }

    Diagnostic {
        range,
        severity: Some(severity),
        code: Some(DiagnosticCode::String(error_code.code())),
        source: Some("tRust".to_string()),
        message,
        tags: vec![],
        related_information: related,
        data: Some(serde_json::json!({
            "solver": obligation.solver,
            "time_ms": obligation.time_ms,
            "kind": obligation.kind,
            "proof_level": format!("{:?}", obligation.proof_level),
        })),
    }
}

/// Convert a full `JsonProofReport` to per-file `PublishDiagnosticsParams`.
///
/// Groups diagnostics by source file URI. Each file gets one
/// `PublishDiagnosticsParams` with all its diagnostics.
#[must_use]
pub(crate) fn report_to_diagnostics(report: &JsonProofReport) -> Vec<PublishDiagnosticsParams> {
    let mut by_file: FxHashMap<String, Vec<Diagnostic>> = FxHashMap::default();

    for func in &report.functions {
        for obligation in &func.obligations {
            let diag = obligation_to_diagnostic(obligation);

            let uri = obligation
                .location
                .as_ref()
                .map(|loc| file_to_uri(&loc.file))
                .unwrap_or_else(|| "file:///unknown".to_string());

            by_file.entry(uri).or_default().push(diag);
        }
    }

    let mut result: Vec<PublishDiagnosticsParams> = by_file
        .into_iter()
        .map(|(uri, diagnostics)| PublishDiagnosticsParams { uri, diagnostics, version: None })
        .collect();

    // Sort by URI for deterministic output.
    result.sort_by(|a, b| a.uri.cmp(&b.uri));
    result
}

// ---------------------------------------------------------------------------
// Message formatting helpers
// ---------------------------------------------------------------------------

fn format_proved_message(description: &str, strength: &ProofStrength, time_ms: u64) -> String {
    let method = match &strength.reasoning {
        trust_types::ReasoningKind::Smt => "SMT",
        trust_types::ReasoningKind::BoundedModelCheck { depth } => {
            return format!(
                "Proved safe (BMC depth {depth}, {time_ms}ms): {description}"
            );
        }
        trust_types::ReasoningKind::Inductive => "induction",
        trust_types::ReasoningKind::Deductive => "deduction",
        trust_types::ReasoningKind::Constructive => "constructive proof",
        trust_types::ReasoningKind::Pdr => "PDR/IC3",
        trust_types::ReasoningKind::ChcSpacer => "CHC/Spacer",
        trust_types::ReasoningKind::AbstractInterpretation => "abstract interpretation",
        trust_types::ReasoningKind::CdclResolution => "CDCL resolution",
        trust_types::ReasoningKind::TheoryLemma { theory } => {
            return format!(
                "Proved safe by {theory:?} theory lemma ({time_ms}ms): {description}"
            );
        }
        trust_types::ReasoningKind::BitBlasting => "bit-blasting",
        trust_types::ReasoningKind::SymbolicExecution => "symbolic execution",
        trust_types::ReasoningKind::OwnershipAnalysis => "ownership analysis",
        trust_types::ReasoningKind::ExplicitStateModel => "explicit-state model checking",
        trust_types::ReasoningKind::NeuralBounding => "neural bounding",
        trust_types::ReasoningKind::Interpolation => "Craig interpolation",
        trust_types::ReasoningKind::ExhaustiveFinite(states) => {
            return format!(
                "Proved safe (exhaustive, {states} states, {time_ms}ms): {description}"
            );
        }
        _ => "verification",
    };
    format!("Proved safe by {method} ({time_ms}ms): {description}")
}

fn format_failed_message(
    title: &str,
    description: &str,
    counterexample: Option<&trust_types::CounterexampleReport>,
) -> String {
    let mut msg = format!("{title}: {description}");

    if let Some(cex) = counterexample {
        let vars: Vec<String> = cex
            .variables
            .iter()
            .map(|v| format!("{} = {}", v.name, v.display))
            .collect();
        if !vars.is_empty() {
            let _ = write!(msg, "\nCounterexample: {}", vars.join(", "));
        }
    }

    msg
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use trust_types::*;

    use super::*;

    #[test]
    fn test_source_span_to_range_1based_to_0based() {
        let span = SourceSpan {
            file: "src/lib.rs".to_string(),
            line_start: 5,
            col_start: 10,
            line_end: 5,
            col_end: 20,
        };
        let range = source_span_to_range(&span);
        assert_eq!(range.start.line, 4);
        assert_eq!(range.start.character, 9);
        assert_eq!(range.end.line, 4);
        assert_eq!(range.end.character, 19);
    }

    #[test]
    fn test_source_span_to_range_zero_clamp() {
        let span = SourceSpan::default();
        let range = source_span_to_range(&span);
        assert_eq!(range.start.line, 0);
        assert_eq!(range.start.character, 0);
    }

    #[test]
    fn test_file_to_uri_absolute() {
        assert_eq!(file_to_uri("/src/lib.rs"), "file:///src/lib.rs");
    }

    #[test]
    fn test_file_to_uri_relative() {
        assert_eq!(file_to_uri("src/lib.rs"), "file:///src/lib.rs");
    }

    #[test]
    fn test_file_to_uri_already_uri() {
        assert_eq!(
            file_to_uri("file:///src/lib.rs"),
            "file:///src/lib.rs"
        );
    }

    #[test]
    fn test_obligation_to_diagnostic_proved() {
        let ob = ObligationReport {
            description: "division by zero".to_string(),
            kind: "division_by_zero".to_string(),
            proof_level: ProofLevel::L0Safety,
            location: Some(SourceSpan {
                file: "src/math.rs".to_string(),
                line_start: 10,
                col_start: 5,
                line_end: 10,
                col_end: 15,
            }),
            outcome: ObligationOutcome::Proved {
                strength: ProofStrength::smt_unsat(),
            },
            solver: "z4".to_string(),
            time_ms: 3,
            evidence: None,
        };

        let diag = obligation_to_diagnostic(&ob);
        assert_eq!(diag.severity, Some(DiagnosticSeverity::Information));
        assert!(diag.message.contains("Proved safe by SMT"));
        assert!(diag.message.contains("3ms"));
        assert_eq!(diag.code, Some(DiagnosticCode::String("E-TRUST-003".to_string())));
        assert_eq!(diag.source, Some("tRust".to_string()));
        assert_eq!(diag.range.start.line, 9); // 0-based
        assert!(diag.related_information.is_empty()); // No fix needed for proved
    }

    #[test]
    fn test_obligation_to_diagnostic_failed_with_counterexample() {
        let ob = ObligationReport {
            description: "arithmetic overflow (Add)".to_string(),
            kind: "arithmetic_overflow_add".to_string(),
            proof_level: ProofLevel::L0Safety,
            location: Some(SourceSpan {
                file: "src/midpoint.rs".to_string(),
                line_start: 5,
                col_start: 5,
                line_end: 5,
                col_end: 10,
            }),
            outcome: ObligationOutcome::Failed {
                counterexample: Some(CounterexampleReport {
                    variables: vec![
                        CounterexampleVariable {
                            name: "a".to_string(),
                            value: "18446744073709551615".to_string(),
                            value_type: "uint".to_string(),
                            display: "18446744073709551615".to_string(),
                        },
                        CounterexampleVariable {
                            name: "b".to_string(),
                            value: "1".to_string(),
                            value_type: "uint".to_string(),
                            display: "1".to_string(),
                        },
                    ],
                }),
            },
            solver: "z4".to_string(),
            time_ms: 3,
            evidence: None,
        };

        let diag = obligation_to_diagnostic(&ob);
        assert_eq!(diag.severity, Some(DiagnosticSeverity::Error));
        assert!(diag.message.contains("possible arithmetic overflow"));
        assert!(diag.message.contains("Counterexample: a = 18446744073709551615, b = 1"));
        assert_eq!(diag.code, Some(DiagnosticCode::String("E-TRUST-001".to_string())));
        // Should have suggested fix as related info
        assert_eq!(diag.related_information.len(), 1);
        assert!(diag.related_information[0].message.contains("help:"));
        assert!(diag.related_information[0].message.contains("checked"));
    }

    #[test]
    fn test_obligation_to_diagnostic_unknown() {
        let ob = ObligationReport {
            description: "index out of bounds".to_string(),
            kind: "index_out_of_bounds".to_string(),
            proof_level: ProofLevel::L0Safety,
            location: Some(SourceSpan {
                file: "src/lookup.rs".to_string(),
                line_start: 12,
                col_start: 9,
                line_end: 12,
                col_end: 20,
            }),
            outcome: ObligationOutcome::Unknown {
                reason: "nonlinear arithmetic".to_string(),
            },
            solver: "z4".to_string(),
            time_ms: 50,
            evidence: None,
        };

        let diag = obligation_to_diagnostic(&ob);
        assert_eq!(diag.severity, Some(DiagnosticSeverity::Warning));
        assert!(diag.message.contains("nonlinear arithmetic"));
        assert_eq!(diag.related_information.len(), 1);
    }

    #[test]
    fn test_obligation_to_diagnostic_timeout() {
        let ob = ObligationReport {
            description: "postcondition".to_string(),
            kind: "postcondition".to_string(),
            proof_level: ProofLevel::L1Functional,
            location: None,
            outcome: ObligationOutcome::Timeout { timeout_ms: 5000 },
            solver: "z4".to_string(),
            time_ms: 5000,
            evidence: None,
        };

        let diag = obligation_to_diagnostic(&ob);
        assert_eq!(diag.severity, Some(DiagnosticSeverity::Warning));
        assert!(diag.message.contains("timed out after 5000ms"));
        // No location => no related info
        assert!(diag.related_information.is_empty());
    }

    #[test]
    fn test_obligation_to_diagnostic_runtime_checked() {
        let ob = ObligationReport {
            description: "overflow check".to_string(),
            kind: "arithmetic_overflow_add".to_string(),
            proof_level: ProofLevel::L0Safety,
            location: None,
            outcome: ObligationOutcome::RuntimeChecked {
                note: Some("overflow_checks enabled".to_string()),
            },
            solver: "runtime".to_string(),
            time_ms: 0,
            evidence: None,
        };

        let diag = obligation_to_diagnostic(&ob);
        assert_eq!(diag.severity, Some(DiagnosticSeverity::Hint));
        assert!(diag.message.contains("Runtime checked"));
        assert!(diag.message.contains("overflow_checks enabled"));
    }

    #[test]
    fn test_obligation_to_diagnostic_no_location() {
        let ob = ObligationReport {
            description: "test".to_string(),
            kind: "division_by_zero".to_string(),
            proof_level: ProofLevel::L0Safety,
            location: None,
            outcome: ObligationOutcome::Failed { counterexample: None },
            solver: "z4".to_string(),
            time_ms: 1,
            evidence: None,
        };

        let diag = obligation_to_diagnostic(&ob);
        // Falls back to 0:0-0:0
        assert_eq!(diag.range.start.line, 0);
        assert_eq!(diag.range.start.character, 0);
    }

    #[test]
    fn test_report_to_diagnostics_groups_by_file() {
        let report = JsonProofReport {
            metadata: ReportMetadata {
                schema_version: "1.0".to_string(),
                trust_version: "0.1.0".to_string(),
                timestamp: "2026-01-01T00:00:00Z".to_string(),
                total_time_ms: 100,
            },
            crate_name: "test_crate".to_string(),
            summary: CrateSummary {
                functions_analyzed: 2,
                functions_verified: 1,
                functions_runtime_checked: 0,
                functions_with_violations: 1,
                functions_inconclusive: 0,
                total_obligations: 3,
                total_proved: 2,
                total_runtime_checked: 0,
                total_failed: 1,
                total_unknown: 0,
                verdict: CrateVerdict::HasViolations,
            },
            functions: vec![
                FunctionProofReport {
                    function: "safe_fn".to_string(),
                    summary: FunctionSummary {
                        total_obligations: 1,
                        proved: 1,
                        runtime_checked: 0,
                        failed: 0,
                        unknown: 0,
                        total_time_ms: 5,
                        max_proof_level: Some(ProofLevel::L0Safety),
                        verdict: FunctionVerdict::Verified,
                    },
                    obligations: vec![ObligationReport {
                        description: "division by zero".to_string(),
                        kind: "division_by_zero".to_string(),
                        proof_level: ProofLevel::L0Safety,
                        location: Some(SourceSpan {
                            file: "src/safe.rs".to_string(),
                            line_start: 3,
                            col_start: 1,
                            line_end: 3,
                            col_end: 10,
                        }),
                        outcome: ObligationOutcome::Proved {
                            strength: ProofStrength::smt_unsat(),
                        },
                        solver: "z4".to_string(),
                        time_ms: 5,
                        evidence: None,
                    }],
                },
                FunctionProofReport {
                    function: "risky_fn".to_string(),
                    summary: FunctionSummary {
                        total_obligations: 2,
                        proved: 1,
                        runtime_checked: 0,
                        failed: 1,
                        unknown: 0,
                        total_time_ms: 10,
                        max_proof_level: Some(ProofLevel::L0Safety),
                        verdict: FunctionVerdict::HasViolations,
                    },
                    obligations: vec![
                        ObligationReport {
                            description: "overflow".to_string(),
                            kind: "arithmetic_overflow_add".to_string(),
                            proof_level: ProofLevel::L0Safety,
                            location: Some(SourceSpan {
                                file: "src/risky.rs".to_string(),
                                line_start: 5,
                                col_start: 5,
                                line_end: 5,
                                col_end: 10,
                            }),
                            outcome: ObligationOutcome::Failed {
                                counterexample: None,
                            },
                            solver: "z4".to_string(),
                            time_ms: 3,
                            evidence: None,
                        },
                        ObligationReport {
                            description: "bounds check".to_string(),
                            kind: "index_out_of_bounds".to_string(),
                            proof_level: ProofLevel::L0Safety,
                            location: Some(SourceSpan {
                                file: "src/risky.rs".to_string(),
                                line_start: 8,
                                col_start: 1,
                                line_end: 8,
                                col_end: 15,
                            }),
                            outcome: ObligationOutcome::Proved {
                                strength: ProofStrength::smt_unsat(),
                            },
                            solver: "z4".to_string(),
                            time_ms: 7,
                            evidence: None,
                        },
                    ],
                },
            ],
        };

        let params = report_to_diagnostics(&report);

        // Should produce 2 files: src/risky.rs and src/safe.rs
        assert_eq!(params.len(), 2);

        // Sorted by URI
        assert!(params[0].uri.contains("risky.rs"));
        assert!(params[1].uri.contains("safe.rs"));

        // risky.rs has 2 diagnostics (1 failed + 1 proved)
        assert_eq!(params[0].diagnostics.len(), 2);

        // safe.rs has 1 diagnostic (proved)
        assert_eq!(params[1].diagnostics.len(), 1);
        assert_eq!(
            params[1].diagnostics[0].severity,
            Some(DiagnosticSeverity::Information)
        );
    }

    #[test]
    fn test_proved_message_formatting() {
        let msg = format_proved_message(
            "division by zero",
            &ProofStrength::smt_unsat(),
            5,
        );
        assert_eq!(msg, "Proved safe by SMT (5ms): division by zero");

        let msg = format_proved_message(
            "loop invariant",
            &ProofStrength::bounded(10),
            100,
        );
        assert_eq!(msg, "Proved safe (BMC depth 10, 100ms): loop invariant");

        let msg = format_proved_message(
            "postcondition",
            &ProofStrength::deductive(),
            25,
        );
        assert_eq!(msg, "Proved safe by deduction (25ms): postcondition");
    }

    #[test]
    fn test_failed_message_with_counterexample() {
        let cex = CounterexampleReport {
            variables: vec![
                CounterexampleVariable {
                    name: "x".to_string(),
                    value: "42".to_string(),
                    value_type: "int".to_string(),
                    display: "42".to_string(),
                },
            ],
        };
        let msg = format_failed_message("possible overflow", "add overflow", Some(&cex));
        assert!(msg.contains("possible overflow: add overflow"));
        assert!(msg.contains("Counterexample: x = 42"));
    }

    #[test]
    fn test_failed_message_without_counterexample() {
        let msg = format_failed_message("possible overflow", "add overflow", None);
        assert_eq!(msg, "possible overflow: add overflow");
        assert!(!msg.contains("Counterexample"));
    }

    #[test]
    fn test_diagnostic_data_contains_metadata() {
        let ob = ObligationReport {
            description: "test".to_string(),
            kind: "division_by_zero".to_string(),
            proof_level: ProofLevel::L0Safety,
            location: None,
            outcome: ObligationOutcome::Proved {
                strength: ProofStrength::smt_unsat(),
            },
            solver: "z4".to_string(),
            time_ms: 5,
            evidence: None,
        };

        let diag = obligation_to_diagnostic(&ob);
        let data = diag.data.expect("should have data");
        assert_eq!(data["solver"], "z4");
        assert_eq!(data["time_ms"], 5);
        assert_eq!(data["kind"], "division_by_zero");
    }
}
