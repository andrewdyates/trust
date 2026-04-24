// trust-lsp/inlay_hints.rs: Per-function proof status inlay hints
//
// Produces LSP InlayHint annotations showing verification status for each
// function in a file. Hints appear at the function definition line:
//
//   fn get_midpoint(a: usize, b: usize) -> usize  // proved (3/3, 8ms)
//   fn risky_fn(x: u32) -> u32                      // FAILED (1/3)
//   fn unknown_fn(data: &[u8])                       // unknown (0/2)
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{FunctionProofReport, FunctionVerdict, JsonProofReport};

use crate::convert::file_to_uri;
use crate::protocol::{InlayHint, InlayHintParams, Position};

/// Proof status for display in an inlay hint.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ProofStatus {
    /// All obligations proved safe.
    Proved,
    /// At least one obligation failed.
    Failed,
    /// Some obligations were runtime checked, none failed.
    RuntimeChecked,
    /// Some obligations are unknown/inconclusive.
    Unknown,
    /// No obligations existed for this function.
    NoObligations,
}

impl ProofStatus {
    /// Map from `FunctionVerdict` to `ProofStatus`.
    #[must_use]
    pub(crate) fn from_verdict(verdict: &FunctionVerdict) -> Self {
        match verdict {
            FunctionVerdict::Verified => Self::Proved,
            FunctionVerdict::HasViolations => Self::Failed,
            FunctionVerdict::RuntimeChecked => Self::RuntimeChecked,
            FunctionVerdict::Inconclusive => Self::Unknown,
            FunctionVerdict::NoObligations => Self::NoObligations,
            _ => Self::Unknown,
        }
    }

    /// Unicode label for the inlay hint.
    #[must_use]
    pub(crate) fn label(self) -> &'static str {
        match self {
            Self::Proved => "\u{2713} proved",
            Self::Failed => "\u{2717} FAILED",
            Self::RuntimeChecked => "\u{25cb} runtime checked",
            Self::Unknown => "? unknown",
            Self::NoObligations => "\u{2014} no checks",
        }
    }
}

/// Build inlay hints for functions in the given file URI from a proof report.
///
/// Returns hints only for functions whose source location matches the
/// requested document. Each hint is placed at the end of the function's
/// first obligation line (or line 0 if no location data).
#[must_use]
pub(crate) fn inlay_hints_for_report(
    params: &InlayHintParams,
    report: &JsonProofReport,
) -> Vec<InlayHint> {
    let mut hints = Vec::new();

    for func in &report.functions {
        let hint = build_function_hint(
            func,
            &params.text_document.uri,
            params.range.start.line,
            params.range.end.line,
        );
        if let Some(h) = hint {
            hints.push(h);
        }
    }

    // Sort by line for deterministic output.
    hints.sort_by_key(|h| h.position.line);
    hints
}

/// Build a single inlay hint for a function's proof status.
///
/// Returns `None` if the function's source file doesn't match `uri` or
/// if the function's line is outside the visible range.
fn build_function_hint(
    func: &FunctionProofReport,
    uri: &str,
    visible_start: u32,
    visible_end: u32,
) -> Option<InlayHint> {
    // Find the function's location from its first obligation with a source span.
    let (file, line) = func.obligations.iter().find_map(|ob| {
        ob.location.as_ref().map(|loc| (file_to_uri(&loc.file), loc.line_start.saturating_sub(1)))
    })?;

    // Only include hints for the requested document.
    if file != uri {
        return None;
    }

    // Only include hints within the visible range.
    if line < visible_start || line > visible_end {
        return None;
    }

    let status = ProofStatus::from_verdict(&func.summary.verdict);
    let summary = &func.summary;

    let label = format!(
        "{} ({}/{}, {}ms)",
        status.label(),
        summary.proved + summary.runtime_checked,
        summary.total_obligations,
        summary.total_time_ms,
    );

    let tooltip = format!(
        "**{}** `{}`\n\n- Proved: {}\n- Runtime checked: {}\n- Failed: {}\n- Unknown: {}\n- Total time: {}ms",
        match status {
            ProofStatus::Proved => "Verified",
            ProofStatus::Failed => "Has violations",
            ProofStatus::RuntimeChecked => "Runtime checked",
            ProofStatus::Unknown => "Inconclusive",
            ProofStatus::NoObligations => "No obligations",
        },
        func.function,
        summary.proved,
        summary.runtime_checked,
        summary.failed,
        summary.unknown,
        summary.total_time_ms,
    );

    Some(InlayHint {
        position: Position { line, character: 0 },
        label,
        kind: None,
        tooltip: Some(tooltip),
        padding_left: Some(true),
        padding_right: None,
    })
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use trust_types::*;

    use crate::protocol::{Range, TextDocumentIdentifier};

    use super::*;

    fn make_report() -> JsonProofReport {
        JsonProofReport {
            metadata: ReportMetadata {
                schema_version: "1.0".to_string(),
                trust_version: "0.1.0".to_string(),
                timestamp: "2026-01-01T00:00:00Z".to_string(),
                total_time_ms: 15,
            },
            crate_name: "test".to_string(),
            summary: CrateSummary {
                functions_analyzed: 2,
                functions_verified: 1,
                functions_runtime_checked: 0,
                functions_with_violations: 1,
                functions_inconclusive: 0,
                total_obligations: 4,
                total_proved: 2,
                total_runtime_checked: 0,
                total_failed: 1,
                total_unknown: 1,
                verdict: CrateVerdict::HasViolations,
            },
            functions: vec![
                FunctionProofReport {
                    function: "safe_fn".into(),
                    summary: FunctionSummary {
                        total_obligations: 2,
                        proved: 2,
                        runtime_checked: 0,
                        failed: 0,
                        unknown: 0,
                        total_time_ms: 5,
                        max_proof_level: Some(ProofLevel::L0Safety),
                        verdict: FunctionVerdict::Verified,
                    },
                    obligations: vec![
                        ObligationReport {
                            description: "overflow".to_string(),
                            kind: "arithmetic_overflow_add".to_string(),
                            proof_level: ProofLevel::L0Safety,
                            location: Some(SourceSpan {
                                file: "src/lib.rs".to_string(),
                                line_start: 3,
                                col_start: 1,
                                line_end: 3,
                                col_end: 10,
                            }),
                            outcome: ObligationOutcome::Proved {
                                strength: ProofStrength::smt_unsat(),
                            },
                            solver: "z4".into(),
                            time_ms: 3,
                            evidence: None,
                        },
                        ObligationReport {
                            description: "div by zero".to_string(),
                            kind: "division_by_zero".to_string(),
                            proof_level: ProofLevel::L0Safety,
                            location: Some(SourceSpan {
                                file: "src/lib.rs".to_string(),
                                line_start: 4,
                                col_start: 1,
                                line_end: 4,
                                col_end: 10,
                            }),
                            outcome: ObligationOutcome::Proved {
                                strength: ProofStrength::smt_unsat(),
                            },
                            solver: "z4".into(),
                            time_ms: 2,
                            evidence: None,
                        },
                    ],
                },
                FunctionProofReport {
                    function: "risky_fn".into(),
                    summary: FunctionSummary {
                        total_obligations: 2,
                        proved: 0,
                        runtime_checked: 0,
                        failed: 1,
                        unknown: 1,
                        total_time_ms: 10,
                        max_proof_level: Some(ProofLevel::L0Safety),
                        verdict: FunctionVerdict::HasViolations,
                    },
                    obligations: vec![ObligationReport {
                        description: "overflow".to_string(),
                        kind: "arithmetic_overflow_add".to_string(),
                        proof_level: ProofLevel::L0Safety,
                        location: Some(SourceSpan {
                            file: "src/lib.rs".to_string(),
                            line_start: 10,
                            col_start: 5,
                            line_end: 10,
                            col_end: 10,
                        }),
                        outcome: ObligationOutcome::Failed { counterexample: None },
                        solver: "z4".into(),
                        time_ms: 5,
                        evidence: None,
                    }],
                },
            ],
        }
    }

    fn make_hint_params(uri: &str) -> InlayHintParams {
        InlayHintParams {
            text_document: TextDocumentIdentifier { uri: uri.to_string() },
            range: Range {
                start: Position { line: 0, character: 0 },
                end: Position { line: 100, character: 0 },
            },
        }
    }

    #[test]
    fn test_inlay_hints_for_matching_file() {
        let report = make_report();
        let params = make_hint_params("file:///src/lib.rs");

        let hints = inlay_hints_for_report(&params, &report);
        assert_eq!(hints.len(), 2);

        // First hint: safe_fn (proved)
        assert!(hints[0].label.contains("\u{2713} proved"));
        assert!(hints[0].label.contains("2/2"));
        assert_eq!(hints[0].position.line, 2); // line 3 -> 0-based = 2

        // Second hint: risky_fn (failed)
        assert!(hints[1].label.contains("\u{2717} FAILED"));
        assert!(hints[1].label.contains("0/2"));
        assert_eq!(hints[1].position.line, 9); // line 10 -> 0-based = 9
    }

    #[test]
    fn test_inlay_hints_filter_by_uri() {
        let report = make_report();
        let params = make_hint_params("file:///src/other.rs");

        let hints = inlay_hints_for_report(&params, &report);
        assert!(hints.is_empty());
    }

    #[test]
    fn test_inlay_hints_filter_by_visible_range() {
        let report = make_report();
        let params = InlayHintParams {
            text_document: TextDocumentIdentifier { uri: "file:///src/lib.rs".to_string() },
            range: Range {
                start: Position { line: 0, character: 0 },
                end: Position { line: 5, character: 0 },
            },
        };

        let hints = inlay_hints_for_report(&params, &report);
        // Only safe_fn (line 2) is in range [0, 5], risky_fn (line 9) is not.
        assert_eq!(hints.len(), 1);
        assert!(hints[0].label.contains("proved"));
    }

    #[test]
    fn test_inlay_hint_tooltip_contains_details() {
        let report = make_report();
        let params = make_hint_params("file:///src/lib.rs");

        let hints = inlay_hints_for_report(&params, &report);
        let tooltip = hints[0].tooltip.as_ref().expect("tooltip");
        assert!(tooltip.contains("Proved: 2"));
        assert!(tooltip.contains("Failed: 0"));
        assert!(tooltip.contains("`safe_fn`"));
    }

    #[test]
    fn test_proof_status_labels() {
        assert_eq!(ProofStatus::Proved.label(), "\u{2713} proved");
        assert_eq!(ProofStatus::Failed.label(), "\u{2717} FAILED");
        assert_eq!(ProofStatus::Unknown.label(), "? unknown");
        assert_eq!(ProofStatus::RuntimeChecked.label(), "\u{25cb} runtime checked");
        assert_eq!(ProofStatus::NoObligations.label(), "\u{2014} no checks");
    }

    #[test]
    fn test_proof_status_from_verdict() {
        assert_eq!(ProofStatus::from_verdict(&FunctionVerdict::Verified), ProofStatus::Proved);
        assert_eq!(ProofStatus::from_verdict(&FunctionVerdict::HasViolations), ProofStatus::Failed);
        assert_eq!(ProofStatus::from_verdict(&FunctionVerdict::Inconclusive), ProofStatus::Unknown);
        assert_eq!(
            ProofStatus::from_verdict(&FunctionVerdict::RuntimeChecked),
            ProofStatus::RuntimeChecked
        );
        assert_eq!(
            ProofStatus::from_verdict(&FunctionVerdict::NoObligations),
            ProofStatus::NoObligations
        );
    }
}
