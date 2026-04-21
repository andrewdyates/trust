// trust-report/terminal.rs: Colored terminal proof report formatter
//
// Renders a JsonProofReport as ANSI-colored terminal output.
// Respects the NO_COLOR environment variable (https://no-color.org/).
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{CrateVerdict, FunctionVerdict, JsonProofReport, ObligationOutcome};

use crate::{function_verdict_label, proof_level_label, proof_strength_label};

// ANSI escape codes
const GREEN: &str = "\x1b[32m";
const BLUE: &str = "\x1b[34m";
const RED: &str = "\x1b[31m";
const YELLOW: &str = "\x1b[33m";
const BOLD: &str = "\x1b[1m";
const DIM: &str = "\x1b[2m";
const RESET: &str = "\x1b[0m";

/// Whether ANSI color codes should be emitted.
///
/// Returns `false` when the `NO_COLOR` environment variable is set
/// (any value, including empty), per <https://no-color.org/>.
fn use_color() -> bool {
    std::env::var_os("NO_COLOR").is_none()
}

/// ANSI helper: wraps `text` in the given code if color is enabled.
fn ansi(code: &str, text: &str, color: bool) -> String {
    if color { format!("{code}{text}{RESET}") } else { text.to_string() }
}

/// Format a `JsonProofReport` as a colored terminal string.
///
/// The output includes:
/// - A header with crate name and metadata
/// - Per-function groups with obligation details
/// - A summary line at the bottom: "X proved, Y runtime-checked, Z failed, W pending"
///
/// Respects `NO_COLOR` environment variable.
pub fn format_terminal_report(report: &JsonProofReport) -> String {
    format_terminal_report_impl(report, use_color())
}

/// Internal implementation that accepts an explicit color flag.
///
/// Exposed as `pub(crate)` so tests can exercise both colored and
/// plain output without mutating process-global environment variables.
pub(crate) fn format_terminal_report_impl(report: &JsonProofReport, color: bool) -> String {
    let mut lines: Vec<String> = Vec::new();

    // Header
    lines.push(format!(
        "{} {} {}",
        ansi(BOLD, "tRust verification report:", color),
        ansi(BOLD, &report.crate_name, color),
        ansi(
            DIM,
            &format!("(v{}, {}ms)", report.metadata.trust_version, report.metadata.total_time_ms),
            color,
        ),
    ));
    lines.push(String::new());

    // Per-function groups
    for func in &report.functions {
        let verdict_str = match func.summary.verdict {
            FunctionVerdict::Verified => {
                ansi(GREEN, function_verdict_label(func.summary.verdict), color)
            }
            FunctionVerdict::RuntimeChecked => {
                ansi(BLUE, function_verdict_label(func.summary.verdict), color)
            }
            FunctionVerdict::HasViolations => {
                ansi(RED, function_verdict_label(func.summary.verdict), color)
            }
            FunctionVerdict::Inconclusive => {
                ansi(YELLOW, function_verdict_label(func.summary.verdict), color)
            }
            FunctionVerdict::NoObligations => {
                ansi(DIM, function_verdict_label(func.summary.verdict), color)
            }
            _ => "UNKNOWN".to_string(),
        };
        lines.push(format!("  {} [{}]", ansi(BOLD, &func.function, color), verdict_str,));
        lines.push(format!(
            "    {}",
            ansi(
                DIM,
                &format!(
                    "{} proved, {} runtime-checked, {} failed, {} pending | {} obligations | max level: {} | {}ms",
                    func.summary.proved,
                    func.summary.runtime_checked,
                    func.summary.failed,
                    func.summary.unknown,
                    func.summary.total_obligations,
                    proof_level_label(func.summary.max_proof_level),
                    func.summary.total_time_ms
                ),
                color,
            )
        ));

        for ob in &func.obligations {
            let status_colored = match &ob.outcome {
                ObligationOutcome::Proved { strength } => {
                    ansi(GREEN, &format!("PROVED [{}]", proof_strength_label(strength)), color)
                }
                ObligationOutcome::RuntimeChecked { .. } => ansi(BLUE, "RUNTIME-CHECKED", color),
                ObligationOutcome::Failed { .. } => ansi(RED, "FAILED", color),
                ObligationOutcome::Unknown { .. } => ansi(YELLOW, "UNKNOWN", color),
                ObligationOutcome::Timeout { .. } => ansi(YELLOW, "TIMEOUT", color),
                _ => "UNKNOWN".to_string(),
            };

            let location_str = ob
                .location
                .as_ref()
                .map(|loc| format!(" {}:{}", loc.file, loc.line_start))
                .unwrap_or_default();

            let meta =
                ansi(DIM, &format!("({}, {}ms{})", ob.solver, ob.time_ms, location_str), color);

            lines.push(format!("    {} {} {}", status_colored, ob.description, meta));

            // Extra detail for failures with counterexamples
            if let ObligationOutcome::Failed { counterexample: Some(cex) } = &ob.outcome {
                let vars: Vec<String> =
                    cex.variables.iter().map(|v| format!("{} = {}", v.name, v.display)).collect();
                lines.push(format!(
                    "      {} {}",
                    ansi(RED, "counterexample:", color),
                    vars.join(", "),
                ));
            }

            // Extra detail for unknown reasons
            if let ObligationOutcome::Unknown { reason } = &ob.outcome {
                lines.push(format!("      {} {}", ansi(YELLOW, "reason:", color), reason,));
            }

            // Extra detail for runtime-checked notes
            if let ObligationOutcome::RuntimeChecked { note: Some(note) } = &ob.outcome {
                lines.push(format!("      {} {}", ansi(BLUE, "note:", color), note,));
            }

            // Extra detail for timeouts
            if let ObligationOutcome::Timeout { timeout_ms } = &ob.outcome {
                lines.push(format!(
                    "      {} after {}ms",
                    ansi(YELLOW, "timed out", color),
                    timeout_ms,
                ));
            }
        }
        lines.push(String::new());
    }

    // Summary line
    let s = &report.summary;
    let proved_str = if s.total_proved > 0 {
        ansi(GREEN, &format!("{} proved", s.total_proved), color)
    } else {
        format!("{} proved", s.total_proved)
    };
    let runtime_checked_str = if s.total_runtime_checked > 0 {
        ansi(BLUE, &format!("{} runtime-checked", s.total_runtime_checked), color)
    } else {
        format!("{} runtime-checked", s.total_runtime_checked)
    };
    let failed_str = if s.total_failed > 0 {
        ansi(RED, &format!("{} failed", s.total_failed), color)
    } else {
        format!("{} failed", s.total_failed)
    };
    let pending_str = if s.total_unknown > 0 {
        ansi(YELLOW, &format!("{} pending", s.total_unknown), color)
    } else {
        format!("{} pending", s.total_unknown)
    };
    lines.push(format!("{}, {}, {}, {}", proved_str, runtime_checked_str, failed_str, pending_str));

    // Verdict
    let verdict_str = match s.verdict {
        CrateVerdict::Verified => ansi(GREEN, "VERIFIED", color),
        CrateVerdict::RuntimeChecked => ansi(BLUE, "RUNTIME CHECKED", color),
        CrateVerdict::HasViolations => ansi(RED, "HAS VIOLATIONS", color),
        CrateVerdict::Inconclusive => ansi(YELLOW, "INCONCLUSIVE", color),
        CrateVerdict::NoObligations => ansi(DIM, "NO OBLIGATIONS", color),
        _ => "UNKNOWN".to_string(),
    };
    lines.push(format!("Verdict: {}", verdict_str));

    lines.join("\n")
}

#[cfg(test)]
mod tests {
    use trust_types::*;

    use super::*;
    use crate::{SCHEMA_VERSION, TRUST_VERSION, build_json_report};

    /// Helper: build a report with one function containing mixed results.
    fn mixed_report() -> JsonProofReport {
        let results = vec![
            (
                VerificationCondition {
                    kind: VcKind::ArithmeticOverflow {
                        op: BinOp::Add,
                        operand_tys: (Ty::usize(), Ty::usize()),
                    },
                    function: "get_midpoint".to_string(),
                    location: SourceSpan {
                        file: "src/midpoint.rs".to_string(),
                        line_start: 5,
                        col_start: 5,
                        line_end: 5,
                        col_end: 10,
                    },
                    formula: Formula::Bool(true),
                    contract_metadata: None,
                },
                VerificationResult::Failed {
                    solver: "z4".to_string(),
                    time_ms: 3,
                    counterexample: Some(Counterexample::new(vec![
                        ("a".to_string(), CounterexampleValue::Uint(u64::MAX as u128)),
                        ("b".to_string(), CounterexampleValue::Uint(1)),
                    ])),
                },
            ),
            (
                VerificationCondition {
                    kind: VcKind::DivisionByZero,
                    function: "get_midpoint".to_string(),
                    location: SourceSpan {
                        file: "src/midpoint.rs".to_string(),
                        line_start: 5,
                        col_start: 18,
                        line_end: 5,
                        col_end: 23,
                    },
                    formula: Formula::Bool(false),
                    contract_metadata: None,
                },
                VerificationResult::Proved {
                    solver: "z4".to_string(),
                    time_ms: 1,
                    strength: ProofStrength::smt_unsat(), proof_certificate: None,
                solver_warnings: None, },
            ),
            (
                VerificationCondition {
                    kind: VcKind::CastOverflow { from_ty: Ty::usize(), to_ty: Ty::u32() },
                    function: "get_midpoint".to_string(),
                    location: SourceSpan::default(),
                    formula: Formula::Bool(true),
                    contract_metadata: None,
                },
                VerificationResult::Unknown {
                    solver: "z4".to_string(),
                    time_ms: 50,
                    reason: "nonlinear arithmetic".to_string(),
                },
            ),
        ];
        build_json_report("midpoint", &results)
    }

    fn runtime_checked_report() -> JsonProofReport {
        JsonProofReport {
            metadata: ReportMetadata {
                schema_version: SCHEMA_VERSION.to_string(),
                trust_version: TRUST_VERSION.to_string(),
                timestamp: "0".to_string(),
                total_time_ms: 11,
            },
            crate_name: "runtime_checked".to_string(),
            summary: CrateSummary {
                functions_analyzed: 1,
                functions_verified: 0,
                functions_runtime_checked: 1,
                functions_with_violations: 0,
                functions_inconclusive: 0,
                total_obligations: 1,
                total_proved: 0,
                total_runtime_checked: 1,
                total_failed: 0,
                total_unknown: 0,
                verdict: CrateVerdict::RuntimeChecked,
            },
            functions: vec![FunctionProofReport {
                function: "dynamic_check".to_string(),
                summary: FunctionSummary {
                    total_obligations: 1,
                    proved: 0,
                    runtime_checked: 1,
                    failed: 0,
                    unknown: 0,
                    total_time_ms: 11,
                    max_proof_level: Some(ProofLevel::L0Safety),
                    verdict: FunctionVerdict::RuntimeChecked,
                },
                obligations: vec![ObligationReport {
                    description: "runtime safety check".to_string(),
                    kind: "postcondition".to_string(),
                    proof_level: ProofLevel::L0Safety,
                    location: Some(SourceSpan {
                        file: "src/runtime.rs".to_string(),
                        line_start: 10,
                        col_start: 1,
                        line_end: 10,
                        col_end: 12,
                    }),
                    outcome: ObligationOutcome::RuntimeChecked {
                        note: Some("validated by runtime instrumentation".to_string()),
                    },
                    solver: "runtime".to_string(),
                    time_ms: 11,
                    evidence: None,
                }],
            }],
        }
    }

    #[test]
    fn test_terminal_report_basic() {
        let report = mixed_report();
        // Explicitly request color=true for deterministic test
        let output = format_terminal_report_impl(&report, true);

        // Header present
        assert!(output.contains("tRust verification report:"));
        assert!(output.contains("midpoint"));

        // Function name in bold
        assert!(output.contains(&format!("{BOLD}get_midpoint{RESET}")));

        // PROVED in green
        assert!(output.contains(&format!("{GREEN}PROVED [SMT UNSAT]{RESET}")));

        // FAILED in red
        assert!(output.contains(&format!("{RED}FAILED{RESET}")));

        // UNKNOWN in yellow
        assert!(output.contains(&format!("{YELLOW}UNKNOWN{RESET}")));

        // Counterexample detail
        assert!(output.contains("counterexample:"));
        assert!(output.contains("a = 18446744073709551615"));

        // Solver metadata in dim
        assert!(output.contains("z4"));

        // Summary line: "X proved, Y failed, Z pending"
        assert!(output.contains("1 proved"));
        assert!(output.contains("1 failed"));
        assert!(output.contains("1 pending"));
        assert!(output.contains("max level: L0 safety"));

        // Verdict
        assert!(output.contains("Verdict:"));
    }

    #[test]
    fn test_terminal_no_color() {
        let report = mixed_report();
        // Explicitly request color=false (equivalent to NO_COLOR being set)
        let output = format_terminal_report_impl(&report, false);

        // No ANSI escape sequences anywhere
        assert!(
            !output.contains("\x1b["),
            "output should not contain ANSI escape codes when color is disabled"
        );

        // Content still present (plain text)
        assert!(output.contains("PROVED"));
        assert!(output.contains("SMT UNSAT"));
        assert!(output.contains("FAILED"));
        assert!(output.contains("get_midpoint"));
        assert!(output.contains("1 proved"));
        assert!(output.contains("1 failed"));
        assert!(output.contains("1 pending"));
        assert!(output.contains("max level: L0 safety"));
    }

    #[test]
    fn test_terminal_summary_line() {
        // Build a report with known counts: 2 proved, 1 failed, 1 pending
        let results = vec![
            (
                VerificationCondition {
                    kind: VcKind::DivisionByZero,
                    function: "f1".to_string(),
                    location: SourceSpan::default(),
                    formula: Formula::Bool(false),
                    contract_metadata: None,
                },
                VerificationResult::Proved {
                    solver: "z4".to_string(),
                    time_ms: 1,
                    strength: ProofStrength::smt_unsat(), proof_certificate: None,
                solver_warnings: None, },
            ),
            (
                VerificationCondition {
                    kind: VcKind::ArithmeticOverflow {
                        op: BinOp::Add,
                        operand_tys: (Ty::u32(), Ty::u32()),
                    },
                    function: "f1".to_string(),
                    location: SourceSpan::default(),
                    formula: Formula::Bool(false),
                    contract_metadata: None,
                },
                VerificationResult::Proved {
                    solver: "z4".to_string(),
                    time_ms: 2,
                    strength: ProofStrength::smt_unsat(), proof_certificate: None,
                solver_warnings: None, },
            ),
            (
                VerificationCondition {
                    kind: VcKind::IndexOutOfBounds,
                    function: "f2".to_string(),
                    location: SourceSpan::default(),
                    formula: Formula::Bool(true),
                    contract_metadata: None,
                },
                VerificationResult::Failed {
                    solver: "z4".to_string(),
                    time_ms: 5,
                    counterexample: None,
                },
            ),
            (
                VerificationCondition {
                    kind: VcKind::Postcondition,
                    function: "f3".to_string(),
                    location: SourceSpan::default(),
                    formula: Formula::Bool(true),
                    contract_metadata: None,
                },
                VerificationResult::Timeout { solver: "z4".to_string(), timeout_ms: 5000 },
            ),
        ];
        let report = build_json_report("counts", &results);
        // Use color=false so we can match exact text without ANSI codes
        let output = format_terminal_report_impl(&report, false);

        // Verify the exact counts in the summary line
        assert!(output.contains("2 proved"), "expected '2 proved' in output:\n{output}");
        assert!(output.contains("1 failed"), "expected '1 failed' in output:\n{output}");
        assert!(output.contains("1 pending"), "expected '1 pending' in output:\n{output}");
        assert!(output.contains("max level: L0 safety"));
    }

    #[test]
    fn test_terminal_runtime_checked_status() {
        let report = runtime_checked_report();
        let output = format_terminal_report_impl(&report, false);

        assert!(output.contains("RUNTIME CHECKED"));
        assert!(output.contains("1 runtime-checked"));
        assert!(output.contains("validated by runtime instrumentation"));
        assert!(output.contains("Verdict: RUNTIME CHECKED"));
    }
}
