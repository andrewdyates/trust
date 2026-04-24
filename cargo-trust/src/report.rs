// cargo-trust report: verification report rendering
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::path::{Path, PathBuf};

use serde::Serialize;
use trust_types::{
    Formula, ProofStrength, SourceSpan, VcKind, VerificationCondition as TrustVc,
    VerificationResult as TrustVr,
};

use crate::types::{OutputFormat, VerificationOutcome, VerificationResult};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ReportArtifact {
    Json,
    Ndjson,
    Html,
}

impl ReportArtifact {
    fn file_name(self) -> &'static str {
        match self {
            Self::Json => "report.json",
            Self::Ndjson => "report.ndjson",
            Self::Html => "report.html",
        }
    }

    fn write_label(self) -> &'static str {
        match self {
            Self::Json => "JSON report",
            Self::Ndjson => "NDJSON report",
            Self::Html => "HTML report",
        }
    }
}

/// A non-verification diagnostic line captured from compiler output.
#[derive(Debug, Clone, Serialize)]
pub(crate) struct CompilerDiagnostic {
    pub(crate) level: String,
    pub(crate) message: String,
}

/// Config info included in the report.
#[derive(Debug, Clone, Serialize)]
pub(crate) struct ReportConfig {
    pub(crate) level: String,
    pub(crate) timeout_ms: u64,
    pub(crate) enabled: bool,
}

/// Summary report of a verification run.
#[derive(Debug, Clone, Serialize)]
pub(crate) struct VerificationReport {
    pub(crate) success: bool,
    pub(crate) exit_code: i32,
    pub(crate) proved: usize,
    pub(crate) failed: usize,
    pub(crate) unknown: usize,
    pub(crate) runtime_checked: usize,
    pub(crate) total: usize,
    pub(crate) results: Vec<VerificationResult>,
    pub(crate) compiler_diagnostics: Vec<CompilerDiagnostic>,
    pub(crate) duration_ms: u64,
    pub(crate) config: ReportConfig,
}

impl VerificationReport {
    pub(crate) fn render(&self, format: OutputFormat, report_dir: Option<&str>) {
        // tRust #531: Delegate JSON and HTML to trust-report for parallel reporting.
        let trust_report = self.to_trust_report();
        let html_report = (matches!(format, OutputFormat::Html) || report_dir.is_some())
            .then(|| trust_report::html_report::generate_html_report(&trust_report));

        match format {
            OutputFormat::Terminal => {
                self.render_terminal();
                // Also print the trust-report text summary for richer output.
                eprintln!();
                eprintln!("{}", trust_report::format_json_summary(&trust_report));
            }
            OutputFormat::Json => {
                // tRust #531: Use trust-report canonical JSON format.
                match serde_json::to_string_pretty(&trust_report) {
                    Ok(json) => println!("{json}"),
                    Err(e) => eprintln!("cargo-trust: failed to serialize report: {e}"),
                }
            }
            OutputFormat::Html => {
                // tRust #531: Use trust-report HTML generator with dashboard.
                println!(
                    "{}",
                    html_report
                        .as_deref()
                        .expect("HTML output should be rendered when format=html")
                );
            }
        }

        // tRust #531: Write report files to --report-dir if specified.
        if let Some(dir) = report_dir {
            write_report_artifacts(
                &trust_report,
                Path::new(dir),
                html_report
                    .as_deref()
                    .expect("HTML report should be rendered when writing report artifacts"),
            );
        }
    }

    fn render_terminal(&self) {
        for line in self.terminal_lines() {
            eprintln!("{line}");
        }
    }

    fn terminal_lines(&self) -> Vec<String> {
        let mut lines = Vec::with_capacity(self.results.len() + 8);
        lines.push(String::new());
        lines.push("=== tRust Verification Report ===".to_string());
        lines.push(format!(
            "Level: {} | Timeout: {}ms | Duration: {}ms",
            self.config.level, self.config.timeout_ms, self.duration_ms
        ));
        lines.push(String::new());

        if self.results.is_empty() {
            lines.push("  No verification obligations found.".to_string());
        } else {
            lines.extend(self.results.iter().map(terminal_result_line));
        }

        lines.push(String::new());
        lines.push(format!(
            "Summary: {} proved, {} failed, {} runtime-checked, {} inconclusive ({} total)",
            self.proved, self.failed, self.runtime_checked, self.unknown, self.total
        ));
        lines.push(format!("Result: {}", self.terminal_status_label()));
        lines.push("=================================".to_string());
        lines
    }

    fn terminal_status_label(&self) -> &'static str {
        if self.success {
            "PASS"
        } else if self.failed > 0 || self.exit_code != 0 {
            "FAIL"
        } else {
            "INCONCLUSIVE"
        }
    }

    /// Convert cargo-trust parsed results to trust-types pairs and build a
    /// `JsonProofReport` via trust-report.
    ///
    /// tRust #531: This bridges the gap between the lightweight text-parsed
    /// results in cargo-trust and the canonical trust-report JSON format.
    fn to_trust_report(&self) -> trust_types::JsonProofReport {
        let pairs: Vec<(TrustVc, TrustVr)> = self
            .results
            .iter()
            .map(|r| {
                let vc = TrustVc {
                    kind: parse_vc_kind(&r.kind),
                    function: if r.function.is_empty() {
                        r.kind.clone().into()
                    } else {
                        r.function.clone().into()
                    },
                    location: r.location.clone().unwrap_or_else(SourceSpan::default),
                    formula: Formula::Bool(true),
                    contract_metadata: None,
                };
                let vr = match r.outcome {
                    VerificationOutcome::Proved => TrustVr::Proved {
                        solver: r.backend.clone().into(),
                        time_ms: r.time_ms.unwrap_or(0),
                        strength: ProofStrength::smt_unsat(),
                        proof_certificate: None,
                        solver_warnings: None,
                    },
                    VerificationOutcome::Failed => TrustVr::Failed {
                        solver: r.backend.clone().into(),
                        time_ms: r.time_ms.unwrap_or(0),
                        counterexample: r.counterexample.clone(),
                    },
                    VerificationOutcome::RuntimeChecked | VerificationOutcome::Unknown => {
                        TrustVr::Unknown {
                            solver: r.backend.clone().into(),
                            time_ms: r.time_ms.unwrap_or(0),
                            reason: r.reason.clone().unwrap_or_else(|| {
                                "unproved obligation with runtime check".to_string()
                            }),
                        }
                    }
                    VerificationOutcome::Timeout => TrustVr::Timeout {
                        solver: r.backend.clone().into(),
                        timeout_ms: r.time_ms.unwrap_or(0),
                    },
                };
                (vc, vr)
            })
            .collect();
        trust_report::build_json_report("crate", &pairs)
    }
}

/// Parse a VC kind tag string back to a `VcKind`.
///
/// This is a best-effort mapping from the kind strings emitted by the compiler
/// (e.g., "overflow:add", "div_by_zero") to `VcKind` enum variants.
pub(crate) fn parse_vc_kind(kind: &str) -> VcKind {
    match kind {
        "div_by_zero" | "division_by_zero" => VcKind::DivisionByZero,
        "remainder_by_zero" => VcKind::RemainderByZero,
        "index_out_of_bounds" | "bounds" => VcKind::IndexOutOfBounds,
        "slice_bounds_check" => VcKind::SliceBoundsCheck,
        "postcondition" => VcKind::Postcondition,
        "unreachable" => VcKind::Unreachable,
        s if s.starts_with("overflow:") || s.starts_with("arithmetic_overflow") => {
            let op = if s.contains("add") {
                trust_types::BinOp::Add
            } else if s.contains("sub") {
                trust_types::BinOp::Sub
            } else if s.contains("mul") {
                trust_types::BinOp::Mul
            } else {
                trust_types::BinOp::Add
            };
            VcKind::ArithmeticOverflow {
                op,
                operand_tys: (trust_types::Ty::u64(), trust_types::Ty::u64()),
            }
        }
        _ => VcKind::Assertion { message: kind.to_string() },
    }
}

/// Minimal HTML escaping for report output.
#[allow(dead_code)] // Used in tests; available for future HTML diff output.
pub(crate) fn html_escape(s: &str) -> String {
    s.replace('&', "&amp;").replace('<', "&lt;").replace('>', "&gt;").replace('"', "&quot;")
}

fn terminal_result_line(result: &VerificationResult) -> String {
    format!(
        "  [{}] [{}] {}{}",
        result.outcome.label(),
        result.kind,
        result.message,
        terminal_result_detail_suffix(result)
    )
}

fn terminal_result_detail_suffix(result: &VerificationResult) -> String {
    match (display_backend(&result.backend), result.time_ms) {
        (Some(backend), Some(time_ms)) => format!(" ({backend}, {time_ms}ms)"),
        (Some(backend), None) => format!(" ({backend})"),
        (None, Some(time_ms)) => format!(" ({time_ms}ms)"),
        (None, None) => String::new(),
    }
}

fn display_backend(backend: &str) -> Option<&str> {
    let backend = backend.trim();
    (!backend.is_empty() && backend != "unknown").then_some(backend)
}

fn report_artifact_path(output_dir: &Path, artifact: ReportArtifact) -> PathBuf {
    output_dir.join(artifact.file_name())
}

fn write_report_artifacts(
    report: &trust_types::JsonProofReport,
    output_dir: &Path,
    html_report: &str,
) {
    write_report_artifact(output_dir, ReportArtifact::Json, || {
        trust_report::write_json_report(report, output_dir)
    });
    write_report_artifact(output_dir, ReportArtifact::Ndjson, || {
        trust_report::write_ndjson_report(report, output_dir)
    });
    write_report_artifact(output_dir, ReportArtifact::Html, || {
        std::fs::create_dir_all(output_dir)?;
        std::fs::write(report_artifact_path(output_dir, ReportArtifact::Html), html_report)
    });
}

fn write_report_artifact<F>(output_dir: &Path, artifact: ReportArtifact, write: F)
where
    F: FnOnce() -> std::io::Result<()>,
{
    let artifact_path = report_artifact_path(output_dir, artifact);
    match write() {
        Ok(()) => eprintln!("cargo-trust: wrote {}", artifact_path.display()),
        Err(e) => eprintln!("cargo-trust: failed to write {}: {e}", artifact.write_label()),
    }
}
