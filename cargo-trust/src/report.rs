// cargo-trust report: verification report rendering
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::path::Path;

use serde::Serialize;
use trust_types::{
    Formula, SourceSpan, VcKind,
    VerificationCondition as TrustVc,
    VerificationResult as TrustVr,
    ProofStrength,
};

use crate::types::{OutputFormat, VerificationOutcome, VerificationResult};

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
                let html = trust_report::html_report::generate_html_report(&trust_report);
                println!("{html}");
            }
        }

        // tRust #531: Write report files to --report-dir if specified.
        if let Some(dir) = report_dir {
            let output_dir = Path::new(dir);
            if let Err(e) = trust_report::write_json_report(&trust_report, output_dir) {
                eprintln!("cargo-trust: failed to write JSON report: {e}");
            } else {
                eprintln!("cargo-trust: wrote {}/report.json", dir);
            }
            if let Err(e) = trust_report::write_ndjson_report(&trust_report, output_dir) {
                eprintln!("cargo-trust: failed to write NDJSON report: {e}");
            } else {
                eprintln!("cargo-trust: wrote {}/report.ndjson", dir);
            }
            let html = trust_report::html_report::generate_html_report(&trust_report);
            let html_path = output_dir.join("report.html");
            if let Err(e) = std::fs::create_dir_all(output_dir)
                .and_then(|()| std::fs::write(&html_path, &html))
            {
                eprintln!("cargo-trust: failed to write HTML report: {e}");
            } else {
                eprintln!("cargo-trust: wrote {}", html_path.display());
            }
        }
    }

    fn render_terminal(&self) {
        eprintln!();
        eprintln!("=== tRust Verification Report ===");
        eprintln!(
            "Level: {} | Timeout: {}ms | Duration: {}ms",
            self.config.level, self.config.timeout_ms, self.duration_ms
        );
        eprintln!();

        if self.results.is_empty() {
            eprintln!("  No verification obligations found.");
        } else {
            for result in &self.results {
                let icon = match result.outcome {
                    VerificationOutcome::Proved => "PROVED",
                    VerificationOutcome::Failed => "FAILED",
                    VerificationOutcome::Unknown => "UNKNOWN",
                };
                let time_str = result
                    .time_ms
                    .map(|ms| format!(" ({}, {}ms)", result.backend, ms))
                    .unwrap_or_default();
                eprintln!(
                    "  [{icon}] [{}] {}{time_str}",
                    result.kind, result.message
                );
            }
        }

        eprintln!();
        eprintln!(
            "Summary: {} proved, {} failed, {} unknown ({} total)",
            self.proved, self.failed, self.unknown, self.total
        );
        let status = if self.success { "PASS" } else { "FAIL" };
        eprintln!("Result: {status}");
        eprintln!("=================================");
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
                    function: r.kind.clone(),
                    location: SourceSpan::default(),
                    formula: Formula::Bool(true),
                    contract_metadata: None,
                };
                let vr = match r.outcome {
                    VerificationOutcome::Proved => TrustVr::Proved {
                        solver: r.backend.clone(),
                        time_ms: r.time_ms.unwrap_or(0),
                        strength: ProofStrength::smt_unsat(),
                        proof_certificate: None,
                        solver_warnings: None,
                    },
                    VerificationOutcome::Failed => TrustVr::Failed {
                        solver: r.backend.clone(),
                        time_ms: r.time_ms.unwrap_or(0),
                        counterexample: None,
                    },
                    VerificationOutcome::Unknown => TrustVr::Unknown {
                        solver: r.backend.clone(),
                        time_ms: r.time_ms.unwrap_or(0),
                        reason: "unknown".to_string(),
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
        _ => VcKind::Assertion {
            message: kind.to_string(),
        },
    }
}

/// Minimal HTML escaping for report output.
#[allow(dead_code)] // Used in tests; available for future HTML diff output.
pub(crate) fn html_escape(s: &str) -> String {
    s.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('"', "&quot;")
}
