// trust-debug/report.rs: Security-focused violation report formatting
//
// Produces human-readable and machine-readable reports from debug analysis
// results. Formats violations with severity, data flow paths, exploitation
// chains, and remediation guidance.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::{DebugReport, ExploitChain, SecurityViolation, SecurityViolationKind, Severity};
use std::fmt::Write;

/// Format a debug report as a terminal-friendly string.
pub(crate) fn format_terminal(report: &DebugReport) -> String {
    let mut out = String::new();

    // Header
    let _ = writeln!(out, 
        "=== trust-debug report: {} ===",
        report.target
    );
    let _ = writeln!(out, 
        "Functions analyzed: {} | VCs generated: {} | VCs checked: {}",
        report.summary.functions_analyzed,
        report.summary.total_vcs_generated,
        report.summary.total_vcs_checked,
    );
    let _ = writeln!(out, 
        "Violations: {} (Critical: {}, High: {}, Medium: {}, Low: {}, Info: {})",
        report.summary.violations_found,
        report.summary.critical_count,
        report.summary.high_count,
        report.summary.medium_count,
        report.summary.low_count,
        report.summary.info_count,
    );
    if !report.chains.is_empty() {
        let _ = writeln!(out, 
            "Exploitation chains: {}",
            report.summary.chains_found,
        );
    }
    out.push('\n');

    // Exploitation chains first (most actionable)
    if !report.chains.is_empty() {
        out.push_str("--- EXPLOITATION CHAINS ---\n\n");
        for chain in &report.chains {
            out.push_str(&format_chain(chain));
            out.push('\n');
        }
    }

    // Violations by severity
    if !report.violations.is_empty() {
        out.push_str("--- VIOLATIONS ---\n\n");
        for violation in &report.violations {
            out.push_str(&format_violation(violation));
            out.push('\n');
        }
    }

    // Time
    let _ = writeln!(out, 
        "Total analysis time: {}ms",
        report.summary.total_time_ms
    );

    out
}

fn format_violation(v: &SecurityViolation) -> String {
    let mut out = String::new();

    let severity_tag = match v.severity {
        Severity::Critical => "[CRITICAL]",
        Severity::High => "[HIGH]    ",
        Severity::Medium => "[MEDIUM]  ",
        Severity::Low => "[LOW]     ",
        Severity::Info => "[INFO]    ",
    };

    let _ = writeln!(out, "{} {} {}", v.id, severity_tag, kind_label(&v.kind));

    if let Some(loc) = &v.location {
        let _ = writeln!(out, "  at {}:{}:{}", loc.file, loc.line_start, loc.col_start);
    }
    let _ = writeln!(out, "  in {}", v.function);
    let _ = writeln!(out, "  {}", v.description);

    if !v.flow_path.is_empty() {
        out.push_str("  Flow path:\n");
        for step in &v.flow_path {
            let _ = writeln!(out, 
                "    local_{} (bb{}) {}",
                step.local, step.block, step.description
            );
        }
    }

    let _ = writeln!(out, "  Solver: {} ({}ms)", v.solver, v.time_ms);

    out
}

fn format_chain(chain: &ExploitChain) -> String {
    let severity_tag = match chain.severity {
        Severity::Critical => "[CRITICAL]",
        Severity::High => "[HIGH]    ",
        Severity::Medium => "[MEDIUM]  ",
        Severity::Low => "[LOW]     ",
        Severity::Info => "[INFO]    ",
    };

    let mut out = format!("{} Chain: {}\n", severity_tag, chain.name);
    let _ = writeln!(out, "  {}", chain.description);
    let _ = writeln!(out, "  Composed from: {}", chain.violation_ids.join(" → "));
    out
}

fn kind_label(kind: &SecurityViolationKind) -> &'static str {
    match kind {
        SecurityViolationKind::TaintedIndirectCall { .. } => "Tainted Indirect Call",
        SecurityViolationKind::TaintedSyscall { .. } => "Tainted Syscall",
        SecurityViolationKind::FormatStringInjection { .. } => "Format String Injection",
        SecurityViolationKind::SqlInjection { .. } => "SQL Injection",
        SecurityViolationKind::CommandInjection { .. } => "Command Injection",
        SecurityViolationKind::BufferOverflow { .. } => "Buffer Overflow",
        SecurityViolationKind::IntegerOverflowToBufferCorruption { .. } => "Integer Overflow → Buffer Corruption",
        SecurityViolationKind::UseAfterFree { .. } => "Use-After-Free",
        SecurityViolationKind::DoubleFree { .. } => "Double-Free",
        SecurityViolationKind::ArbitraryWrite { .. } => "Arbitrary Write",
        SecurityViolationKind::Toctou { .. } => "TOCTOU Race",
        SecurityViolationKind::Deadlock { .. } => "Deadlock",
        SecurityViolationKind::DataRace { .. } => "Data Race",
        SecurityViolationKind::ArithmeticOverflow { .. } => "Arithmetic Overflow",
        SecurityViolationKind::DivisionByZero => "Division by Zero",
        SecurityViolationKind::IndexOutOfBounds { .. } => "Index Out of Bounds",
        SecurityViolationKind::UnreachableReached => "Unreachable Reached",
        SecurityViolationKind::TaintFlow { .. } => "Taint Flow",
        SecurityViolationKind::DeadCode { .. } => "Dead Code",
        SecurityViolationKind::PrivilegeEscalation { .. } => "Privilege Escalation",
    }
}

/// Format a debug report as JSON for machine consumption.
pub(crate) fn format_json(report: &DebugReport) -> String {
    serde_json::to_string_pretty(report).unwrap_or_else(|e| {
        format!("{{\"error\": \"serialization failed: {e}\"}}")
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::DebugSummary;

    fn sample_report() -> DebugReport {
        DebugReport {
            target: "test-binary".to_string(),
            violations: vec![
                SecurityViolation {
                    id: "V0001".to_string(),
                    severity: Severity::Critical,
                    kind: SecurityViolationKind::SqlInjection {
                        sink_func: "db::query".to_string(),
                        taint_source: "user-input".to_string(),
                    },
                    function: "handler::process".to_string(),
                    location: Some(trust_types::SourceSpan {
                        file: "src/handler.rs".into(),
                        line_start: 42,
                        col_start: 5,
                        line_end: 42,
                        col_end: 30,
                    }),
                    description: "User input reaches SQL query without sanitization".to_string(),
                    flow_path: vec![],
                    counterexample: None,
                    solver: "taint-analysis".to_string(),
                    time_ms: 12,
                },
                SecurityViolation {
                    id: "V0002".to_string(),
                    severity: Severity::Medium,
                    kind: SecurityViolationKind::ArithmeticOverflow {
                        operation: "Add".to_string(),
                    },
                    function: "math::midpoint".to_string(),
                    location: None,
                    description: "a + b may overflow".to_string(),
                    flow_path: vec![],
                    counterexample: None,
                    solver: "z4".to_string(),
                    time_ms: 5,
                },
            ],
            chains: vec![],
            summary: DebugSummary {
                functions_analyzed: 10,
                total_vcs_generated: 42,
                total_vcs_checked: 42,
                violations_found: 2,
                critical_count: 1,
                high_count: 0,
                medium_count: 1,
                low_count: 0,
                info_count: 0,
                chains_found: 0,
                total_time_ms: 17,
            },
        }
    }

    #[test]
    fn test_format_terminal_includes_header() {
        let output = format_terminal(&sample_report());
        assert!(output.contains("trust-debug report: test-binary"));
        assert!(output.contains("Functions analyzed: 10"));
        assert!(output.contains("Critical: 1"));
    }

    #[test]
    fn test_format_terminal_includes_violations() {
        let output = format_terminal(&sample_report());
        assert!(output.contains("[CRITICAL]"));
        assert!(output.contains("SQL Injection"));
        assert!(output.contains("src/handler.rs:42:5"));
        assert!(output.contains("[MEDIUM]"));
        assert!(output.contains("Arithmetic Overflow"));
    }

    #[test]
    fn test_format_json_roundtrip() {
        let report = sample_report();
        let json = format_json(&report);
        let parsed: DebugReport = serde_json::from_str(&json).expect("should parse");
        assert_eq!(parsed.target, "test-binary");
        assert_eq!(parsed.violations.len(), 2);
    }

    #[test]
    fn test_format_empty_report() {
        let report = DebugReport {
            target: "empty".to_string(),
            violations: vec![],
            chains: vec![],
            summary: DebugSummary::from_violations(&[], &[]),
        };
        let output = format_terminal(&report);
        assert!(output.contains("Violations: 0"));
        assert!(!output.contains("--- VIOLATIONS ---"));
    }
}
