use std::path::Path;

use crate::cli::parse_subcommand_args;
use crate::config::TrustConfig;
use crate::pipeline::{has_edition, level_to_num, merged_rustflags};
use crate::report::html_escape;
use crate::types::{OutputFormat, VerificationOutcome, VerificationResult, parse_trust_note};
use crate::report::{ReportConfig, VerificationReport};

// -- Argument parsing tests --

#[test]
fn test_parse_args_default_format() {
    let args: Vec<String> = vec![];
    let result = parse_subcommand_args(&args).expect("should parse empty args");
    assert_eq!(result.format, OutputFormat::Terminal);
    assert!(!result.is_single_file);
    assert!(result.passthrough.is_empty());
}

#[test]
fn test_parse_args_format_json() {
    let args: Vec<String> = vec!["--format".into(), "json".into()];
    let result = parse_subcommand_args(&args).expect("should parse --format json");
    assert_eq!(result.format, OutputFormat::Json);
    assert!(result.passthrough.is_empty());
}

#[test]
fn test_parse_args_format_equals() {
    let args: Vec<String> = vec!["--format=html".into()];
    let result = parse_subcommand_args(&args).expect("should parse --format=html");
    assert_eq!(result.format, OutputFormat::Html);
}

#[test]
fn test_parse_args_invalid_format() {
    let args: Vec<String> = vec!["--format".into(), "csv".into()];
    assert!(parse_subcommand_args(&args).is_err());
}

#[test]
fn test_parse_args_single_file() {
    let args: Vec<String> = vec!["test.rs".into()];
    let result = parse_subcommand_args(&args).expect("should parse single file");
    assert!(result.is_single_file);
    assert_eq!(result.passthrough, vec!["test.rs"]);
}

#[test]
fn test_parse_args_passthrough_with_format() {
    let args: Vec<String> = vec![
        "--format".into(),
        "json".into(),
        "--release".into(),
    ];
    let result = parse_subcommand_args(&args).expect("should parse mixed args");
    assert_eq!(result.format, OutputFormat::Json);
    assert_eq!(result.passthrough, vec!["--release"]);
}

// -- Rewrite flag parsing tests --

#[test]
fn test_parse_args_rewrite_flag() {
    let args: Vec<String> = vec!["--rewrite".into()];
    let result = parse_subcommand_args(&args).expect("should parse --rewrite");
    assert!(result.rewrite);
    assert_eq!(result.max_iterations, 10); // default
}

#[test]
fn test_parse_args_rewrite_with_max_iterations() {
    let args: Vec<String> = vec![
        "--rewrite".into(),
        "--max-iterations".into(),
        "5".into(),
    ];
    let result = parse_subcommand_args(&args).expect("should parse --rewrite --max-iterations 5");
    assert!(result.rewrite);
    assert_eq!(result.max_iterations, 5);
}

#[test]
fn test_parse_args_max_iterations_equals() {
    let args: Vec<String> = vec!["--max-iterations=3".into()];
    let result = parse_subcommand_args(&args).expect("should parse --max-iterations=3");
    assert_eq!(result.max_iterations, 3);
}

#[test]
fn test_parse_args_max_iterations_zero_fails() {
    let args: Vec<String> = vec!["--max-iterations".into(), "0".into()];
    assert!(parse_subcommand_args(&args).is_err());
}

#[test]
fn test_parse_args_max_iterations_invalid_fails() {
    let args: Vec<String> = vec!["--max-iterations".into(), "abc".into()];
    assert!(parse_subcommand_args(&args).is_err());
}

#[test]
fn test_parse_args_no_rewrite_by_default() {
    let args: Vec<String> = vec!["--format".into(), "json".into()];
    let result = parse_subcommand_args(&args).expect("should parse without --rewrite");
    assert!(!result.rewrite);
}

#[test]
fn test_parse_args_fresh_flag() {
    let args: Vec<String> = vec!["--fresh".into()];
    let result = parse_subcommand_args(&args).expect("should parse --fresh");
    assert!(result.fresh);
}

#[test]
fn test_parse_args_no_fresh_by_default() {
    let args: Vec<String> = vec![];
    let result = parse_subcommand_args(&args).expect("should parse without --fresh");
    assert!(!result.fresh);
}

// -- Baseline argument parsing tests --

#[test]
fn test_parse_args_baseline_flag() {
    let args: Vec<String> = vec!["--baseline".into(), "report.json".into()];
    let result = parse_subcommand_args(&args).expect("should parse --baseline");
    assert_eq!(result.baseline.as_deref(), Some("report.json"));
}

#[test]
fn test_parse_args_baseline_equals() {
    let args: Vec<String> = vec!["--baseline=/tmp/base.json".into()];
    let result = parse_subcommand_args(&args).expect("should parse --baseline=path");
    assert_eq!(result.baseline.as_deref(), Some("/tmp/base.json"));
}

#[test]
fn test_parse_args_baseline_missing_value() {
    let args: Vec<String> = vec!["--baseline".into()];
    assert!(parse_subcommand_args(&args).is_err());
}

#[test]
fn test_parse_args_no_baseline_by_default() {
    let args: Vec<String> = vec!["test.rs".into()];
    let result = parse_subcommand_args(&args).expect("should parse without --baseline");
    assert!(result.baseline.is_none());
}

#[test]
fn test_parse_args_baseline_with_format_and_file() {
    let args: Vec<String> = vec![
        "test.rs".into(),
        "--baseline".into(),
        "base.json".into(),
        "--format".into(),
        "json".into(),
    ];
    let result = parse_subcommand_args(&args).expect("should parse combined args");
    assert_eq!(result.baseline.as_deref(), Some("base.json"));
    assert_eq!(result.format, OutputFormat::Json);
    assert!(result.is_single_file);
    assert_eq!(result.passthrough, vec!["test.rs"]);
}

// -- Current flag parsing tests (tRust #625) --

#[test]
fn test_parse_args_current_flag() {
    let args: Vec<String> = vec!["--current".into(), "current.json".into()];
    let result = parse_subcommand_args(&args).expect("should parse --current");
    assert_eq!(result.current.as_deref(), Some("current.json"));
}

#[test]
fn test_parse_args_current_equals() {
    let args: Vec<String> = vec!["--current=/tmp/cur.json".into()];
    let result = parse_subcommand_args(&args).expect("should parse --current=path");
    assert_eq!(result.current.as_deref(), Some("/tmp/cur.json"));
}

#[test]
fn test_parse_args_current_missing_value() {
    let args: Vec<String> = vec!["--current".into()];
    assert!(parse_subcommand_args(&args).is_err());
}

#[test]
fn test_parse_args_no_current_by_default() {
    let args: Vec<String> = vec!["test.rs".into()];
    let result = parse_subcommand_args(&args).expect("should parse without --current");
    assert!(result.current.is_none());
}

#[test]
fn test_parse_args_baseline_and_current() {
    let args: Vec<String> = vec![
        "--baseline".into(),
        "base.json".into(),
        "--current".into(),
        "cur.json".into(),
        "--format".into(),
        "json".into(),
    ];
    let result = parse_subcommand_args(&args).expect("should parse combined args");
    assert_eq!(result.baseline.as_deref(), Some("base.json"));
    assert_eq!(result.current.as_deref(), Some("cur.json"));
    assert_eq!(result.format, OutputFormat::Json);
}

// -- tRust note parsing tests --

#[test]
fn test_parse_trust_note_proved_em_dash() {
    let line = "note: tRust [overflow:add]: arithmetic overflow (Add) \u{2014} PROVED (z4-smtlib, 8ms)";
    let result = parse_trust_note(line).expect("should parse proved note");
    assert_eq!(result.kind, "overflow:add");
    assert_eq!(result.message, "arithmetic overflow (Add)");
    assert_eq!(result.outcome, VerificationOutcome::Proved);
    assert_eq!(result.backend, "z4-smtlib");
    assert_eq!(result.time_ms, Some(8));
}

#[test]
fn test_parse_trust_note_failed_ascii_dash() {
    let line = "note: tRust [overflow:add]: arithmetic overflow (Add) -- FAILED (z4-smtlib, 12ms)";
    let result = parse_trust_note(line).expect("should parse failed note");
    assert_eq!(result.kind, "overflow:add");
    assert_eq!(result.message, "arithmetic overflow (Add)");
    assert_eq!(result.outcome, VerificationOutcome::Failed);
    assert_eq!(result.backend, "z4-smtlib");
    assert_eq!(result.time_ms, Some(12));
}

#[test]
fn test_parse_trust_note_div_by_zero() {
    let line = "note: tRust [div_by_zero]: division by zero (Div) -- PROVED (z4-smtlib, 3ms)";
    let result = parse_trust_note(line).expect("should parse div note");
    assert_eq!(result.kind, "div_by_zero");
    assert_eq!(result.outcome, VerificationOutcome::Proved);
    assert_eq!(result.time_ms, Some(3));
}

#[test]
fn test_parse_trust_note_no_time() {
    let line = "note: tRust [bounds]: array index out of bounds -- PROVED (mock)";
    let result = parse_trust_note(line).expect("should parse note without time");
    assert_eq!(result.kind, "bounds");
    assert_eq!(result.outcome, VerificationOutcome::Proved);
    assert_eq!(result.backend, "mock");
    assert_eq!(result.time_ms, None);
}

#[test]
fn test_parse_trust_note_not_a_trust_line() {
    assert!(parse_trust_note("error[E0308]: mismatched types").is_none());
    assert!(parse_trust_note("warning: unused variable").is_none());
    assert!(parse_trust_note("").is_none());
}

#[test]
fn test_parse_trust_note_with_prefix_whitespace() {
    let line = "   note: tRust [overflow:add]: msg -- PROVED (z4-smtlib, 1ms)";
    let result = parse_trust_note(line).expect("should parse with leading spaces");
    assert_eq!(result.outcome, VerificationOutcome::Proved);
}

// -- Config tests --

#[test]
fn test_trust_config_default() {
    let config = TrustConfig::default();
    assert!(config.enabled);
    assert_eq!(config.level, "L0");
    assert_eq!(config.timeout_ms, 5000);
}

#[test]
fn test_trust_config_load_nonexistent() {
    let config = TrustConfig::load(Path::new("/nonexistent/path"));
    assert!(config.enabled);
    assert_eq!(config.level, "L0");
}

// -- Utility tests --

#[test]
fn test_level_to_num() {
    assert_eq!(level_to_num("L0"), 0);
    assert_eq!(level_to_num("L1"), 1);
    assert_eq!(level_to_num("L2"), 2);
    assert_eq!(level_to_num("unknown"), 0);
}

#[test]
fn test_merged_rustflags_empty_env() {
    let _saved = std::env::var("RUSTFLAGS").ok();
    std::env::remove_var("RUSTFLAGS");
    let flags = merged_rustflags("L1");
    assert!(flags.contains("-Z trust-verify"));
    assert!(flags.contains("trust-verify-level=1"));
}

#[test]
fn test_html_escape() {
    assert_eq!(html_escape("<b>test</b>"), "&lt;b&gt;test&lt;/b&gt;");
    assert_eq!(html_escape("a & b"), "a &amp; b");
}

#[test]
fn test_output_format_from_str() {
    assert_eq!(
        OutputFormat::from_str("terminal").unwrap(),
        OutputFormat::Terminal
    );
    assert_eq!(
        OutputFormat::from_str("json").unwrap(),
        OutputFormat::Json
    );
    assert_eq!(
        OutputFormat::from_str("html").unwrap(),
        OutputFormat::Html
    );
    assert!(OutputFormat::from_str("csv").is_err());
}

#[test]
fn test_has_edition() {
    assert!(has_edition(&["--edition".into(), "2021".into()]));
    assert!(has_edition(&["--edition=2024".into()]));
    assert!(!has_edition(&["--release".into()]));
}

#[test]
fn test_report_json_serialization() {
    let report = VerificationReport {
        success: true,
        exit_code: 0,
        proved: 1,
        failed: 0,
        unknown: 0,
        total: 1,
        results: vec![VerificationResult {
            kind: "overflow:add".into(),
            message: "arithmetic overflow".into(),
            outcome: VerificationOutcome::Proved,
            backend: "z4-smtlib".into(),
            time_ms: Some(8),
            raw_line: "note: tRust [overflow:add]: arithmetic overflow -- PROVED (z4-smtlib, 8ms)".into(),
        }],
        compiler_diagnostics: vec![],
        duration_ms: 42,
        config: ReportConfig {
            level: "L0".into(),
            timeout_ms: 5000,
            enabled: true,
        },
    };
    let json = serde_json::to_string(&report).expect("should serialize report");
    assert!(json.contains("\"success\":true"));
    assert!(json.contains("\"proved\":1"));
    assert!(json.contains("overflow:add"));
}

#[test]
fn test_report_success_logic() {
    // No failures, compiler exit 0 => success
    let report = VerificationReport {
        success: true,
        exit_code: 0,
        proved: 2,
        failed: 0,
        unknown: 0,
        total: 2,
        results: vec![],
        compiler_diagnostics: vec![],
        duration_ms: 10,
        config: ReportConfig {
            level: "L0".into(),
            timeout_ms: 5000,
            enabled: true,
        },
    };
    assert!(report.success);

    // Has failures => not success even with exit 0
    let report2 = VerificationReport {
        success: false,
        exit_code: 0,
        proved: 1,
        failed: 1,
        unknown: 0,
        total: 2,
        results: vec![],
        compiler_diagnostics: vec![],
        duration_ms: 10,
        config: ReportConfig {
            level: "L0".into(),
            timeout_ms: 5000,
            enabled: true,
        },
    };
    assert!(!report2.success);
}

// -- Solver flag parsing tests (tRust #579) --

#[test]
fn test_parse_args_solver_flag() {
    let args: Vec<String> = vec!["--solver".into(), "z4".into()];
    let result = parse_subcommand_args(&args).expect("should parse --solver z4");
    assert_eq!(result.solver.as_deref(), Some("z4"));
}

#[test]
fn test_parse_args_solver_equals() {
    let args: Vec<String> = vec!["--solver=zani".into()];
    let result = parse_subcommand_args(&args).expect("should parse --solver=zani");
    assert_eq!(result.solver.as_deref(), Some("zani"));
}

#[test]
fn test_parse_args_solver_unknown_fails() {
    let args: Vec<String> = vec!["--solver".into(), "nonexistent".into()];
    assert!(parse_subcommand_args(&args).is_err());
}

#[test]
fn test_parse_args_solver_missing_value() {
    let args: Vec<String> = vec!["--solver".into()];
    assert!(parse_subcommand_args(&args).is_err());
}

#[test]
fn test_parse_args_no_solver_by_default() {
    let args: Vec<String> = vec!["test.rs".into()];
    let result = parse_subcommand_args(&args).expect("should parse without --solver");
    assert!(result.solver.is_none());
}

#[test]
fn test_parse_args_solver_with_format() {
    let args: Vec<String> = vec![
        "--solver".into(),
        "sunder".into(),
        "--format".into(),
        "json".into(),
        "test.rs".into(),
    ];
    let result = parse_subcommand_args(&args).expect("should parse combined args");
    assert_eq!(result.solver.as_deref(), Some("sunder"));
    assert_eq!(result.format, OutputFormat::Json);
    assert!(result.is_single_file);
}

#[test]
fn test_parse_args_all_known_solvers() {
    for name in &["z4", "zani", "sunder", "certus", "tla2", "lean5"] {
        let args: Vec<String> = vec!["--solver".into(), name.to_string()];
        let result = parse_subcommand_args(&args)
            .unwrap_or_else(|_| panic!("should parse --solver {name}"));
        assert_eq!(result.solver.as_deref(), Some(*name));
    }
}
