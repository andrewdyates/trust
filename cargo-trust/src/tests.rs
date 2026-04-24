use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

use super::{
    DoctorBackendSource, DoctorBackendStatus, DoctorCheckReportMode, DoctorCompilerStatus,
    DoctorConfigSourceKind, DoctorConfigStatus, DoctorReport, DoctorSolverStatus, LiftReportInput,
    LiftedTmirFunctionSummary, backend_status, build_lift_report, describe_capability,
    describe_config_source, lift_should_fail, load_doctor_config, parse_lift_entry,
    render_lift_terminal,
};
use crate::cli::{parse_subcommand_args, usage_text};
use crate::config::{DEFAULT_CODEGEN_BACKEND, TrustConfig};
use crate::pipeline::{
    LinkedTrustToolchainStatus, LinkedTrustToolchainStatusKind, NativeRustcDiscovery,
    NativeRustcDiscoverySource, build_native_command, build_native_command_with_json_transport,
    compiler_help_supports_option, has_edition, has_output_path_flag, is_cargo_program,
    level_to_num, merged_rustflags, merged_rustflags_with_backend,
    merged_rustflags_with_json_transport, parse_compiler_stderr, select_native_rustc_discovery,
};
use crate::project_root::resolve_project_root_from;
use crate::report::{ReportConfig, VerificationReport, html_escape, parse_vc_kind};
use crate::types::{
    BinaryLiftStatus, OutputFormat, Subcommand, VerificationOutcome, VerificationResult,
    parse_trust_note, transport_to_verification_result,
};
use trust_types::{BinOp, VcKind};

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
    assert_eq!(result.single_file_path(), Some("test.rs"));
    assert_eq!(result.passthrough, vec!["test.rs"]);
}

#[test]
fn test_parse_args_manifest_path_is_preserved_for_passthrough() {
    let args: Vec<String> =
        vec!["--manifest-path".into(), "demo/Cargo.toml".into(), "--release".into()];
    let result = parse_subcommand_args(&args).expect("should parse --manifest-path");
    assert_eq!(result.manifest_path.as_deref(), Some("demo/Cargo.toml"));
    assert!(!result.is_single_file);
    assert_eq!(result.passthrough, vec!["--manifest-path", "demo/Cargo.toml", "--release"]);
}

#[test]
fn test_parse_args_passthrough_with_format() {
    let args: Vec<String> = vec!["--format".into(), "json".into(), "--release".into()];
    let result = parse_subcommand_args(&args).expect("should parse mixed args");
    assert_eq!(result.format, OutputFormat::Json);
    assert_eq!(result.passthrough, vec!["--release"]);
}

#[test]
fn test_parse_args_lift_options() {
    let args: Vec<String> = vec![
        "demo.bin".into(),
        "--entry".into(),
        "0x401000".into(),
        "--json".into(),
        "--strict".into(),
    ];
    let result = parse_subcommand_args(&args).expect("should parse lift args");
    assert_eq!(result.passthrough, vec!["demo.bin"]);
    assert_eq!(result.entry.as_deref(), Some("0x401000"));
    assert_eq!(result.format, OutputFormat::Json);
    assert!(!result.all_functions);
    assert!(result.strict);
}

#[test]
fn test_parse_args_lift_all_functions() {
    let args: Vec<String> = vec!["demo.bin".into(), "--all".into(), "--allow-unsupported".into()];
    let result = parse_subcommand_args(&args).expect("should parse lift --all");
    assert_eq!(result.passthrough, vec!["demo.bin"]);
    assert!(result.all_functions);
    assert!(!result.strict);
}

#[test]
fn test_parse_args_lift_allow_unsupported_overrides_strict() {
    let args: Vec<String> =
        vec!["demo.bin".into(), "--strict".into(), "--allow-unsupported".into()];
    let result = parse_subcommand_args(&args).expect("should parse lift strictness");
    assert!(!result.strict);
}

#[test]
fn test_parse_lift_entry_decimal_and_hex() {
    assert_eq!(parse_lift_entry(Some("4198400")).unwrap(), Some(4_198_400));
    assert_eq!(parse_lift_entry(Some("0x401000")).unwrap(), Some(0x401000));
    assert!(parse_lift_entry(Some("not-an-address")).is_err());
}

#[test]
fn test_lift_report_counts_and_strict_exit() {
    let report = build_lift_report(
        Path::new("demo.bin"),
        Some(0x401000),
        true,
        LiftReportInput {
            format: Some("ELF".into()),
            architecture: Some("x86_64".into()),
            binary_entry: Some(0x401000),
            functions: vec![LiftedTmirFunctionSummary {
                name: "main".into(),
                entry: Some(0x401000),
                blocks: 2,
                statements: 7,
                vcs: 3,
            }],
            unsupported: vec!["unsupported opcode".into()],
            failures: Vec::new(),
        },
    );

    assert_eq!(report.status, BinaryLiftStatus::Incomplete);
    assert_eq!(report.functions_lifted, 1);
    assert_eq!(report.blocks, 2);
    assert_eq!(report.statements, 7);
    assert_eq!(report.vcs, 3);
    assert_eq!(report.unsupported, 1);
    assert!(lift_should_fail(&report));

    let rendered = render_lift_terminal(&report);
    assert!(rendered.contains("functions lifted: 1\n"));
    assert!(rendered.contains("status: incomplete\n"));
    assert!(rendered.contains("  - main @ 0x401000: blocks=2 statements=7 vcs=3\n"));
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
    let args: Vec<String> = vec!["--rewrite".into(), "--max-iterations".into(), "5".into()];
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

#[test]
fn test_resolve_project_root_prefers_manifest_path() {
    let cwd = temp_test_dir("project-root-manifest");
    let args: Vec<String> = vec!["--manifest-path".into(), "workspace/member/Cargo.toml".into()];
    let sub_args = parse_subcommand_args(&args).expect("should parse args");

    let resolved = resolve_project_root_from(&sub_args, &cwd);
    assert_eq!(resolved.root, cwd.join("workspace/member"));
    assert_eq!(resolved.manifest_path, Some(cwd.join("workspace/member/Cargo.toml")));
    assert_eq!(resolved.single_file_path, None);
}

#[test]
fn test_resolve_project_root_uses_single_file_parent() {
    let cwd = temp_test_dir("project-root-file");
    let args: Vec<String> = vec!["src/bin/demo.rs".into()];
    let sub_args = parse_subcommand_args(&args).expect("should parse args");

    let resolved = resolve_project_root_from(&sub_args, &cwd);
    assert_eq!(resolved.root, cwd.join("src/bin"));
    assert_eq!(resolved.manifest_path, None);
    assert_eq!(resolved.single_file_path, Some(cwd.join("src/bin/demo.rs")));
}

#[test]
fn test_resolve_project_root_walks_up_to_manifest_ancestor() {
    let root = temp_test_dir("project-root-ancestor");
    let cwd = root.join("member/src/nested");
    std::fs::create_dir_all(&cwd).expect("should create nested cwd");
    std::fs::write(
        root.join("member/Cargo.toml"),
        r#"
[package]
name = "member"
version = "0.1.0"
edition = "2021"
"#,
    )
    .expect("should write Cargo.toml");

    let sub_args = parse_subcommand_args(&[]).expect("should parse empty args");
    let resolved = resolve_project_root_from(&sub_args, &cwd);
    assert_eq!(resolved.root, root.join("member"));
    assert_eq!(resolved.manifest_path, Some(root.join("member/Cargo.toml")));

    let _ = std::fs::remove_dir_all(&root);
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
    let line =
        "note: tRust [overflow:add]: arithmetic overflow (Add) \u{2014} PROVED (z4-smtlib, 8ms)";
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

#[test]
fn test_transport_to_verification_result_preserves_structure() {
    let span = trust_types::SourceSpan {
        file: "src/lib.rs".into(),
        line_start: 7,
        col_start: 5,
        line_end: 7,
        col_end: 16,
    };
    let counterexample = trust_types::Counterexample::new(vec![(
        "divisor".into(),
        trust_types::CounterexampleValue::Int(0),
    )]);
    let transport = trust_types::TransportObligationResult {
        kind: "div_by_zero".into(),
        description: "division by zero".into(),
        location: Some(span.clone()),
        outcome: "failed".into(),
        solver: "z4-smtlib".into(),
        time_ms: 9,
        counterexample: Some("divisor = 0".into()),
        counterexample_model: Some(counterexample.clone()),
        reason: Some("solver produced a concrete witness".into()),
    };

    let result = transport_to_verification_result("crate::math::divide", &transport);
    assert_eq!(result.function, "crate::math::divide");
    assert_eq!(result.location, Some(span));
    assert_eq!(
        result.counterexample.as_ref().map(ToString::to_string),
        Some(counterexample.to_string())
    );
    assert_eq!(result.reason.as_deref(), Some("solver produced a concrete witness"));
}

// -- Config tests --

#[test]
fn test_trust_config_default() {
    let config = TrustConfig::default();
    assert!(config.enabled);
    assert_eq!(config.level, "L1");
    assert_eq!(config.timeout_ms, 5000);
    assert!(config.codegen_backend.is_none());
}

#[test]
fn test_trust_config_load_nonexistent() {
    let config = TrustConfig::load(Path::new("/nonexistent/path"));
    assert!(config.enabled);
    assert_eq!(config.level, "L1");
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
    assert!(flags.contains("trust-verify-output=json"));
}

#[test]
fn test_merged_rustflags_without_json_transport() {
    let _saved = std::env::var("RUSTFLAGS").ok();
    std::env::remove_var("RUSTFLAGS");
    let flags = merged_rustflags_with_json_transport("L1", None, false);
    assert!(flags.contains("-Z trust-verify"));
    assert!(flags.contains("trust-verify-level=1"));
    assert!(!flags.contains("trust-verify-output=json"));
}

#[test]
fn test_merged_rustflags_with_explicit_codegen_backend() {
    let _saved = std::env::var("RUSTFLAGS").ok();
    std::env::remove_var("RUSTFLAGS");
    let flags = merged_rustflags_with_backend("L1", Some("llvm2"));
    assert!(flags.contains("codegen-backend=llvm2"));
}

#[test]
fn test_html_escape() {
    assert_eq!(html_escape("<b>test</b>"), "&lt;b&gt;test&lt;/b&gt;");
    assert_eq!(html_escape("a & b"), "a &amp; b");
}

#[test]
fn test_output_format_from_str() {
    assert_eq!(OutputFormat::from_str("terminal").unwrap(), OutputFormat::Terminal);
    assert_eq!(OutputFormat::from_str("json").unwrap(), OutputFormat::Json);
    assert_eq!(OutputFormat::from_str("html").unwrap(), OutputFormat::Html);
    assert!(OutputFormat::from_str("csv").is_err());
}

#[test]
fn test_has_edition() {
    assert!(has_edition(&["--edition".into(), "2021".into()]));
    assert!(has_edition(&["--edition=2024".into()]));
    assert!(!has_edition(&["--release".into()]));
}

fn temp_test_dir(label: &str) -> PathBuf {
    let unique = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock should be after epoch")
        .as_nanos();
    std::env::temp_dir().join(format!("cargo-trust-{label}-{}-{unique}", std::process::id()))
}

fn write_trust_toml(dir: &Path, contents: &str) {
    std::fs::create_dir_all(dir).expect("should create temp dir");
    std::fs::write(dir.join("trust.toml"), contents).expect("should write trust.toml");
}

fn linked_toolchain_status(path: Option<PathBuf>) -> LinkedTrustToolchainStatus {
    LinkedTrustToolchainStatus {
        status: if path.is_some() {
            LinkedTrustToolchainStatusKind::Visible
        } else {
            LinkedTrustToolchainStatusKind::Missing
        },
        rustc: path,
        detail: None,
    }
}

#[test]
fn test_select_native_compiler_discovery_prefers_linked_trust_toolchain_before_repo_local() {
    let linked = PathBuf::from("/tmp/rustup/trust/bin/trustc");
    let repo = vec![NativeRustcDiscovery {
        rustc: PathBuf::from("/tmp/repo/build/stage1/bin/trustc"),
        source: NativeRustcDiscoverySource::RepoLocalStage1,
    }];

    let selected = select_native_rustc_discovery(
        None,
        None,
        &linked_toolchain_status(Some(linked.clone())),
        repo,
    )
    .expect("should discover trustc");

    assert_eq!(selected.rustc, linked);
    assert_eq!(selected.source, NativeRustcDiscoverySource::RustupToolchainTrust);
}

#[test]
fn test_select_native_rustc_discovery_prefers_sibling_over_linked_toolchain() {
    let sibling = PathBuf::from("/tmp/install/bin/trustc");
    let linked = PathBuf::from("/tmp/rustup/trust/bin/trustc");

    let selected = select_native_rustc_discovery(
        None,
        Some(sibling.clone()),
        &linked_toolchain_status(Some(linked)),
        Vec::new(),
    )
    .expect("should discover trustc");

    assert_eq!(selected.rustc, sibling);
    assert_eq!(selected.source, NativeRustcDiscoverySource::SiblingCargoTrust);
}

#[test]
fn test_select_native_rustc_discovery_returns_none_when_no_candidates_exist() {
    let selected = select_native_rustc_discovery(
        None,
        None,
        &LinkedTrustToolchainStatus {
            status: LinkedTrustToolchainStatusKind::RustupUnavailable,
            rustc: None,
            detail: Some("`rustup` was not found on PATH".into()),
        },
        Vec::new(),
    );

    assert!(selected.is_none());
}

#[test]
fn test_native_rustc_discovery_source_labels_match_doctor_output() {
    assert_eq!(NativeRustcDiscoverySource::TrustRustcEnv.label(), "TRUSTC");
    assert_eq!(
        NativeRustcDiscoverySource::SiblingCargoTrust.label(),
        "sibling trustc next to `cargo-trust`"
    );
    assert_eq!(
        NativeRustcDiscoverySource::RustupToolchainTrust.label(),
        "linked rustup toolchain `trust`"
    );
    assert_eq!(NativeRustcDiscoverySource::RepoLocalStage2.label(), "repo-local stage2 build");
    assert_eq!(NativeRustcDiscoverySource::RepoLocalStage1.label(), "repo-local stage1 build");
}

#[test]
fn test_linked_trust_toolchain_status_visibility_depends_on_status_kind() {
    let visible = LinkedTrustToolchainStatus {
        status: LinkedTrustToolchainStatusKind::Visible,
        rustc: Some(PathBuf::from("/tmp/rustup/trust/bin/trustc")),
        detail: None,
    };
    let missing = LinkedTrustToolchainStatus {
        status: LinkedTrustToolchainStatusKind::Missing,
        rustc: None,
        detail: Some("toolchain not linked".into()),
    };
    let unavailable = LinkedTrustToolchainStatus {
        status: LinkedTrustToolchainStatusKind::RustupUnavailable,
        rustc: None,
        detail: Some("`rustup` was not found on PATH".into()),
    };

    assert!(visible.is_visible());
    assert!(!missing.is_visible());
    assert!(!unavailable.is_visible());
}

#[test]
fn test_build_native_command_uses_sibling_cargo_for_crates() {
    let root = temp_test_dir("sibling-cargo");
    let bin_dir = root.join("stage1").join("bin");
    std::fs::create_dir_all(&bin_dir).expect("should create bin dir");

    let rustc = bin_dir.join(if cfg!(windows) { "rustc.exe" } else { "rustc" });
    let cargo = bin_dir.join(if cfg!(windows) { "cargo.exe" } else { "cargo" });
    std::fs::write(&rustc, "").expect("should create rustc marker");
    std::fs::write(&cargo, "").expect("should create cargo marker");

    let sub_args = parse_subcommand_args(&[]).expect("should parse empty passthrough");
    let cmd_args =
        build_native_command(&rustc, Subcommand::Build, &sub_args, &TrustConfig::default());

    assert_eq!(
        cmd_args[0],
        std::fs::canonicalize(&cargo)
            .expect("cargo path should canonicalize")
            .to_string_lossy()
            .to_string()
    );
    assert_eq!(cmd_args[1], "build");

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}

#[test]
fn test_build_native_command_falls_back_to_path_cargo_when_sibling_missing() {
    let root = temp_test_dir("path-cargo");
    let bin_dir = root.join("stage1").join("bin");
    std::fs::create_dir_all(&bin_dir).expect("should create bin dir");

    let rustc = bin_dir.join(if cfg!(windows) { "rustc.exe" } else { "rustc" });
    std::fs::write(&rustc, "").expect("should create rustc marker");

    let sub_args = parse_subcommand_args(&[]).expect("should parse empty passthrough");
    let cmd_args =
        build_native_command(&rustc, Subcommand::Check, &sub_args, &TrustConfig::default());

    assert_eq!(cmd_args[0], "cargo");
    assert_eq!(cmd_args[1], "check");

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}

#[test]
fn test_is_cargo_program_accepts_absolute_cargo_paths() {
    assert!(is_cargo_program("/tmp/stage1/bin/cargo"));
    assert!(is_cargo_program("cargo"));
    assert!(!is_cargo_program("/tmp/stage1/bin/rustc"));
}

#[test]
fn test_has_output_path_flag() {
    assert!(has_output_path_flag(&["-o".into(), "out.bin".into()]));
    assert!(has_output_path_flag(&["--out-dir".into(), "target/tmp".into()]));
    assert!(has_output_path_flag(&["--out-dir=target/tmp".into()]));
    assert!(!has_output_path_flag(&["--edition".into(), "2021".into(), "main.rs".into()]));
}

#[test]
fn test_build_native_command_injects_temp_output_for_single_file_checks() {
    let rustc = Path::new("/tmp/rustc");
    let config = TrustConfig::default();
    let sub_args = parse_subcommand_args(&["examples/midpoint.rs".into()])
        .expect("should parse single-file args");
    let cmd = build_native_command(rustc, Subcommand::Check, &sub_args, &config);

    let output_idx = cmd.iter().position(|arg| arg == "-o").expect("missing -o");
    let output_path = &cmd[output_idx + 1];
    assert!(output_path.contains("cargo-trust-midpoint-"));
    assert!(cmd.iter().any(|arg| arg == "trust-verify-output=json"));
}

#[test]
fn test_build_native_command_can_omit_json_transport_flag() {
    let rustc = Path::new("/tmp/rustc");
    let config = TrustConfig::default();
    let sub_args = parse_subcommand_args(&["examples/midpoint.rs".into()])
        .expect("should parse single-file args");
    let cmd = build_native_command_with_json_transport(
        rustc,
        Subcommand::Check,
        &sub_args,
        &config,
        None,
        false,
    );

    assert!(!cmd.iter().any(|arg| arg == "trust-verify-output=json"));
}

#[test]
fn test_build_native_command_includes_explicit_codegen_backend() {
    let rustc = Path::new("/tmp/rustc");
    let config = TrustConfig::default();
    let sub_args = parse_subcommand_args(&["examples/midpoint.rs".into()])
        .expect("should parse single-file args");
    let cmd = build_native_command_with_json_transport(
        rustc,
        Subcommand::Build,
        &sub_args,
        &config,
        Some("llvm2"),
        true,
    );

    assert!(cmd.iter().any(|arg| arg == "codegen-backend=llvm2"));
}

#[test]
fn test_build_native_command_preserves_default_output_for_single_file_builds() {
    let rustc = Path::new("/tmp/rustc");
    let config = TrustConfig::default();
    let sub_args = parse_subcommand_args(&["examples/midpoint.rs".into()])
        .expect("should parse single-file args");
    let cmd = build_native_command(rustc, Subcommand::Build, &sub_args, &config);

    assert!(!cmd.iter().any(|arg| arg == "-o"));
}

#[test]
fn test_build_native_command_respects_explicit_output_for_single_file_checks() {
    let rustc = Path::new("/tmp/rustc");
    let config = TrustConfig::default();
    let sub_args = parse_subcommand_args(&[
        "examples/midpoint.rs".into(),
        "-o".into(),
        "custom-midpoint".into(),
    ])
    .expect("should parse single-file args with explicit output");
    let cmd = build_native_command(rustc, Subcommand::Check, &sub_args, &config);

    let outputs = cmd.iter().filter(|arg| arg.as_str() == "-o").count();
    assert_eq!(outputs, 1);
    assert!(cmd.iter().any(|arg| arg == "custom-midpoint"));
}

#[test]
fn test_compiler_help_supports_option_detects_expected_flags() {
    let help = "  -Z trust-verify=val\n  -Z trust-verify-output=val\n";
    assert!(compiler_help_supports_option(help, "trust-verify="));
    assert!(compiler_help_supports_option(help, "trust-verify-output="));
    assert!(!compiler_help_supports_option(help, "no-such-flag="));
}

#[test]
fn test_report_json_serialization() {
    let report = VerificationReport {
        success: true,
        exit_code: 0,
        proved: 1,
        failed: 0,
        unknown: 0,
        runtime_checked: 0,
        total: 1,
        results: vec![VerificationResult {
            function: "crate::midpoint".into(),
            kind: "overflow:add".into(),
            message: "arithmetic overflow".into(),
            outcome: VerificationOutcome::Proved,
            backend: "z4-smtlib".into(),
            time_ms: Some(8),
            location: None,
            counterexample: None,
            reason: None,
            raw_line: "note: tRust [overflow:add]: arithmetic overflow -- PROVED (z4-smtlib, 8ms)"
                .into(),
        }],
        compiler_diagnostics: vec![],
        duration_ms: 42,
        config: ReportConfig { level: "L0".into(), timeout_ms: 5000, enabled: true },
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
        runtime_checked: 0,
        total: 2,
        results: vec![],
        compiler_diagnostics: vec![],
        duration_ms: 10,
        config: ReportConfig { level: "L0".into(), timeout_ms: 5000, enabled: true },
    };
    assert!(report.success);

    // Has failures => not success even with exit 0
    let report2 = VerificationReport {
        success: false,
        exit_code: 0,
        proved: 1,
        failed: 1,
        unknown: 0,
        runtime_checked: 0,
        total: 2,
        results: vec![],
        compiler_diagnostics: vec![],
        duration_ms: 10,
        config: ReportConfig { level: "L0".into(), timeout_ms: 5000, enabled: true },
    };
    assert!(!report2.success);
}

// -- Doctor helper tests --

#[test]
fn test_backend_status_prefers_cli_override_over_trust_toml() {
    let args =
        parse_subcommand_args(&["--backend".into(), "llvm".into()]).expect("should parse args");
    let config = TrustConfig { codegen_backend: Some("llvm2".into()), ..TrustConfig::default() };

    let status = backend_status(&args, &config);

    assert_eq!(status.selected, "llvm");
    assert_eq!(status.source.label(), "CLI override");
}

#[test]
fn test_backend_status_uses_trust_toml_then_default() {
    let args = parse_subcommand_args(&[]).expect("should parse empty args");

    let configured = backend_status(
        &args,
        &TrustConfig { codegen_backend: Some("llvm2".into()), ..TrustConfig::default() },
    );
    assert_eq!(configured.selected, "llvm2");
    assert_eq!(configured.source.label(), "trust.toml");

    let defaulted = backend_status(&args, &TrustConfig::default());
    assert_eq!(defaulted.selected, DEFAULT_CODEGEN_BACKEND);
    assert_eq!(defaulted.source.label(), "default");
}

#[test]
fn test_load_doctor_config_reports_missing_trust_toml() {
    let root = temp_test_dir("doctor-config-missing");
    std::fs::create_dir_all(&root).expect("should create temp dir");

    let (config, status) = load_doctor_config(&root);

    assert_eq!(config.level, TrustConfig::default().level);
    assert_eq!(config.timeout_ms, TrustConfig::default().timeout_ms);
    assert_eq!(status.path, root.join("trust.toml"));
    assert_eq!(status.source.label(), "defaults");
    assert_eq!(status.detail.as_deref(), Some("no trust.toml found"));
    assert_eq!(
        describe_config_source(&status),
        format!("defaults at {}: no trust.toml found", status.path.display())
    );

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}

#[test]
fn test_load_doctor_config_normalizes_known_backend() {
    let root = temp_test_dir("doctor-config-valid");
    write_trust_toml(
        &root,
        r#"
enabled = false
level = "L2"
timeout_ms = 42
codegen_backend = "LLVM2"
"#,
    );

    let (config, status) = load_doctor_config(&root);

    assert!(!config.enabled);
    assert_eq!(config.level, "L2");
    assert_eq!(config.timeout_ms, 42);
    assert_eq!(config.codegen_backend.as_deref(), Some("llvm2"));
    assert_eq!(status.source.label(), "trust.toml");
    assert_eq!(status.configured_codegen_backend.as_deref(), Some("llvm2"));
    assert!(status.detail.is_none());
    assert_eq!(describe_config_source(&status), format!("trust.toml ({})", status.path.display()));

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}

#[test]
fn test_load_doctor_config_ignores_unknown_backend_with_detail() {
    let root = temp_test_dir("doctor-config-unknown-backend");
    write_trust_toml(
        &root,
        r#"
level = "L0"
codegen_backend = "cranelift"
"#,
    );

    let (config, status) = load_doctor_config(&root);

    assert_eq!(config.level, "L0");
    assert!(config.codegen_backend.is_none());
    assert!(status.configured_codegen_backend.is_none());
    assert_eq!(status.source.label(), "trust.toml");
    let detail = status.detail.expect("should explain ignored backend");
    assert!(detail.contains("ignored unknown codegen backend `cranelift`"));

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}

#[test]
fn test_load_doctor_config_invalid_toml_falls_back_to_defaults() {
    let root = temp_test_dir("doctor-config-invalid");
    write_trust_toml(
        &root,
        r#"
enabled = true
unexpected = "value"
"#,
    );

    let (config, status) = load_doctor_config(&root);

    assert_eq!(config.level, TrustConfig::default().level);
    assert_eq!(config.timeout_ms, TrustConfig::default().timeout_ms);
    assert_eq!(status.source.label(), "defaults (invalid trust.toml)");
    assert!(status.source.has_error());
    assert!(status.detail.is_some());
    let description = describe_config_source(&status);
    assert!(description.contains("defaults (invalid trust.toml)"));
    assert!(description.contains("trust.toml"));

    std::fs::remove_dir_all(&root).expect("should remove temp dir");
}

#[test]
fn test_describe_capability_covers_all_states() {
    assert_eq!(describe_capability(Some(true)), "supported");
    assert_eq!(describe_capability(Some(false)), "not supported");
    assert_eq!(describe_capability(None), "unknown");
}

#[test]
fn test_doctor_report_json_exposes_native_reporting_contract() {
    let rustc = PathBuf::from("/opt/trust/bin/trustc");
    let linked_rustc = PathBuf::from("/rustup/toolchains/trust/bin/trustc");
    let report = DoctorReport {
        ready: true,
        status: "ready",
        compiler: DoctorCompilerStatus {
            path: Some(rustc.clone()),
            discovery_source: Some(NativeRustcDiscoverySource::TrustRustcEnv),
            linked_toolchain_status: LinkedTrustToolchainStatusKind::Visible,
            linked_toolchain_path: Some(linked_rustc.clone()),
            linked_toolchain_detail: None,
            trust_verify: Some(true),
            json_transport: Some(true),
            check_report_mode: DoctorCheckReportMode::NativeCompiler,
        },
        backend: DoctorBackendStatus {
            selected: DEFAULT_CODEGEN_BACKEND.to_string(),
            source: DoctorBackendSource::Default,
        },
        config: DoctorConfigStatus {
            source: DoctorConfigSourceKind::Defaults,
            path: PathBuf::from("trust.toml"),
            detail: None,
            enabled: true,
            level: "L1".to_string(),
            timeout_ms: 5_000,
            configured_codegen_backend: None,
        },
        solvers: DoctorSolverStatus { requested: None, available: 0, total: 0, solvers: vec![] },
    };

    let json = serde_json::to_value(&report).expect("doctor report should serialize");
    let compiler = &json["compiler"];

    assert_eq!(compiler["path"], rustc.to_string_lossy().as_ref());
    assert_eq!(compiler["discovery_source"], "trustc_env");
    assert_eq!(compiler["linked_toolchain_status"], "visible");
    assert_eq!(compiler["linked_toolchain_path"], linked_rustc.to_string_lossy().as_ref());
    assert_eq!(compiler["trust_verify"], true);
    assert_eq!(compiler["json_transport"], true);
    assert_eq!(compiler["check_report_mode"], "native_compiler");
}

#[test]
fn test_doctor_report_json_exposes_standalone_fallback_contract() {
    let report = DoctorReport {
        ready: false,
        status: "needs_attention",
        compiler: DoctorCompilerStatus {
            path: None,
            discovery_source: None,
            linked_toolchain_status: LinkedTrustToolchainStatusKind::Missing,
            linked_toolchain_path: None,
            linked_toolchain_detail: Some("toolchain `trust` is not installed".to_string()),
            trust_verify: None,
            json_transport: None,
            check_report_mode: DoctorCheckReportMode::StandaloneFallback,
        },
        backend: DoctorBackendStatus {
            selected: DEFAULT_CODEGEN_BACKEND.to_string(),
            source: DoctorBackendSource::Default,
        },
        config: DoctorConfigStatus {
            source: DoctorConfigSourceKind::Defaults,
            path: PathBuf::from("trust.toml"),
            detail: Some("no trust.toml found".to_string()),
            enabled: true,
            level: "L1".to_string(),
            timeout_ms: 5_000,
            configured_codegen_backend: None,
        },
        solvers: DoctorSolverStatus { requested: None, available: 0, total: 0, solvers: vec![] },
    };

    let json = serde_json::to_value(&report).expect("doctor report should serialize");
    let compiler = &json["compiler"];

    assert!(compiler.get("path").expect("path field should be stable").is_null());
    assert!(
        compiler
            .get("discovery_source")
            .expect("discovery_source field should be stable")
            .is_null()
    );
    assert_eq!(compiler["linked_toolchain_status"], "missing");
    assert!(
        compiler
            .get("linked_toolchain_path")
            .expect("linked_toolchain_path field should be stable")
            .is_null()
    );
    assert_eq!(compiler["linked_toolchain_detail"], "toolchain `trust` is not installed");
    assert!(compiler.get("trust_verify").expect("trust_verify field should be stable").is_null());
    assert!(
        compiler.get("json_transport").expect("json_transport field should be stable").is_null()
    );
    assert_eq!(compiler["check_report_mode"], "standalone_fallback");
}

#[test]
fn test_parse_compiler_stderr_strips_raw_trust_json_transport() {
    let transport_json = r#"{"type":"function_result","function":"crate::midpoint","results":[{"kind":"overflow:add","description":"arithmetic overflow","outcome":"proved","solver":"z4-smtlib","time_ms":8}],"proved":1,"failed":0,"unknown":0,"runtime_checked":0,"total":1}"#;
    let stderr = format!(
        "{}{}\nwarning: ordinary compiler warning\nnote: tRust [overflow:add]: arithmetic overflow -- FAILED (z4-smtlib, 3ms)\n",
        trust_types::TRANSPORT_PREFIX,
        transport_json
    );

    let parsed = parse_compiler_stderr(std::io::Cursor::new(stderr), false);

    assert_eq!(parsed.verification_results.len(), 1);
    let result = &parsed.verification_results[0];
    assert_eq!(result.function, "crate::midpoint");
    assert_eq!(result.kind, "overflow:add");
    assert_eq!(result.outcome, VerificationOutcome::Proved);
    assert_eq!(result.backend, "z4-smtlib");
    assert_eq!(result.time_ms, Some(8));
    assert!(result.raw_line.is_empty());

    assert_eq!(parsed.compiler_diagnostics.len(), 1);
    assert_eq!(parsed.compiler_diagnostics[0].level, "warning");
    assert!(!parsed.compiler_diagnostics[0].message.contains(trust_types::TRANSPORT_PREFIX));
}

// -- Solver flag parsing tests (tRust #579) --

#[test]
fn test_parse_args_solver_flag() {
    let args: Vec<String> = vec!["--solver".into(), "z4".into()];
    let result = parse_subcommand_args(&args).expect("should parse --solver z4");
    assert_eq!(result.solver.as_deref(), Some("z4"));
}

#[test]
fn test_parse_args_backend_flag() {
    let args: Vec<String> = vec!["--backend".into(), "llvm2".into()];
    let result = parse_subcommand_args(&args).expect("should parse --backend llvm2");
    assert_eq!(result.backend.as_deref(), Some("llvm2"));
}

#[test]
fn test_usage_text_mentions_backend_and_llvm2() {
    let usage = usage_text();
    assert!(usage.contains("--backend <name>"));
    assert!(usage.contains("llvm2"));
    assert!(usage.contains("cargo trust doctor"));
}

#[test]
fn test_parse_args_backend_equals() {
    let args: Vec<String> = vec!["--backend=llvm".into()];
    let result = parse_subcommand_args(&args).expect("should parse --backend=llvm");
    assert_eq!(result.backend.as_deref(), Some("llvm"));
}

#[test]
fn test_parse_args_backend_unknown_fails() {
    let args: Vec<String> = vec!["--backend".into(), "cranelift".into()];
    assert!(parse_subcommand_args(&args).is_err());
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
        let result =
            parse_subcommand_args(&args).unwrap_or_else(|_| panic!("should parse --solver {name}"));
        assert_eq!(result.solver.as_deref(), Some(*name));
    }
}

// -- Report helper tests --

#[test]
fn test_parse_vc_kind_maps_known_aliases() {
    assert!(matches!(parse_vc_kind("div_by_zero"), VcKind::DivisionByZero));
    assert!(matches!(parse_vc_kind("division_by_zero"), VcKind::DivisionByZero));
    assert!(matches!(parse_vc_kind("bounds"), VcKind::IndexOutOfBounds));
    assert!(matches!(parse_vc_kind("slice_bounds_check"), VcKind::SliceBoundsCheck));
}

#[test]
fn test_parse_vc_kind_maps_overflow_ops_and_unknown_assertions() {
    assert!(matches!(
        parse_vc_kind("overflow:sub"),
        VcKind::ArithmeticOverflow { op: BinOp::Sub, .. }
    ));
    assert!(matches!(
        parse_vc_kind("arithmetic_overflow:mul"),
        VcKind::ArithmeticOverflow { op: BinOp::Mul, .. }
    ));

    match parse_vc_kind("custom::check") {
        VcKind::Assertion { message } => assert_eq!(message, "custom::check"),
        other => panic!("expected assertion fallback, got {other:?}"),
    }
}
