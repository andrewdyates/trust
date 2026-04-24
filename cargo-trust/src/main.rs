// cargo-trust: Cargo subcommand for tRust verification
//
// Usage:
//   cargo trust check            -- verify the current crate (check only, no codegen)
//   cargo trust check path.rs    -- verify a single file
//   cargo trust build            -- verify and build (check + codegen)
//   cargo trust check --format json
//
// cargo-trust invokes the built trustc compiler with -Z trust-verify, captures
// verification diagnostics from stderr, parses structured TRUST_JSON transport
// when present, and produces a summary report.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use anyhow::Context;
use serde::Serialize;

mod cli;
mod config;
mod diff;
mod diff_git;
mod diff_report;
mod init;
mod pipeline;
mod project_root;
mod report;
mod rewrite_loop;
mod solver_detect;
mod source_analysis;
mod types;

#[cfg(test)]
mod tests;

use cli::{SubcommandArgs, parse_subcommand_args, print_usage};
use config::{
    DEFAULT_CODEGEN_BACKEND, TrustConfig, known_codegen_backend_names, normalize_codegen_backend,
};
use pipeline::{
    LinkedTrustToolchainStatusKind, NativeRustcDiscoverySource,
    build_native_command_with_json_transport, detect_linked_trust_toolchain,
    detect_native_rustc_capabilities, discover_native_rustc, run_compiler, run_rewrite_loop,
    run_standalone_check,
};
use project_root::resolve_project_root;
use trust_lift::{
    BinaryFunctionSelection, BinaryLiftOptions, LiftError, LiftedBinary, lift_binary_to_tmir,
};
use trust_vcgen::lift_adapter::generate_binary_vcs;
use types::{
    BinaryLiftFunctionReport, BinaryLiftReport, BinaryLiftStatus, OutputFormat, Subcommand,
};

#[derive(Debug, Clone, Copy, Serialize)]
#[serde(rename_all = "snake_case")]
enum DoctorBackendSource {
    Cli,
    TrustToml,
    Default,
}

impl DoctorBackendSource {
    fn label(self) -> &'static str {
        match self {
            Self::Cli => "CLI override",
            Self::TrustToml => "trust.toml",
            Self::Default => "default",
        }
    }
}

#[derive(Debug, Clone, Serialize)]
struct DoctorBackendStatus {
    selected: String,
    source: DoctorBackendSource,
}

#[derive(Debug, Clone, Copy, Serialize)]
#[serde(rename_all = "snake_case")]
enum DoctorConfigSourceKind {
    TrustToml,
    Defaults,
    InvalidTrustToml,
    UnreadableTrustToml,
}

impl DoctorConfigSourceKind {
    fn label(self) -> &'static str {
        match self {
            Self::TrustToml => "trust.toml",
            Self::Defaults => "defaults",
            Self::InvalidTrustToml => "defaults (invalid trust.toml)",
            Self::UnreadableTrustToml => "defaults (unreadable trust.toml)",
        }
    }

    fn has_error(self) -> bool {
        matches!(self, Self::InvalidTrustToml | Self::UnreadableTrustToml)
    }
}

#[derive(Debug, Clone, Serialize)]
struct DoctorConfigStatus {
    source: DoctorConfigSourceKind,
    path: PathBuf,
    detail: Option<String>,
    enabled: bool,
    level: String,
    timeout_ms: u64,
    configured_codegen_backend: Option<String>,
}

#[derive(Debug, Clone, Serialize)]
struct DoctorCompilerStatus {
    path: Option<PathBuf>,
    discovery_source: Option<NativeRustcDiscoverySource>,
    linked_toolchain_status: LinkedTrustToolchainStatusKind,
    linked_toolchain_path: Option<PathBuf>,
    linked_toolchain_detail: Option<String>,
    trust_verify: Option<bool>,
    json_transport: Option<bool>,
    check_report_mode: DoctorCheckReportMode,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
enum DoctorCheckReportMode {
    NativeCompiler,
    StandaloneFallback,
}

impl DoctorCheckReportMode {
    fn label(self) -> &'static str {
        match self {
            Self::NativeCompiler => "native compiler",
            Self::StandaloneFallback => "standalone fallback",
        }
    }
}

#[derive(Debug, Clone, Serialize)]
struct DoctorSolverStatus {
    requested: Option<String>,
    available: usize,
    total: usize,
    solvers: Vec<solver_detect::SolverInfo>,
}

#[derive(Debug, Clone, Serialize)]
struct DoctorReport {
    ready: bool,
    status: &'static str,
    compiler: DoctorCompilerStatus,
    backend: DoctorBackendStatus,
    config: DoctorConfigStatus,
    solvers: DoctorSolverStatus,
}

fn backend_status(sub_args: &SubcommandArgs, config: &TrustConfig) -> DoctorBackendStatus {
    if let Some(backend) = sub_args.backend.as_deref() {
        DoctorBackendStatus { selected: backend.to_string(), source: DoctorBackendSource::Cli }
    } else if let Some(backend) = config.codegen_backend.as_deref() {
        DoctorBackendStatus {
            selected: backend.to_string(),
            source: DoctorBackendSource::TrustToml,
        }
    } else {
        DoctorBackendStatus {
            selected: DEFAULT_CODEGEN_BACKEND.to_string(),
            source: DoctorBackendSource::Default,
        }
    }
}

fn load_doctor_config(crate_root: &Path) -> (TrustConfig, DoctorConfigStatus) {
    let path = crate_root.join("trust.toml");
    let config = TrustConfig::default();

    if !path.exists() {
        let status = DoctorConfigStatus {
            source: DoctorConfigSourceKind::Defaults,
            path,
            detail: Some("no trust.toml found".to_string()),
            enabled: config.enabled,
            level: config.level.clone(),
            timeout_ms: config.timeout_ms,
            configured_codegen_backend: config.codegen_backend.clone(),
        };
        return (config, status);
    }

    match fs::read_to_string(&path) {
        Ok(content) => match toml::from_str::<TrustConfig>(&content) {
            Ok(mut loaded) => {
                let mut detail = None;
                if let Some(raw_backend) = loaded.codegen_backend.take() {
                    if let Some(normalized) = normalize_codegen_backend(&raw_backend) {
                        loaded.codegen_backend = Some(normalized.to_string());
                    } else {
                        let known = known_codegen_backend_names().join(", ");
                        detail = Some(format!(
                            "ignored unknown codegen backend `{raw_backend}` (known backends: {known})"
                        ));
                    }
                }
                let status = DoctorConfigStatus {
                    source: DoctorConfigSourceKind::TrustToml,
                    path,
                    detail,
                    enabled: loaded.enabled,
                    level: loaded.level.clone(),
                    timeout_ms: loaded.timeout_ms,
                    configured_codegen_backend: loaded.codegen_backend.clone(),
                };
                (loaded, status)
            }
            Err(error) => {
                let status = DoctorConfigStatus {
                    source: DoctorConfigSourceKind::InvalidTrustToml,
                    path,
                    detail: Some(error.to_string()),
                    enabled: config.enabled,
                    level: config.level.clone(),
                    timeout_ms: config.timeout_ms,
                    configured_codegen_backend: config.codegen_backend.clone(),
                };
                (config, status)
            }
        },
        Err(error) => {
            let status = DoctorConfigStatus {
                source: DoctorConfigSourceKind::UnreadableTrustToml,
                path,
                detail: Some(error.to_string()),
                enabled: config.enabled,
                level: config.level.clone(),
                timeout_ms: config.timeout_ms,
                configured_codegen_backend: config.codegen_backend.clone(),
            };
            (config, status)
        }
    }
}

fn describe_capability(supported: Option<bool>) -> &'static str {
    match supported {
        Some(true) => "supported",
        Some(false) => "not supported",
        None => "unknown",
    }
}

fn describe_linked_toolchain(
    status: LinkedTrustToolchainStatusKind,
    path: Option<&Path>,
    detail: Option<&str>,
) -> String {
    match status {
        LinkedTrustToolchainStatusKind::Visible => path
            .map(|path| format!("visible at {}", path.display()))
            .unwrap_or_else(|| "visible".to_string()),
        LinkedTrustToolchainStatusKind::Missing => detail
            .map(|detail| format!("not visible ({detail})"))
            .unwrap_or_else(|| "not visible".to_string()),
        LinkedTrustToolchainStatusKind::RustupUnavailable => detail
            .map(|detail| format!("rustup unavailable ({detail})"))
            .unwrap_or_else(|| "rustup unavailable".to_string()),
    }
}

fn doctor_check_report_mode(
    compiler_path: Option<&Path>,
    trust_verify: Option<bool>,
) -> DoctorCheckReportMode {
    if compiler_path.is_some() && trust_verify == Some(true) {
        DoctorCheckReportMode::NativeCompiler
    } else {
        DoctorCheckReportMode::StandaloneFallback
    }
}

fn describe_config_source(config: &DoctorConfigStatus) -> String {
    match config.source {
        DoctorConfigSourceKind::TrustToml => {
            format!("{} ({})", config.source.label(), config.path.display())
        }
        DoctorConfigSourceKind::Defaults
        | DoctorConfigSourceKind::InvalidTrustToml
        | DoctorConfigSourceKind::UnreadableTrustToml => {
            if let Some(detail) = config.detail.as_deref() {
                format!("{} at {}: {detail}", config.source.label(), config.path.display())
            } else {
                format!("{} at {}", config.source.label(), config.path.display())
            }
        }
    }
}

fn doctor_next_steps(report: &DoctorReport) -> Vec<String> {
    let mut steps = Vec::new();

    if report.compiler.path.is_none() {
        steps.push(
            "Make trustc discoverable via TRUSTC, a sibling install, a linked `trust` toolchain, or a repo-local build."
                .to_string(),
        );
        match report.compiler.linked_toolchain_status {
            LinkedTrustToolchainStatusKind::Missing => steps.push(
                "Link a local toolchain with `rustup toolchain link trust <path-to-toolchain>` if you want rustup-based discovery."
                    .to_string(),
            ),
            LinkedTrustToolchainStatusKind::RustupUnavailable => steps.push(
                "Install rustup or keep using TRUSTC if you want rustup-based discovery."
                    .to_string(),
            ),
            LinkedTrustToolchainStatusKind::Visible => {}
        }
    } else if report.compiler.trust_verify == Some(false) {
        steps.push("Use a trustc that supports `-Z trust-verify`.".to_string());
    }

    if report.compiler.check_report_mode == DoctorCheckReportMode::StandaloneFallback {
        steps.push(
            "`cargo trust check` and `cargo trust report` can fall back to standalone source analysis, but `build`, `loop`, and rewrite flows still need native trustc."
                .to_string(),
        );
    }

    if report.solvers.available == 0 {
        steps.push(
            "Install at least one supported solver to avoid all-unknown verification results."
                .to_string(),
        );
    }
    if report.config.source.has_error() {
        steps.push(
            "Fix or remove trust.toml so cargo-trust can load configuration cleanly.".to_string(),
        );
    }

    steps
}

fn build_doctor_report(sub_args: &SubcommandArgs) -> DoctorReport {
    let crate_root = resolve_project_root(sub_args).root;
    let (config, config_status) = load_doctor_config(&crate_root);
    let backend = backend_status(sub_args, &config);

    let linked_toolchain = detect_linked_trust_toolchain();
    let compiler_discovery = discover_native_rustc();
    let capabilities = compiler_discovery
        .as_ref()
        .map(|discovery| detect_native_rustc_capabilities(&discovery.rustc));

    let compiler = DoctorCompilerStatus {
        path: compiler_discovery.as_ref().map(|discovery| discovery.rustc.clone()),
        discovery_source: compiler_discovery.as_ref().map(|discovery| discovery.source),
        linked_toolchain_status: linked_toolchain.status,
        linked_toolchain_path: linked_toolchain.rustc.clone(),
        linked_toolchain_detail: linked_toolchain.detail.clone(),
        trust_verify: capabilities.map(|caps| caps.trust_verify),
        json_transport: capabilities.map(|caps| caps.json_transport),
        check_report_mode: doctor_check_report_mode(
            compiler_discovery.as_ref().map(|discovery| discovery.rustc.as_path()),
            capabilities.map(|caps| caps.trust_verify),
        ),
    };

    let solvers = if let Some(ref name) = sub_args.solver {
        vec![solver_detect::detect_solver(name)]
    } else {
        solver_detect::detect_all_solvers()
    };
    let available = solvers.iter().filter(|solver| solver.available).count();

    let ready =
        compiler.trust_verify == Some(true) && available > 0 && !config_status.source.has_error();

    DoctorReport {
        ready,
        status: if ready { "ready" } else { "needs_attention" },
        compiler,
        backend,
        config: config_status,
        solvers: DoctorSolverStatus {
            requested: sub_args.solver.clone(),
            available,
            total: solvers.len(),
            solvers,
        },
    }
}

fn print_doctor_terminal(report: &DoctorReport) {
    eprintln!();
    eprintln!("=== tRust Doctor ===");
    eprintln!();
    eprintln!("Status: {}", if report.ready { "READY" } else { "NEEDS ATTENTION" });
    eprintln!();
    eprintln!("Compiler:");
    match report.compiler.path.as_deref() {
        Some(path) => eprintln!("  trustc: {}", path.display()),
        None => eprintln!("  trustc: not found"),
    }
    match report.compiler.discovery_source {
        Some(source) => eprintln!("  discovery: {}", source.label()),
        None => eprintln!("  discovery: unresolved"),
    }
    eprintln!(
        "  rustup toolchain `trust`: {}",
        describe_linked_toolchain(
            report.compiler.linked_toolchain_status,
            report.compiler.linked_toolchain_path.as_deref(),
            report.compiler.linked_toolchain_detail.as_deref(),
        )
    );
    eprintln!("  -Z trust-verify: {}", describe_capability(report.compiler.trust_verify));
    eprintln!(
        "  -Z trust-verify-output=json: {}",
        describe_capability(report.compiler.json_transport)
    );
    eprintln!("  check/report mode: {}", report.compiler.check_report_mode.label());
    eprintln!();
    eprintln!("Backend:");
    eprintln!("  selected: {} ({})", report.backend.selected, report.backend.source.label());
    eprintln!("  available: llvm (default), llvm2 (opt-in)");
    eprintln!();
    eprintln!("Config:");
    eprintln!("  source: {}", describe_config_source(&report.config));
    eprintln!("  enabled: {}", report.config.enabled);
    eprintln!("  level: {}", report.config.level);
    eprintln!("  timeout_ms: {}", report.config.timeout_ms);
    if let Some(backend) = report.config.configured_codegen_backend.as_deref() {
        eprintln!("  trust.toml backend: {backend}");
    }
    eprintln!();
    eprintln!("Solvers:");
    eprintln!("  available: {}/{}", report.solvers.available, report.solvers.total);
    if let Some(requested) = report.solvers.requested.as_deref() {
        eprintln!("  requested: {requested}");
    }
    for solver in &report.solvers.solvers {
        let status = if solver.available { "FOUND" } else { "MISSING" };
        let version = solver.version.as_deref().map(|v| format!(" ({v})")).unwrap_or_default();
        let path =
            solver.path.as_deref().map(|p| format!(" at {}", p.display())).unwrap_or_default();
        eprintln!("  [{status:>7}] {:<10} {}{version}{path}", solver.name, solver.description);
    }

    if !report.ready {
        eprintln!();
        eprintln!("Next steps:");
        for step in doctor_next_steps(report) {
            eprintln!("  {step}");
        }
    }

    eprintln!();
    eprintln!("====================");
}

#[cfg(test)]
mod doctor_tests {
    use super::*;
    use crate::solver_detect::SolverInfo;

    fn available_solver() -> SolverInfo {
        SolverInfo {
            name: "z4".to_string(),
            description: "Primary SMT solver".to_string(),
            proof_levels: vec!["L0".to_string()],
            available: true,
            path: Some(PathBuf::from("/tmp/z4")),
            version: Some("1.0".to_string()),
        }
    }

    fn report_with_compiler(compiler: DoctorCompilerStatus) -> DoctorReport {
        DoctorReport {
            ready: false,
            status: "needs_attention",
            compiler,
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
            solvers: DoctorSolverStatus {
                requested: None,
                available: 1,
                total: 1,
                solvers: vec![available_solver()],
            },
        }
    }

    #[test]
    fn test_describe_linked_toolchain_rustup_unavailable() {
        assert_eq!(
            describe_linked_toolchain(
                LinkedTrustToolchainStatusKind::RustupUnavailable,
                None,
                Some("`rustup` was not found on PATH"),
            ),
            "rustup unavailable (`rustup` was not found on PATH)"
        );
    }

    #[test]
    fn test_doctor_check_report_mode_prefers_native_compiler_when_supported() {
        assert_eq!(
            doctor_check_report_mode(Some(Path::new("/tmp/rustc")), Some(true)),
            DoctorCheckReportMode::NativeCompiler
        );
        assert_eq!(
            doctor_check_report_mode(Some(Path::new("/tmp/rustc")), Some(false)),
            DoctorCheckReportMode::StandaloneFallback
        );
        assert_eq!(doctor_check_report_mode(None, None), DoctorCheckReportMode::StandaloneFallback);
    }

    #[test]
    fn test_doctor_next_steps_suggests_linking_rustup_toolchain() {
        let report = report_with_compiler(DoctorCompilerStatus {
            path: None,
            discovery_source: None,
            linked_toolchain_status: LinkedTrustToolchainStatusKind::Missing,
            linked_toolchain_path: None,
            linked_toolchain_detail: Some("toolchain `trust` is not installed".to_string()),
            trust_verify: None,
            json_transport: None,
            check_report_mode: DoctorCheckReportMode::StandaloneFallback,
        });

        let steps = doctor_next_steps(&report);
        assert!(steps.iter().any(|step| step.contains("rustup toolchain link trust")));
        assert!(steps.iter().any(|step| step.contains("standalone source analysis")));
    }
}

fn main() -> ExitCode {
    let args: Vec<String> = env::args().collect();

    // cargo invokes us as: cargo-trust trust <subcommand> [args...]
    let start = if args.get(1).is_some_and(|a| a == "trust") { 2 } else { 1 };

    let subcommand = args.get(start).map(|s| s.as_str());

    match subcommand {
        Some("check") => run_subcommand(Subcommand::Check, &args[start + 1..]),
        Some("build") => run_subcommand(Subcommand::Build, &args[start + 1..]),
        Some("lift") => run_lift_subcommand(&args[start + 1..]),
        Some("report") => run_subcommand(Subcommand::Report, &args[start + 1..]),
        Some("loop") => run_subcommand(Subcommand::Loop, &args[start + 1..]),
        Some("diff") => run_subcommand(Subcommand::Diff, &args[start + 1..]),
        Some("init") => run_init_subcommand(&args[start + 1..]),
        Some("solvers") => run_subcommand(Subcommand::Solvers, &args[start + 1..]),
        Some("doctor") => run_doctor_subcommand(&args[start + 1..]),
        Some("help") | Some("--help") | None => {
            print_usage();
            ExitCode::SUCCESS
        }
        Some(other) => {
            eprintln!("cargo-trust: unknown subcommand `{other}`");
            print_usage();
            ExitCode::FAILURE
        }
    }
}

#[derive(Debug, Clone)]
struct LiftReportInput {
    format: Option<String>,
    architecture: Option<String>,
    binary_entry: Option<u64>,
    functions: Vec<LiftedTmirFunctionSummary>,
    unsupported: Vec<String>,
    failures: Vec<String>,
}

#[derive(Debug, Clone)]
struct LiftedTmirFunctionSummary {
    name: String,
    entry: Option<u64>,
    blocks: usize,
    statements: usize,
    vcs: usize,
}

fn run_lift_subcommand(args: &[String]) -> ExitCode {
    if args.iter().any(|arg| arg == "--help" || arg == "-h") {
        print!("{}", lift_usage_text());
        return ExitCode::SUCCESS;
    }

    let sub_args = match parse_subcommand_args(args) {
        Ok(a) => a,
        Err(e) => {
            eprintln!("cargo-trust: {e}");
            return ExitCode::from(2);
        }
    };

    let binary = match lift_binary_arg(&sub_args) {
        Ok(binary) => binary,
        Err(e) => {
            eprintln!("cargo-trust: {e}");
            return ExitCode::from(2);
        }
    };

    let entry = match parse_lift_entry(sub_args.entry.as_deref()) {
        Ok(entry) => entry,
        Err(e) => {
            eprintln!("cargo-trust: {e}");
            return ExitCode::from(2);
        }
    };

    let binary_path = Path::new(binary);
    let bytes = match fs::read(binary_path) {
        Ok(bytes) => bytes,
        Err(error) => {
            eprintln!("cargo-trust: failed to read {}: {error}", binary_path.display());
            return ExitCode::from(2);
        }
    };

    let options = lift_options(entry, sub_args.all_functions, sub_args.strict);
    let output = lift_report_input_from_result(lift_binary_to_tmir(&bytes, options));
    let report = build_lift_report(binary_path, entry, sub_args.strict, output);

    match sub_args.format {
        OutputFormat::Json => match serde_json::to_string_pretty(&report) {
            Ok(json) => println!("{json}"),
            Err(error) => {
                eprintln!("cargo-trust: failed to serialize lift report: {error}");
                return ExitCode::from(2);
            }
        },
        OutputFormat::Terminal | OutputFormat::Html => {
            print!("{}", render_lift_terminal(&report));
        }
    }

    if lift_should_fail(&report) { ExitCode::FAILURE } else { ExitCode::SUCCESS }
}

fn lift_binary_arg(sub_args: &SubcommandArgs) -> anyhow::Result<&str> {
    match sub_args.passthrough.as_slice() {
        [] => anyhow::bail!("lift requires a binary path"),
        [binary] if binary.starts_with('-') => anyhow::bail!("unexpected lift option `{binary}`"),
        [binary] => Ok(binary),
        _ => anyhow::bail!("lift accepts exactly one binary path"),
    }
}

fn lift_usage_text() -> &'static str {
    "cargo-trust lift: lift binary code into tMIR\n\
\n\
Usage:\n\
  cargo trust lift <binary> [--entry <addr>] [--all] [--json] [--strict|--allow-unsupported]\n\
\n\
Options:\n\
  --entry <addr>       Lift the function containing addr (decimal or 0x-prefixed hex)\n\
  --all                Lift all detected function symbols\n\
  --json               Emit JSON output\n\
  --strict             Fail when unsupported code is encountered (default)\n\
  --allow-unsupported  Permit partial lift coverage\n"
}

fn parse_lift_entry(entry: Option<&str>) -> anyhow::Result<Option<u64>> {
    let Some(entry) = entry else {
        return Ok(None);
    };
    if entry.is_empty() {
        anyhow::bail!("--entry requires an address");
    }
    let parsed = if let Some(hex) = entry.strip_prefix("0x").or_else(|| entry.strip_prefix("0X")) {
        u64::from_str_radix(hex, 16)
            .with_context(|| format!("--entry must be a valid address: `{entry}`"))?
    } else {
        entry
            .parse::<u64>()
            .with_context(|| format!("--entry must be a valid address: `{entry}`"))?
    };
    Ok(Some(parsed))
}

fn lift_options(entry: Option<u64>, all_functions: bool, strict: bool) -> BinaryLiftOptions {
    let functions = match entry {
        Some(entry) => BinaryFunctionSelection::Addresses(vec![entry]),
        None if all_functions => BinaryFunctionSelection::All,
        None => BinaryFunctionSelection::Entry,
    };
    BinaryLiftOptions { functions, strict }
}

fn lift_report_input_from_result(result: Result<LiftedBinary, LiftError>) -> LiftReportInput {
    match result {
        Ok(binary) => lift_report_input_from_binary(binary),
        Err(error) => {
            let message = error.to_string();
            if is_unsupported_lift_error(&error) {
                LiftReportInput {
                    format: None,
                    architecture: None,
                    binary_entry: None,
                    functions: Vec::new(),
                    unsupported: vec![message],
                    failures: Vec::new(),
                }
            } else {
                LiftReportInput {
                    format: None,
                    architecture: None,
                    binary_entry: None,
                    functions: Vec::new(),
                    unsupported: Vec::new(),
                    failures: vec![message],
                }
            }
        }
    }
}

fn lift_report_input_from_binary(binary: LiftedBinary) -> LiftReportInput {
    let format = Some(binary.format.to_string());
    let architecture = Some(binary.architecture.to_string());
    let binary_entry = binary.entry_point;
    let functions = binary
        .functions
        .into_iter()
        .map(|function| {
            let blocks = function.tmir_body.blocks.len();
            let statements = function.tmir_body.blocks.iter().map(|block| block.stmts.len()).sum();
            let vcs = generate_binary_vcs(&function).len();
            LiftedTmirFunctionSummary {
                name: function.name,
                entry: Some(function.entry_point),
                blocks,
                statements,
                vcs,
            }
        })
        .collect::<Vec<_>>();
    let unsupported = binary
        .failures
        .into_iter()
        .map(|failure| {
            let entry = hex_addr(failure.entry_point);
            match failure.name {
                Some(name) => format!("{name} @ {entry}: {}", failure.error),
                None => format!("{entry}: {}", failure.error),
            }
        })
        .collect();

    LiftReportInput {
        format,
        architecture,
        binary_entry,
        functions,
        unsupported,
        failures: Vec::new(),
    }
}

fn is_unsupported_lift_error(error: &LiftError) -> bool {
    matches!(
        error,
        LiftError::BinaryParserUnavailable
            | LiftError::UnsupportedMachine(_)
            | LiftError::UnsupportedBinaryFormat { .. }
            | LiftError::Disasm { .. }
            | LiftError::EmptyBlock { .. }
    )
}

fn build_lift_report(
    binary_path: &Path,
    entry: Option<u64>,
    strict: bool,
    output: LiftReportInput,
) -> BinaryLiftReport {
    let functions = output
        .functions
        .into_iter()
        .map(|function| BinaryLiftFunctionReport {
            name: function.name,
            entry: function.entry.map(hex_addr),
            blocks: function.blocks,
            statements: function.statements,
            vcs: function.vcs,
        })
        .collect::<Vec<_>>();
    let blocks = functions.iter().map(|function| function.blocks).sum();
    let statements = functions.iter().map(|function| function.statements).sum();
    let vcs = functions.iter().map(|function| function.vcs).sum();
    let unsupported = output.unsupported.len();
    let failures = output.failures.len();
    let status = if failures > 0 {
        BinaryLiftStatus::Failed
    } else if unsupported > 0 {
        BinaryLiftStatus::Incomplete
    } else {
        BinaryLiftStatus::Ok
    };

    BinaryLiftReport {
        binary: binary_path.display().to_string(),
        format: output.format,
        architecture: output.architecture,
        entry: entry.map(hex_addr),
        binary_entry: output.binary_entry.map(hex_addr),
        strict,
        status,
        functions_lifted: functions.len(),
        blocks,
        statements,
        vcs,
        unsupported,
        failures,
        functions,
        unsupported_items: output.unsupported,
        failure_items: output.failures,
    }
}

fn lift_should_fail(report: &BinaryLiftReport) -> bool {
    report.failures > 0 || (report.strict && report.unsupported > 0)
}

fn render_lift_terminal(report: &BinaryLiftReport) -> String {
    use std::fmt::Write as _;

    let mut out = String::new();
    writeln!(out, "cargo-trust lift report").expect("write to string");
    writeln!(out, "binary: {}", report.binary).expect("write to string");
    writeln!(out, "format: {}", report.format.as_deref().unwrap_or("unknown"))
        .expect("write to string");
    writeln!(out, "architecture: {}", report.architecture.as_deref().unwrap_or("unknown"))
        .expect("write to string");
    writeln!(out, "entry: {}", report.entry.as_deref().unwrap_or("all")).expect("write to string");
    writeln!(out, "binary entry: {}", report.binary_entry.as_deref().unwrap_or("unknown"))
        .expect("write to string");
    writeln!(out, "strict: {}", report.strict).expect("write to string");
    writeln!(out, "functions lifted: {}", report.functions_lifted).expect("write to string");
    writeln!(out, "blocks: {}", report.blocks).expect("write to string");
    writeln!(out, "statements: {}", report.statements).expect("write to string");
    writeln!(out, "vcs: {}", report.vcs).expect("write to string");
    writeln!(out, "unsupported: {}", report.unsupported).expect("write to string");
    writeln!(out, "failures: {}", report.failures).expect("write to string");
    writeln!(out, "status: {}", report.status.label()).expect("write to string");

    if !report.functions.is_empty() {
        writeln!(out, "functions:").expect("write to string");
        for function in &report.functions {
            writeln!(
                out,
                "  - {} @ {}: blocks={} statements={} vcs={}",
                function.name,
                function.entry.as_deref().unwrap_or("unknown"),
                function.blocks,
                function.statements,
                function.vcs
            )
            .expect("write to string");
        }
    }

    if !report.unsupported_items.is_empty() {
        writeln!(out, "unsupported items:").expect("write to string");
        for item in &report.unsupported_items {
            writeln!(out, "  - {item}").expect("write to string");
        }
    }

    if !report.failure_items.is_empty() {
        writeln!(out, "failures:").expect("write to string");
        for item in &report.failure_items {
            writeln!(out, "  - {item}").expect("write to string");
        }
    }

    out
}

fn hex_addr(address: u64) -> String {
    format!("0x{address:x}")
}

fn run_subcommand(subcommand: Subcommand, args: &[String]) -> ExitCode {
    let sub_args = match parse_subcommand_args(args) {
        Ok(a) => a,
        Err(e) => {
            eprintln!("cargo-trust: {e}");
            return ExitCode::from(2);
        }
    };

    // Handle `diff` subcommand separately -- it compares reports, not runs.
    if subcommand == Subcommand::Diff {
        return diff_report::run_diff(&sub_args, &resolve_project_root(&sub_args).root);
    }

    // Handle `solvers` subcommand -- detect and report solver status.
    if subcommand == Subcommand::Solvers {
        return run_solvers(&sub_args);
    }

    // Discover trust.toml from the resolved project root.
    let crate_root = resolve_project_root(&sub_args).root;
    let config = TrustConfig::load(&crate_root);
    let selected_codegen_backend =
        sub_args.backend.as_deref().or(config.codegen_backend.as_deref());
    // tRust #580: Load incremental verification cache.
    let cache_path = crate_root.join("target/trust-cache/verification.json");
    let mut cache = if sub_args.fresh {
        eprintln!("cargo-trust: --fresh: bypassing verification cache");
        trust_cache::VerificationCache::in_memory()
    } else {
        match trust_cache::VerificationCache::load(&cache_path) {
            Ok(c) => {
                if !c.is_empty() {
                    eprintln!("cargo-trust: loaded {} cached verification results", c.len());
                }
                c
            }
            Err(e) => {
                eprintln!("cargo-trust: warning: failed to load cache: {e}");
                trust_cache::VerificationCache::in_memory()
            }
        }
    };

    if !config.enabled {
        eprintln!("cargo-trust: verification disabled in trust.toml");
        return ExitCode::SUCCESS;
    }

    // tRust #579: When --solver is specified, validate availability and set
    // TRUST_SOLVER env var so the verification pipeline uses it.
    if let Some(ref solver_name) = sub_args.solver {
        let info = solver_detect::detect_solver(solver_name);
        if !info.available {
            eprintln!("cargo-trust: warning: solver `{solver_name}` not found on PATH");
            eprintln!("  Run `cargo trust solvers` to check solver status");
        } else if let Some(ref path) = info.path {
            eprintln!("cargo-trust: using solver `{solver_name}` at {}", path.display());
        }
        // Set env var for downstream trust-router to pick up.
        env::set_var("TRUST_SOLVER", solver_name);
    }

    // Standalone mode: source-level analysis without invoking trustc.
    let native_rustc = discover_native_rustc();
    let native_capabilities =
        native_rustc.as_ref().map(|discovery| detect_native_rustc_capabilities(&discovery.rustc));
    let use_standalone = sub_args.standalone
        || native_rustc.is_none()
        || (matches!(subcommand, Subcommand::Check | Subcommand::Report)
            && native_capabilities.is_some_and(|caps| !caps.trust_verify));

    if use_standalone && (subcommand == Subcommand::Check || subcommand == Subcommand::Report) {
        if !sub_args.standalone {
            if native_rustc.is_none() {
                eprintln!(
                    "cargo-trust: trustc not found, falling back to standalone source analysis"
                );
            } else {
                eprintln!(
                    "cargo-trust: native compiler lacks -Z trust-verify, falling back to standalone source analysis"
                );
            }
        }
        return run_standalone_check(&sub_args, &crate_root);
    }

    if let (Some(discovery), Some(capabilities)) = (native_rustc, native_capabilities) {
        let rustc = discovery.rustc;
        eprintln!(
            "cargo-trust: using native compiler at {} ({})",
            rustc.display(),
            discovery.source.label()
        );
        if let Some(backend) = selected_codegen_backend {
            eprintln!("cargo-trust: using codegen backend `{backend}`");
        } else {
            eprintln!("cargo-trust: using default codegen backend `{DEFAULT_CODEGEN_BACKEND}`");
        }
        if !capabilities.json_transport {
            eprintln!(
                "cargo-trust: native compiler lacks -Z trust-verify-output; parsing human-readable diagnostics"
            );
        }

        // `loop` subcommand always runs the rewrite loop.
        if subcommand == Subcommand::Loop || sub_args.rewrite {
            return run_rewrite_loop(
                &rustc,
                if subcommand == Subcommand::Loop { Subcommand::Check } else { subcommand },
                &sub_args,
                &config,
                selected_codegen_backend,
                capabilities.json_transport,
            );
        }

        // `report` runs check + renders in the requested format.
        let compile_cmd = match subcommand {
            Subcommand::Report => Subcommand::Check,
            other => other,
        };

        let exit_code = run_compiler(
            &build_native_command_with_json_transport(
                &rustc,
                compile_cmd,
                &sub_args,
                &config,
                selected_codegen_backend,
                capabilities.json_transport,
            ),
            &rustc,
            &config,
            selected_codegen_backend,
            capabilities.json_transport,
            sub_args.format,
            sub_args.report_dir.as_deref(),
            &mut cache,
        );
        // tRust #580: Save cache after verification.
        if let Err(e) = cache.save() {
            eprintln!("cargo-trust: warning: failed to save cache: {e}");
        } else if !sub_args.fresh {
            eprintln!("cargo-trust: cache saved ({})", cache.summary());
        }
        return exit_code;
    }

    eprintln!("cargo-trust: error: trustc not found");
    eprintln!();
    eprintln!("Discovery order:");
    eprintln!("  1. TRUSTC");
    eprintln!("  2. sibling trustc next to the running cargo-trust");
    eprintln!("  3. linked rustup toolchain `trust`");
    eprintln!("  4. repo-local build/.../stage{{1,2}} trustc");
    eprintln!();
    eprintln!(
        "Set TRUSTC=/path/to/trustc to override discovery (cargo-trust derives sibling cargo)."
    );
    eprintln!("Or build/link a trust toolchain so cargo-trust can find trustc automatically.");
    eprintln!("Or use --standalone for source-level analysis without the compiler.");
    ExitCode::from(2)
}

fn run_doctor_subcommand(args: &[String]) -> ExitCode {
    let sub_args = match parse_subcommand_args(args) {
        Ok(a) => a,
        Err(e) => {
            eprintln!("cargo-trust: {e}");
            return ExitCode::from(2);
        }
    };

    let report = build_doctor_report(&sub_args);

    match sub_args.format {
        OutputFormat::Json => match serde_json::to_string_pretty(&report) {
            Ok(json) => println!("{json}"),
            Err(error) => {
                eprintln!("cargo-trust: failed to serialize doctor report: {error}");
                return ExitCode::from(2);
            }
        },
        OutputFormat::Terminal | OutputFormat::Html => print_doctor_terminal(&report),
    }

    if report.ready { ExitCode::SUCCESS } else { ExitCode::FAILURE }
}

// ---------------------------------------------------------------------------
// Solver detection subcommand
// ---------------------------------------------------------------------------

/// Run the `solvers` subcommand: detect all known dMATH solver binaries and
/// report their status.
fn run_solvers(sub_args: &SubcommandArgs) -> ExitCode {
    let solvers = if let Some(ref name) = sub_args.solver {
        vec![solver_detect::detect_solver(name)]
    } else {
        solver_detect::detect_all_solvers()
    };

    match sub_args.format {
        OutputFormat::Json => solver_detect::render_solvers_json(&solvers),
        OutputFormat::Terminal | OutputFormat::Html => {
            solver_detect::render_solvers_terminal(&solvers);
        }
    }

    let any_available = solvers.iter().any(|s| s.available);
    if any_available { ExitCode::SUCCESS } else { ExitCode::FAILURE }
}

// ---------------------------------------------------------------------------
// Init subcommand
// ---------------------------------------------------------------------------

/// Run the `init` subcommand: scaffold verification annotations.
fn run_init_subcommand(args: &[String]) -> ExitCode {
    let sub_args = match parse_subcommand_args(args) {
        Ok(a) => a,
        Err(e) => {
            eprintln!("cargo-trust: {e}");
            return ExitCode::from(2);
        }
    };

    let resolved_root = resolve_project_root(&sub_args);
    let crate_root = resolved_root.root;

    let summary = if sub_args.is_single_file {
        let file = resolved_root.single_file_path.unwrap_or_else(|| {
            PathBuf::from(
                sub_args.single_file_path().expect("single-file mode should have a file path"),
            )
        });
        if !file.exists() {
            eprintln!("cargo-trust: error: file not found: {}", file.display());
            return ExitCode::from(2);
        }
        eprintln!("cargo-trust: scanning {} for annotation scaffolding", file.display());
        init::scaffold_file(&file)
    } else {
        eprintln!(
            "cargo-trust: scanning crate at {} for annotation scaffolding",
            crate_root.display()
        );
        init::scaffold_crate(&crate_root)
    };

    // Write trust.toml if it doesn't exist
    let toml_path = crate_root.join("trust.toml");
    if !toml_path.exists() {
        let toml_content = init::generate_trust_toml();
        match std::fs::write(&toml_path, &toml_content) {
            Ok(()) => {
                eprintln!("cargo-trust: created {}", toml_path.display());
            }
            Err(e) => {
                eprintln!("cargo-trust: warning: failed to write {}: {e}", toml_path.display());
            }
        }
    } else {
        eprintln!("cargo-trust: {} already exists, skipping", toml_path.display());
    }

    // Output annotations
    if sub_args.inline {
        if summary.annotations.is_empty() {
            eprintln!("cargo-trust: no annotations to write");
        } else {
            match init::write_inline_annotations(&summary.annotations) {
                Ok(count) => {
                    eprintln!("cargo-trust: wrote annotations for {count} functions inline");
                }
                Err(e) => {
                    eprintln!("cargo-trust: error writing inline annotations: {e}");
                    return ExitCode::FAILURE;
                }
            }
        }
    } else {
        init::render_annotations_stdout(&summary.annotations);
    }

    init::render_summary(&summary);

    ExitCode::SUCCESS
}
