// cargo-trust pipeline: compiler invocation, rewrite loop, and standalone analysis
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::env;
use std::ffi::{OsStr, OsString};
use std::io;
use std::io::{BufRead, BufReader};
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode, Output, Stdio};
use std::time::{Instant, SystemTime, UNIX_EPOCH};

use serde::Serialize;
use trust_cache::VerificationCache;

use crate::cli::SubcommandArgs;
use crate::config::TrustConfig;
use crate::report::{CompilerDiagnostic, ReportConfig, VerificationReport};
use crate::source_analysis;
use crate::types::{
    OutputFormat, Subcommand, VerificationOutcome, VerificationResult, parse_trust_note,
    transport_to_verification_result,
};

#[derive(Debug, Clone, Copy, Default)]
pub(crate) struct NativeRustcCapabilities {
    pub(crate) trust_verify: bool,
    pub(crate) json_transport: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum NativeRustcDiscoverySource {
    #[serde(rename = "trustc_env")]
    TrustRustcEnv,
    #[serde(rename = "sibling_trustc")]
    SiblingCargoTrust,
    RustupToolchainTrust,
    RepoLocalStage2,
    RepoLocalStage1,
}

impl NativeRustcDiscoverySource {
    pub(crate) fn label(self) -> &'static str {
        match self {
            Self::TrustRustcEnv => "TRUSTC",
            Self::SiblingCargoTrust => "sibling trustc next to `cargo-trust`",
            Self::RustupToolchainTrust => "linked rustup toolchain `trust`",
            Self::RepoLocalStage2 => "repo-local stage2 build",
            Self::RepoLocalStage1 => "repo-local stage1 build",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub(crate) struct NativeRustcDiscovery {
    pub(crate) rustc: PathBuf,
    pub(crate) source: NativeRustcDiscoverySource,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum LinkedTrustToolchainStatusKind {
    Visible,
    Missing,
    RustupUnavailable,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub(crate) struct LinkedTrustToolchainStatus {
    pub(crate) status: LinkedTrustToolchainStatusKind,
    pub(crate) rustc: Option<PathBuf>,
    pub(crate) detail: Option<String>,
}

impl LinkedTrustToolchainStatus {
    pub(crate) fn is_visible(&self) -> bool {
        matches!(self.status, LinkedTrustToolchainStatusKind::Visible)
    }
}

// ---------------------------------------------------------------------------
// Utility functions (used by pipeline and main)
// ---------------------------------------------------------------------------

pub(crate) fn has_edition(args: &[String]) -> bool {
    args.iter().any(|arg| arg == "--edition" || arg.starts_with("--edition="))
}

pub(crate) fn has_output_path_flag(args: &[String]) -> bool {
    args.iter().any(|arg| arg == "-o" || arg == "--out-dir" || arg.starts_with("--out-dir="))
}

fn temp_single_file_output_path(args: &[String]) -> PathBuf {
    let stem = args
        .iter()
        .find(|arg| arg.ends_with(".rs"))
        .and_then(|arg| Path::new(arg).file_stem())
        .and_then(|stem| stem.to_str())
        .filter(|stem| !stem.is_empty())
        .unwrap_or("trust-check");
    let nanos = SystemTime::now().duration_since(UNIX_EPOCH).map(|d| d.as_nanos()).unwrap_or(0);
    let suffix = if cfg!(windows) { ".exe" } else { "" };
    env::temp_dir().join(format!("cargo-trust-{stem}-{}-{nanos}{suffix}", std::process::id()))
}

/// Convert level string to numeric value for -Z trust-verify-level.
pub(crate) fn level_to_num(level: &str) -> u8 {
    match level {
        "L0" => 0,
        "L1" => 1,
        "L2" => 2,
        _ => 0,
    }
}

pub(crate) fn compiler_help_supports_option(help: &str, option: &str) -> bool {
    help.lines().any(|line| line.contains(option))
}

const TRUST_VERIFY_PROBE_SOURCE: &str = r#"
pub fn trust_verify_probe(a: usize, b: usize) -> usize {
    (a + b) / 2
}
"#;

fn temp_probe_path(suffix: &str) -> PathBuf {
    let nanos = SystemTime::now().duration_since(UNIX_EPOCH).map(|d| d.as_nanos()).unwrap_or(0);
    env::temp_dir().join(format!("cargo-trust-probe-{}-{nanos}{suffix}", std::process::id()))
}

fn push_unique_existing_dir(paths: &mut Vec<PathBuf>, candidate: PathBuf) {
    let candidate = canonicalize_or_self(candidate);
    if candidate.is_dir() && !paths.iter().any(|path| path == &candidate) {
        paths.push(candidate);
    }
}

fn native_runtime_library_paths(rustc: &Path) -> Vec<PathBuf> {
    let mut paths = Vec::new();
    let Some(bin_dir) = rustc.parent() else {
        return paths;
    };
    let Some(sysroot) = bin_dir.parent() else {
        return paths;
    };

    push_unique_existing_dir(&mut paths, sysroot.join("lib"));

    let rustlib_root = sysroot.join("lib").join("rustlib");
    if let Ok(entries) = std::fs::read_dir(&rustlib_root) {
        for entry in entries.flatten() {
            push_unique_existing_dir(&mut paths, entry.path().join("lib"));
        }
    }

    if let (Some(build_dir), Some(stage_name)) =
        (sysroot.parent(), sysroot.file_name().and_then(|name| name.to_str()))
    {
        let rustc_deps_root = build_dir.join(format!("{stage_name}-rustc"));
        if let Ok(entries) = std::fs::read_dir(&rustc_deps_root) {
            for entry in entries.flatten() {
                push_unique_existing_dir(&mut paths, entry.path().join("release").join("deps"));
            }
        }
    }

    paths
}

fn merged_search_path_value(
    mut extra_paths: Vec<PathBuf>,
    existing: Option<&OsStr>,
) -> Option<OsString> {
    if let Some(existing) = existing {
        for path in env::split_paths(existing) {
            if !path.as_os_str().is_empty() && !extra_paths.iter().any(|existing| existing == &path)
            {
                extra_paths.push(path);
            }
        }
    }

    if extra_paths.is_empty() { None } else { env::join_paths(extra_paths).ok() }
}

fn runtime_library_path_var() -> Option<&'static str> {
    if cfg!(windows) {
        None
    } else if cfg!(target_os = "macos") {
        Some("DYLD_LIBRARY_PATH")
    } else {
        Some("LD_LIBRARY_PATH")
    }
}

fn apply_native_runtime_env(cmd: &mut Command, rustc: &Path) {
    let Some(path_var) = runtime_library_path_var() else {
        return;
    };
    let merged = merged_search_path_value(
        native_runtime_library_paths(rustc),
        env::var_os(path_var).as_deref(),
    );
    if let Some(merged) = merged {
        cmd.env(path_var, merged);
    }
}

fn output_contains_json_transport(output: &Output) -> bool {
    String::from_utf8_lossy(&output.stderr).contains(trust_types::TRANSPORT_PREFIX)
}

fn output_contains_native_verification_signal(output: &Output) -> bool {
    let stderr = String::from_utf8_lossy(&output.stderr);
    stderr.contains(trust_types::TRANSPORT_PREFIX)
        || stderr.contains("=== tRust Verification Report ===")
        || stderr.contains("note: tRust [")
        || stderr.contains("tRust [")
}

fn run_native_compile_probe(rustc: &Path, json_transport: bool) -> io::Result<Output> {
    let src = temp_probe_path(".rs");
    let out = temp_probe_path(".rmeta");
    std::fs::write(&src, TRUST_VERIFY_PROBE_SOURCE)?;

    let mut cmd = Command::new(rustc);
    apply_native_runtime_env(&mut cmd, rustc);
    cmd.env("TRUST_VERIFY", "1")
        .arg("-Z")
        .arg("trust-verify")
        .arg("--edition")
        .arg("2021")
        .arg("--crate-name")
        .arg("trust_verify_probe")
        .arg("--crate-type")
        .arg("lib")
        .arg("--emit")
        .arg("metadata")
        .arg("-o")
        .arg(&out);
    if json_transport {
        cmd.arg("-Z").arg("trust-verify-output=json");
    }
    cmd.arg(&src);

    let output = cmd.output();
    let _ = std::fs::remove_file(&src);
    let _ = std::fs::remove_file(&out);
    output
}

pub(crate) fn detect_native_rustc_capabilities(rustc: &Path) -> NativeRustcCapabilities {
    if let Ok(output) = run_native_compile_probe(rustc, true) {
        if output.status.success() && output_contains_json_transport(&output) {
            return NativeRustcCapabilities { trust_verify: true, json_transport: true };
        }
    }

    if let Ok(output) = run_native_compile_probe(rustc, false) {
        if output.status.success() && output_contains_native_verification_signal(&output) {
            return NativeRustcCapabilities { trust_verify: true, json_transport: false };
        }
    }

    NativeRustcCapabilities::default()
}

fn append_codegen_backend_rustflag(flags: &mut String, selected_codegen_backend: Option<&str>) {
    if let Some(backend) = selected_codegen_backend {
        if !flags.contains("codegen-backend=") {
            if !flags.is_empty() {
                flags.push(' ');
            }
            flags.push_str("-Z ");
            flags.push_str(&format!("codegen-backend={backend}"));
        }
    }
}

fn append_codegen_backend_args(cmd_args: &mut Vec<String>, selected_codegen_backend: Option<&str>) {
    if let Some(backend) = selected_codegen_backend {
        cmd_args.push("-Z".to_string());
        cmd_args.push(format!("codegen-backend={backend}"));
    }
}

#[cfg(test)]
pub(crate) fn merged_rustflags(level: &str) -> String {
    merged_rustflags_with_backend(level, None)
}

#[cfg(test)]
pub(crate) fn merged_rustflags_with_backend(
    level: &str,
    selected_codegen_backend: Option<&str>,
) -> String {
    merged_rustflags_with_json_transport(level, selected_codegen_backend, true)
}

pub(crate) fn merged_rustflags_with_json_transport(
    level: &str,
    selected_codegen_backend: Option<&str>,
    supports_json_transport: bool,
) -> String {
    let trust_flags = if supports_json_transport {
        format!(
            "-Z trust-verify -Z trust-verify-level={} -Z trust-verify-output=json",
            level_to_num(level)
        )
    } else {
        format!("-Z trust-verify -Z trust-verify-level={}", level_to_num(level))
    };
    let mut merged = match env::var("RUSTFLAGS") {
        Ok(flags) if flags.trim().is_empty() => trust_flags,
        Ok(flags) => {
            let mut merged = flags;
            if !merged.contains("trust-verify") {
                merged.push_str(" -Z trust-verify");
            }
            if !merged.contains("trust-verify-level=") {
                merged.push_str(&format!(" -Z trust-verify-level={}", level_to_num(level)));
            }
            if supports_json_transport && !merged.contains("trust-verify-output=") {
                merged.push_str(" -Z trust-verify-output=json");
            }
            merged
        }
        Err(_) => trust_flags,
    };
    append_codegen_backend_rustflag(&mut merged, selected_codegen_backend);
    merged
}

fn canonicalize_or_self(path: PathBuf) -> PathBuf {
    std::fs::canonicalize(&path).unwrap_or(path)
}

fn trust_compiler_names() -> [&'static str; 2] {
    if cfg!(windows) { ["trustc.exe", "rustc.exe"] } else { ["trustc", "rustc"] }
}

fn sibling_rustc_path(executable: &Path) -> Option<PathBuf> {
    let bin_dir = executable.parent()?;
    trust_compiler_names()
        .into_iter()
        .map(|name| bin_dir.join(name))
        .find(|candidate| candidate.is_file())
        .map(canonicalize_or_self)
}

fn current_exe_sibling_rustc() -> Option<PathBuf> {
    env::current_exe().ok().and_then(|path| sibling_rustc_path(&path))
}

fn non_empty_output_lines(bytes: &[u8]) -> Vec<String> {
    String::from_utf8_lossy(bytes)
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty())
        .map(str::to_owned)
        .collect()
}

fn trim_command_output(bytes: &[u8]) -> Option<String> {
    let lines = non_empty_output_lines(bytes);
    if lines.is_empty() { None } else { Some(lines.join("; ")) }
}

fn rustup_reported_rustc_path(bytes: &[u8]) -> Option<PathBuf> {
    non_empty_output_lines(bytes)
        .into_iter()
        .rev()
        .map(PathBuf::from)
        .find(|path| path.is_file())
}

fn last_non_empty_output_line(bytes: &[u8]) -> Option<String> {
    non_empty_output_lines(bytes).into_iter().last()
}

fn linked_trust_toolchain_status_from_output(output: Output) -> LinkedTrustToolchainStatus {
    if !output.status.success() {
        return LinkedTrustToolchainStatus {
            status: LinkedTrustToolchainStatusKind::Missing,
            rustc: None,
            detail: trim_command_output(&output.stderr)
                .or_else(|| trim_command_output(&output.stdout)),
        };
    }

    if let Some(path) = rustup_reported_rustc_path(&output.stdout) {
        return LinkedTrustToolchainStatus {
            status: LinkedTrustToolchainStatusKind::Visible,
            rustc: Some(canonicalize_or_self(path)),
            detail: None,
        };
    }

    let Some(path_text) = last_non_empty_output_line(&output.stdout) else {
        return LinkedTrustToolchainStatus {
            status: LinkedTrustToolchainStatusKind::Missing,
            rustc: None,
            detail: Some("rustup returned an empty compiler path".to_string()),
        };
    };

    LinkedTrustToolchainStatus {
        status: LinkedTrustToolchainStatusKind::Missing,
        rustc: None,
        detail: Some(format!("rustup reported `{path_text}` but that path is not a file")),
    }
}

fn detect_linked_trust_toolchain_with<F>(mut query_rustup: F) -> LinkedTrustToolchainStatus
where
    F: FnMut() -> io::Result<Output>,
{
    match query_rustup() {
        Ok(output) => linked_trust_toolchain_status_from_output(output),
        Err(error) if error.kind() == io::ErrorKind::NotFound => LinkedTrustToolchainStatus {
            status: LinkedTrustToolchainStatusKind::RustupUnavailable,
            rustc: None,
            detail: Some("`rustup` was not found on PATH".to_string()),
        },
        Err(error) => LinkedTrustToolchainStatus {
            status: LinkedTrustToolchainStatusKind::Missing,
            rustc: None,
            detail: Some(format!("failed to query rustup: {error}")),
        },
    }
}

pub(crate) fn detect_linked_trust_toolchain() -> LinkedTrustToolchainStatus {
    detect_linked_trust_toolchain_with(|| {
        let trustc = Command::new("rustup")
            .args(["which", "--toolchain", "trust", "trustc"])
            .output()?;
        if trustc.status.success() {
            Ok(trustc)
        } else {
            Command::new("rustup").args(["which", "--toolchain", "trust", "rustc"]).output()
        }
    })
}

pub(crate) fn native_cargo_path(rustc: &Path) -> PathBuf {
    rustc
        .parent()
        .map(|bin_dir| bin_dir.join(if cfg!(windows) { "cargo.exe" } else { "cargo" }))
        .filter(|candidate| candidate.is_file())
        .map(canonicalize_or_self)
        .unwrap_or_else(|| PathBuf::from("cargo"))
}

pub(crate) fn is_cargo_program(program: &str) -> bool {
    Path::new(program).file_name().is_some_and(|name| name == "cargo" || name == "cargo.exe")
}

fn repo_local_rustc_candidates(trust_root: &Path) -> Vec<NativeRustcDiscovery> {
    let stage_dirs = [
        ("build/host/stage2/bin", NativeRustcDiscoverySource::RepoLocalStage2),
        ("build/host/stage1/bin", NativeRustcDiscoverySource::RepoLocalStage1),
        ("build/aarch64-apple-darwin/stage2/bin", NativeRustcDiscoverySource::RepoLocalStage2),
        ("build/aarch64-apple-darwin/stage1/bin", NativeRustcDiscoverySource::RepoLocalStage1),
        ("build/x86_64-unknown-linux-gnu/stage2/bin", NativeRustcDiscoverySource::RepoLocalStage2),
        ("build/x86_64-unknown-linux-gnu/stage1/bin", NativeRustcDiscoverySource::RepoLocalStage1),
        ("build/x86_64-apple-darwin/stage2/bin", NativeRustcDiscoverySource::RepoLocalStage2),
        ("build/x86_64-apple-darwin/stage1/bin", NativeRustcDiscoverySource::RepoLocalStage1),
    ];

    stage_dirs
        .into_iter()
        .flat_map(|(dir, source)| {
            trust_compiler_names()
                .into_iter()
                .map(move |name| (trust_root.join(dir).join(name), source))
        })
        .filter_map(|(candidate, source)| {
            candidate.is_file().then(|| NativeRustcDiscovery {
                rustc: canonicalize_or_self(candidate),
                source,
            })
        })
        .collect()
}

pub(crate) fn select_native_rustc_discovery(
    trust_rustc: Option<PathBuf>,
    sibling_rustc: Option<PathBuf>,
    linked_toolchain: &LinkedTrustToolchainStatus,
    repo_candidates: Vec<NativeRustcDiscovery>,
) -> Option<NativeRustcDiscovery> {
    if let Some(rustc) = trust_rustc {
        return Some(NativeRustcDiscovery {
            rustc: canonicalize_or_self(rustc),
            source: NativeRustcDiscoverySource::TrustRustcEnv,
        });
    }

    if let Some(rustc) = sibling_rustc {
        return Some(NativeRustcDiscovery {
            rustc,
            source: NativeRustcDiscoverySource::SiblingCargoTrust,
        });
    }

    if let Some(rustc) = linked_toolchain.rustc.clone() {
        return Some(NativeRustcDiscovery {
            rustc,
            source: NativeRustcDiscoverySource::RustupToolchainTrust,
        });
    }

    repo_candidates.into_iter().next()
}

pub(crate) fn discover_native_rustc() -> Option<NativeRustcDiscovery> {
    let trust_rustc = env::var("TRUSTC")
        .ok()
        .map(PathBuf::from)
        .filter(|path| path.is_file());
    let linked_toolchain = detect_linked_trust_toolchain();
    let trust_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..");
    select_native_rustc_discovery(
        trust_rustc,
        current_exe_sibling_rustc(),
        &linked_toolchain,
        repo_local_rustc_candidates(&trust_root),
    )
}

// ---------------------------------------------------------------------------
// Build command
// ---------------------------------------------------------------------------

/// Build the command for a built local trustc compiler.
#[cfg(test)]
pub(crate) fn build_native_command(
    rustc: &Path,
    subcommand: Subcommand,
    sub_args: &SubcommandArgs,
    config: &TrustConfig,
) -> Vec<String> {
    build_native_command_with_json_transport(rustc, subcommand, sub_args, config, None, true)
}

pub(crate) fn build_native_command_with_json_transport(
    rustc: &Path,
    subcommand: Subcommand,
    sub_args: &SubcommandArgs,
    config: &TrustConfig,
    selected_codegen_backend: Option<&str>,
    supports_json_transport: bool,
) -> Vec<String> {
    if sub_args.is_single_file {
        // Direct rustc invocation for a single .rs file.
        let mut cmd_args = vec![
            rustc.to_string_lossy().to_string(),
            "-Z".to_string(),
            "trust-verify".to_string(),
            "-Z".to_string(),
            format!("trust-verify-level={}", level_to_num(&config.level)),
        ];
        if supports_json_transport {
            cmd_args.push("-Z".to_string());
            cmd_args.push("trust-verify-output=json".to_string());
        }
        append_codegen_backend_args(&mut cmd_args, selected_codegen_backend);
        if !has_edition(&sub_args.passthrough) {
            cmd_args.push("--edition".to_string());
            cmd_args.push("2021".to_string());
        }
        cmd_args.extend(sub_args.passthrough.iter().cloned());
        if subcommand != Subcommand::Build && !has_output_path_flag(&sub_args.passthrough) {
            cmd_args.push("-o".to_string());
            cmd_args
                .push(temp_single_file_output_path(&sub_args.passthrough).display().to_string());
        }
        cmd_args
    } else {
        // Cargo-based invocation for a crate.
        let cargo_cmd = match subcommand {
            Subcommand::Check
            | Subcommand::Report
            | Subcommand::Loop
            | Subcommand::Diff
            | Subcommand::Solvers
            | Subcommand::Init => "check",
            Subcommand::Build => "build",
        };
        let mut cmd_args =
            vec![native_cargo_path(rustc).to_string_lossy().to_string(), cargo_cmd.to_string()];
        cmd_args.extend(sub_args.passthrough.iter().cloned());
        // RUSTC and RUSTFLAGS are set via env in run_compiler
        cmd_args
    }
}

#[derive(Default)]
pub(crate) struct ParsedCompilerOutput {
    pub(crate) verification_results: Vec<VerificationResult>,
    pub(crate) compiler_diagnostics: Vec<CompilerDiagnostic>,
}

pub(crate) fn parse_compiler_stderr<R: BufRead>(reader: R, echo: bool) -> ParsedCompilerOutput {
    let mut verification_results = Vec::new();
    let mut structured_results = Vec::new();
    let mut compiler_diagnostics = Vec::new();
    let mut has_structured = false;

    for line in reader.lines() {
        let line = match line {
            Ok(l) => l,
            Err(_) => continue,
        };

        if line.starts_with(trust_types::TRANSPORT_PREFIX) {
            if let Some(msg) = trust_types::parse_transport_line(&line) {
                has_structured = true;
                if let trust_types::TransportMessage::FunctionResult(func_result) = msg {
                    for r in &func_result.results {
                        structured_results
                            .push(transport_to_verification_result(&func_result.function, r));
                    }
                }
            }
            continue;
        }

        if echo {
            eprintln!("{line}");
        }

        if let Some(result) = parse_trust_note(&line) {
            verification_results.push(result);
        } else if line.contains("error") || line.contains("warning") {
            compiler_diagnostics.push(CompilerDiagnostic {
                level: if line.contains("error") {
                    "error".to_string()
                } else {
                    "warning".to_string()
                },
                message: line,
            });
        }
    }

    if has_structured {
        verification_results = structured_results;
    }

    ParsedCompilerOutput { verification_results, compiler_diagnostics }
}

// ---------------------------------------------------------------------------
// Compiler execution
// ---------------------------------------------------------------------------

/// Run a compiler command, capture diagnostics, produce a report.
pub(crate) fn run_compiler(
    cmd_args: &[String],
    rustc_path: &Path,
    config: &TrustConfig,
    selected_codegen_backend: Option<&str>,
    supports_json_transport: bool,
    format: OutputFormat,
    report_dir: Option<&str>,
    cache: &mut VerificationCache,
) -> ExitCode {
    if cmd_args.is_empty() {
        eprintln!("cargo-trust: internal error: empty command");
        return ExitCode::from(2);
    }

    let program = &cmd_args[0];
    let args = &cmd_args[1..];
    let start = Instant::now();

    let mut cmd = Command::new(program);
    cmd.args(args);
    cmd.env("TRUST_VERIFY", "1");
    cmd.stderr(Stdio::piped());
    apply_native_runtime_env(&mut cmd, rustc_path);

    // For cargo-based invocations, set RUSTC and RUSTFLAGS.
    if is_cargo_program(program) {
        cmd.env("RUSTC", rustc_path);
        cmd.env(
            "RUSTFLAGS",
            merged_rustflags_with_json_transport(
                &config.level,
                selected_codegen_backend,
                supports_json_transport,
            ),
        );
    }

    let mut child = match cmd.spawn() {
        Ok(c) => c,
        Err(e) => {
            eprintln!("cargo-trust: failed to spawn `{program}`: {e}");
            return ExitCode::from(2);
        }
    };

    let mut verification_results = Vec::new();
    let mut compiler_diagnostics = Vec::new();

    if let Some(stderr) = child.stderr.take() {
        let parsed = parse_compiler_stderr(BufReader::new(stderr), true);
        let ParsedCompilerOutput {
            verification_results: parsed_results,
            compiler_diagnostics: parsed_diagnostics,
        } = parsed;
        verification_results = parsed_results;
        compiler_diagnostics = parsed_diagnostics;
    }

    let status = match child.wait() {
        Ok(s) => s,
        Err(e) => {
            eprintln!("cargo-trust: failed to wait for process: {e}");
            return ExitCode::from(2);
        }
    };

    let compiler_exit = status.code().unwrap_or(1);
    let duration_ms = start.elapsed().as_millis() as u64;

    // Count verification outcomes.
    let proved = verification_results.iter().filter(|r| r.outcome.is_proved()).count();
    let failed = verification_results.iter().filter(|r| r.outcome.is_failed()).count();
    let runtime_checked =
        verification_results.iter().filter(|r| r.outcome.is_runtime_checked()).count();
    let unknown = verification_results.iter().filter(|r| r.outcome.is_inconclusive()).count();
    let total = verification_results.len();

    // tRust #580: Store verification results in incremental cache.
    for result in &verification_results {
        let cache_key = format!("{}:{}", result.kind, result.message);
        let verdict = match result.outcome {
            VerificationOutcome::Proved => trust_types::FunctionVerdict::Verified,
            VerificationOutcome::Failed => trust_types::FunctionVerdict::HasViolations,
            VerificationOutcome::RuntimeChecked => trust_types::FunctionVerdict::RuntimeChecked,
            VerificationOutcome::Timeout | VerificationOutcome::Unknown => {
                trust_types::FunctionVerdict::Inconclusive
            }
        };
        let entry = trust_cache::CacheEntry {
            content_hash: format!("{:x}", {
                use std::hash::{Hash, Hasher};

                let mut hasher = std::collections::hash_map::DefaultHasher::new();
                result.kind.hash(&mut hasher);
                result.message.hash(&mut hasher);
                hasher.finish()
            }),
            verdict,
            total_obligations: 1,
            proved: usize::from(result.outcome.is_proved()),
            failed: usize::from(result.outcome.is_failed()),
            unknown: usize::from(result.outcome.is_inconclusive()),
            runtime_checked: usize::from(result.outcome.is_runtime_checked()),
            cached_at: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map(|d| d.as_secs())
                .unwrap_or(0),
            spec_hash: String::new(),
            obligation_results: vec![],
        };
        cache.store(&cache_key, entry);
    }

    // Success means the compiler succeeded and every obligation was fully proved.
    let success = compiler_exit == 0 && failed == 0 && unknown == 0 && runtime_checked == 0;

    let report = VerificationReport {
        success,
        exit_code: compiler_exit,
        proved,
        failed,
        unknown,
        runtime_checked,
        total,
        results: verification_results,
        compiler_diagnostics,
        duration_ms,
        config: ReportConfig {
            level: config.level.clone(),
            timeout_ms: config.timeout_ms,
            enabled: config.enabled,
        },
    };

    report.render(format, report_dir);

    if success { ExitCode::SUCCESS } else { ExitCode::FAILURE }
}

// ---------------------------------------------------------------------------
// Compiler capture (for rewrite loop)
// ---------------------------------------------------------------------------

/// Outcome of a single compiler invocation, for use in the rewrite loop.
#[allow(dead_code)] // Fields used as loop evolves to apply rewrites.
pub(crate) struct CompilerRunResult {
    pub(crate) exit_code: i32,
    pub(crate) verification_results: Vec<VerificationResult>,
    pub(crate) compiler_diagnostics: Vec<CompilerDiagnostic>,
    pub(crate) duration_ms: u64,
}

/// Run a compiler command and capture verification results without rendering.
///
/// Unlike `run_compiler`, this returns the results for loop processing rather
/// than rendering a report and exiting.
pub(crate) fn run_compiler_capture(
    cmd_args: &[String],
    rustc_path: &Path,
    config: &TrustConfig,
    selected_codegen_backend: Option<&str>,
    supports_json_transport: bool,
    quiet: bool,
) -> Result<CompilerRunResult, ExitCode> {
    if cmd_args.is_empty() {
        eprintln!("cargo-trust: internal error: empty command");
        return Err(ExitCode::from(2));
    }

    let program = &cmd_args[0];
    let args = &cmd_args[1..];
    let start = Instant::now();

    let mut cmd = Command::new(program);
    cmd.args(args);
    cmd.env("TRUST_VERIFY", "1");
    cmd.stderr(Stdio::piped());
    apply_native_runtime_env(&mut cmd, rustc_path);

    if is_cargo_program(program) {
        cmd.env("RUSTC", rustc_path);
        cmd.env(
            "RUSTFLAGS",
            merged_rustflags_with_json_transport(
                &config.level,
                selected_codegen_backend,
                supports_json_transport,
            ),
        );
    }

    let mut child = match cmd.spawn() {
        Ok(c) => c,
        Err(e) => {
            eprintln!("cargo-trust: failed to spawn `{program}`: {e}");
            return Err(ExitCode::from(2));
        }
    };

    let mut verification_results = Vec::new();
    let mut compiler_diagnostics = Vec::new();

    if let Some(stderr) = child.stderr.take() {
        let parsed = parse_compiler_stderr(BufReader::new(stderr), !quiet);
        verification_results = parsed.verification_results;
        compiler_diagnostics = parsed.compiler_diagnostics;
    }

    let status = match child.wait() {
        Ok(s) => s,
        Err(e) => {
            eprintln!("cargo-trust: failed to wait for process: {e}");
            return Err(ExitCode::from(2));
        }
    };

    Ok(CompilerRunResult {
        exit_code: status.code().unwrap_or(1),
        verification_results,
        compiler_diagnostics,
        duration_ms: start.elapsed().as_millis() as u64,
    })
}

// ---------------------------------------------------------------------------
// Rewrite loop
// ---------------------------------------------------------------------------

/// Run the prove-strengthen-backprop convergence loop.
///
/// Uses the ad-hoc CLI rewrite loop implementation.
pub(crate) fn run_rewrite_loop(
    rustc: &Path,
    subcommand: Subcommand,
    sub_args: &SubcommandArgs,
    config: &TrustConfig,
    selected_codegen_backend: Option<&str>,
    supports_json_transport: bool,
) -> ExitCode {
    run_rewrite_loop_fallback(
        rustc,
        subcommand,
        sub_args,
        config,
        selected_codegen_backend,
        supports_json_transport,
    )
}
/// Ad-hoc CLI rewrite loop.
fn run_rewrite_loop_fallback(
    rustc: &Path,
    subcommand: Subcommand,
    sub_args: &SubcommandArgs,
    config: &TrustConfig,
    selected_codegen_backend: Option<&str>,
    supports_json_transport: bool,
) -> ExitCode {
    use crate::rewrite_loop::{
        BackpropEngine, ConvergenceTracker, LoopDecision, ProofFrontier, RepairArtifact,
        RepairIteration, RepairRunSummary, append_audit_entries, build_rewrite_records,
        decision_label, print_iteration_header, print_iteration_summary, print_loop_summary,
        strengthen_failures, write_repair_artifact, write_repair_markdown,
    };
    let mut audit_trail = trust_backprop::AuditTrail::new();

    let max_iterations = sub_args.max_iterations;
    let mut tracker = ConvergenceTracker::new(max_iterations);
    let mut backprop = BackpropEngine::with_protected(&config.skip_functions);

    if sub_args.is_single_file {
        let file_path = std::fs::canonicalize(
            sub_args.single_file_path().expect("single-file mode should have a file path"),
        )
            .unwrap_or_else(|_| {
                PathBuf::from(
                    sub_args.single_file_path().expect("single-file mode should have a file path"),
                )
            });
        backprop.set_default_source_file(file_path.display().to_string());
    }

    let loop_start = Instant::now();
    let mut last_frontier = ProofFrontier { proved: 0, failed: 0, unknown: 0 };
    let mut last_decision = LoopDecision::Continue { verdict: "starting" };
    let mut repair_iterations = Vec::new();

    eprintln!();
    eprintln!("cargo-trust: starting rewrite loop (max {} iterations)", max_iterations);

    for iteration in 0..max_iterations {
        let iter_start = Instant::now();
        print_iteration_header(iteration, max_iterations);

        // Step 1: Prove -- run the compiler and capture results.
        let cmd_args = build_native_command_with_json_transport(
            rustc,
            subcommand,
            sub_args,
            config,
            selected_codegen_backend,
            supports_json_transport,
        );
        let run_result = match run_compiler_capture(
            &cmd_args,
            rustc,
            config,
            selected_codegen_backend,
            supports_json_transport,
            iteration > 0,
        ) {
            Ok(r) => r,
            Err(exit_code) => return exit_code,
        };

        // Step 2: Strengthen -- analyze failures and propose rewrites.
        let frontier = ProofFrontier::from_results(&run_result.verification_results);
        let strengthen =
            strengthen_failures(&run_result.verification_results, backprop.default_source_file());
        let proposal_summaries = strengthen.summaries();

        // Step 3: Backprop -- apply rewrites to source via trust-backprop.
        let mut bp_result = crate::rewrite_loop::BackpropResult {
            files_modified: 0,
            rewrites_applied: 0,
            governance_skips: 0,
            limit_skips: 0,
            applied_rewrites: Vec::new(),
            pending_rewrites: Vec::new(),
            file_results: Vec::new(),
        };
        if !strengthen.proposals.is_empty() {
            bp_result = backprop.apply_strengthen_proposals(&strengthen.proposals, 0, 0);
            eprintln!(
                "  Backprop: {} rewrites applied to {} files ({} governance skips, {} limit skips, {} queued for review)",
                bp_result.rewrites_applied,
                bp_result.files_modified,
                bp_result.governance_skips,
                bp_result.limit_skips,
                bp_result.pending_rewrites.len(),
            );
        }

        // Step 4: Converge -- check if the loop should continue.
        let decision = tracker.observe(frontier.clone());
        let iter_elapsed = iter_start.elapsed();
        print_iteration_summary(&frontier, &proposal_summaries, &decision, &iter_elapsed);

        let proposal_records = strengthen.proposal_records();
        let rewrite_records = build_rewrite_records(
            &bp_result.applied_rewrites,
            &bp_result.pending_rewrites,
            &bp_result.file_results,
        );
        append_audit_entries(&mut audit_trail, iteration + 1, &rewrite_records);
        repair_iterations.push(RepairIteration {
            iteration: iteration + 1,
            command: cmd_args,
            exit_code: run_result.exit_code,
            frontier: frontier.clone(),
            results: run_result.verification_results.clone(),
            compiler_diagnostics: run_result.compiler_diagnostics,
            failures: strengthen.failures,
            proposals: proposal_records,
            applied_rewrites: bp_result.applied_rewrites.clone(),
            pending_rewrites: bp_result.pending_rewrites.clone(),
            rewrite_records,
            governance_skips: bp_result.governance_skips,
            limit_skips: bp_result.limit_skips,
            duration_ms: iter_elapsed.as_millis() as u64,
        });

        last_frontier = frontier;
        last_decision = decision.clone();

        match &decision {
            LoopDecision::Continue { .. } => {
                if last_frontier.failed == 0 && last_frontier.unknown == 0 {
                    eprintln!("  All obligations proved -- stopping early.");
                    last_decision = LoopDecision::Converged { stable_rounds: 1 };
                    break;
                }
                if strengthen.proposals.is_empty() && last_frontier.failed > 0 {
                    eprintln!(
                        "  No proposals generated for {} failures -- stopping.",
                        last_frontier.failed
                    );
                    break;
                }
            }
            LoopDecision::Converged { .. }
            | LoopDecision::Regressed { .. }
            | LoopDecision::IterationLimitReached => break,
        }
    }

    let total_elapsed = loop_start.elapsed();
    print_loop_summary(&tracker, &last_frontier, &total_elapsed, &last_decision);

    if let Some(dir) = sub_args.report_dir.as_deref() {
        let artifact = RepairArtifact {
            schema_version: "0.2.0",
            summary: RepairRunSummary {
                iterations: tracker.iteration_count(),
                succeeded: last_frontier.failed == 0,
                final_frontier: last_frontier.clone(),
                final_decision: decision_label(&last_decision),
                total_duration_ms: total_elapsed.as_millis() as u64,
            },
            iterations: repair_iterations,
            audit_trail,
        };
        let output_dir = Path::new(dir);
        match write_repair_artifact(output_dir, &artifact) {
            Ok(()) => eprintln!("cargo-trust: wrote {dir}/repair.json"),
            Err(e) => eprintln!("cargo-trust: failed to write repair artifact: {e}"),
        }
        match write_repair_markdown(output_dir, &artifact) {
            Ok(()) => eprintln!("cargo-trust: wrote {dir}/repair.md"),
            Err(e) => eprintln!("cargo-trust: failed to write repair markdown: {e}"),
        }
    }

    if last_frontier.failed == 0 { ExitCode::SUCCESS } else { ExitCode::FAILURE }
}

// ---------------------------------------------------------------------------
// Standalone source-level analysis mode
// ---------------------------------------------------------------------------

/// Run standalone source-level analysis without invoking the compiler.
pub(crate) fn run_standalone_check(sub_args: &SubcommandArgs, crate_root: &Path) -> ExitCode {
    let start = Instant::now();

    let summary = if sub_args.is_single_file {
        let file = PathBuf::from(
            sub_args.single_file_path().expect("single-file mode should have a file path"),
        );
        if !file.exists() {
            eprintln!("cargo-trust: error: file not found: {}", file.display());
            return ExitCode::from(2);
        }
        eprintln!("cargo-trust: standalone analysis of {}", file.display());
        source_analysis::analyze_file(&file)
    } else {
        eprintln!("cargo-trust: standalone analysis of crate at {}", crate_root.display());
        source_analysis::analyze_crate(crate_root)
    };

    let duration_ms = start.elapsed().as_millis() as u64;

    match sub_args.format {
        OutputFormat::Json => {
            render_standalone_json(&summary, duration_ms);
        }
        OutputFormat::Terminal | OutputFormat::Html => {
            render_standalone_terminal(&summary, duration_ms);
        }
    }

    if summary.failed == 0 { ExitCode::SUCCESS } else { ExitCode::FAILURE }
}

fn render_standalone_terminal(summary: &source_analysis::SourceAnalysisSummary, duration_ms: u64) {
    eprintln!();
    eprintln!("=== tRust Standalone Verification Report ===");
    eprintln!("Mode: source analysis | Duration: {}ms", duration_ms);
    eprintln!();
    eprintln!("Files analyzed:      {}", summary.files_analyzed);
    eprintln!("Functions found:     {}", summary.functions_found);
    eprintln!("  Public:            {}", summary.public_functions);
    eprintln!("  Unsafe:            {}", summary.unsafe_functions);
    eprintln!("  With specs:        {}", summary.specified_functions);
    eprintln!();

    if summary.vcs.is_empty() {
        eprintln!("  No verification obligations generated.");
    } else {
        for vc in &summary.vcs {
            let icon = match vc.outcome {
                source_analysis::StandaloneOutcome::Proved => "PROVED",
                source_analysis::StandaloneOutcome::Failed => "FAILED",
                source_analysis::StandaloneOutcome::Unknown => "UNKNOWN",
            };
            let kind_str = match vc.kind {
                source_analysis::VcKind::PreconditionPresent => "requires",
                source_analysis::VcKind::PostconditionPresent => "ensures",
                source_analysis::VcKind::UnsafeFunction => "unsafe",
                source_analysis::VcKind::UnspecifiedPublicApi => "no-spec",
            };
            eprintln!("  [{icon}] [{kind_str}] {}", vc.description);
        }
    }

    eprintln!();
    eprintln!(
        "Summary: {} proved, {} failed, {} unknown ({} total VCs)",
        summary.proved, summary.failed, summary.unknown, summary.total_vcs
    );
    let status = if summary.failed == 0 { "PASS" } else { "FAIL" };
    eprintln!("Result: {status}");
    eprintln!("=============================================");
}

fn render_standalone_json(summary: &source_analysis::SourceAnalysisSummary, duration_ms: u64) {
    #[derive(Serialize)]
    struct JsonReport<'a> {
        mode: &'static str,
        duration_ms: u64,
        #[serde(flatten)]
        summary: &'a source_analysis::SourceAnalysisSummary,
    }
    let report = JsonReport { mode: "standalone", duration_ms, summary };
    match serde_json::to_string_pretty(&report) {
        Ok(json) => println!("{json}"),
        Err(e) => eprintln!("cargo-trust: failed to serialize report: {e}"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::process::ExitStatus;
    use std::time::{SystemTime, UNIX_EPOCH};

    #[cfg(unix)]
    fn exit_status(success: bool) -> ExitStatus {
        use std::os::unix::process::ExitStatusExt;

        ExitStatus::from_raw(if success { 0 } else { 1 })
    }

    #[cfg(windows)]
    fn exit_status(success: bool) -> ExitStatus {
        use std::os::windows::process::ExitStatusExt;

        ExitStatus::from_raw(if success { 0 } else { 1 })
    }

    fn temp_test_dir(label: &str) -> PathBuf {
        let unique = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("clock should be after epoch")
            .as_nanos();
        env::temp_dir()
            .join(format!("cargo-trust-pipeline-{label}-{}-{unique}", std::process::id()))
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
    fn test_linked_trust_toolchain_status_from_output_visible() {
        let root = temp_test_dir("linked-toolchain");
        let bin_dir = root.join("bin");
        std::fs::create_dir_all(&bin_dir).expect("should create bin dir");

        let rustc = bin_dir.join(if cfg!(windows) { "trustc.exe" } else { "trustc" });
        std::fs::write(&rustc, "").expect("should create trustc marker");

        let output = Output {
            status: exit_status(true),
            stdout: format!("{}\n", rustc.display()).into_bytes(),
            stderr: vec![],
        };

        let status = linked_trust_toolchain_status_from_output(output);
        assert!(status.is_visible());
        assert_eq!(status.status, LinkedTrustToolchainStatusKind::Visible);
        assert_eq!(status.rustc, Some(canonicalize_or_self(rustc.clone())));
        assert!(status.detail.is_none());

        std::fs::remove_dir_all(&root).expect("should remove temp dir");
    }

    #[test]
    fn test_linked_trust_toolchain_status_from_output_uses_last_existing_path_line() {
        let root = temp_test_dir("linked-toolchain-multiline");
        let bin_dir = root.join("bin");
        std::fs::create_dir_all(&bin_dir).expect("should create bin dir");

        let rustc = bin_dir.join(if cfg!(windows) { "trustc.exe" } else { "trustc" });
        std::fs::write(&rustc, "").expect("should create trustc marker");

        let output = Output {
            status: exit_status(true),
            stdout: format!("info: using linked toolchain\n{}\n", rustc.display()).into_bytes(),
            stderr: vec![],
        };

        let status = linked_trust_toolchain_status_from_output(output);
        assert!(status.is_visible());
        assert_eq!(status.rustc, Some(canonicalize_or_self(rustc.clone())));

        std::fs::remove_dir_all(&root).expect("should remove temp dir");
    }

    #[test]
    fn test_linked_trust_toolchain_status_from_output_empty_stdout() {
        let output = Output { status: exit_status(true), stdout: vec![], stderr: vec![] };

        let status = linked_trust_toolchain_status_from_output(output);
        assert_eq!(status.status, LinkedTrustToolchainStatusKind::Missing);
        assert_eq!(status.detail.as_deref(), Some("rustup returned an empty compiler path"));
    }

    #[test]
    fn test_detect_linked_trust_toolchain_with_rustup_unavailable() {
        let status = detect_linked_trust_toolchain_with(|| {
            Err(io::Error::new(io::ErrorKind::NotFound, "rustup missing"))
        });

        assert_eq!(status.status, LinkedTrustToolchainStatusKind::RustupUnavailable);
        assert_eq!(status.detail.as_deref(), Some("`rustup` was not found on PATH"));
    }

    #[test]
    fn test_select_native_rustc_discovery_priority() {
        let env_rustc = PathBuf::from("/tmp/trustc");
        let sibling_rustc = PathBuf::from("/tmp/cargo-trust/trustc");
        let repo_candidates = vec![
            NativeRustcDiscovery {
                rustc: PathBuf::from("/tmp/repo/stage2/trustc"),
                source: NativeRustcDiscoverySource::RepoLocalStage2,
            },
            NativeRustcDiscovery {
                rustc: PathBuf::from("/tmp/repo/stage1/trustc"),
                source: NativeRustcDiscoverySource::RepoLocalStage1,
            },
        ];

        let selected = select_native_rustc_discovery(
            Some(env_rustc.clone()),
            Some(sibling_rustc.clone()),
            &linked_toolchain_status(Some(PathBuf::from("/tmp/rustup/trust/trustc"))),
            repo_candidates.clone(),
        )
        .expect("expected TRUSTC selection");
        assert_eq!(selected.source, NativeRustcDiscoverySource::TrustRustcEnv);
        assert_eq!(selected.rustc, env_rustc);

        let selected = select_native_rustc_discovery(
            None,
            Some(sibling_rustc.clone()),
            &linked_toolchain_status(Some(PathBuf::from("/tmp/rustup/trust/trustc"))),
            repo_candidates.clone(),
        )
        .expect("expected sibling selection");
        assert_eq!(selected.source, NativeRustcDiscoverySource::SiblingCargoTrust);
        assert_eq!(selected.rustc, sibling_rustc);

        let selected = select_native_rustc_discovery(
            None,
            None,
            &linked_toolchain_status(Some(PathBuf::from("/tmp/rustup/trust/trustc"))),
            repo_candidates.clone(),
        )
        .expect("expected linked toolchain selection");
        assert_eq!(selected.source, NativeRustcDiscoverySource::RustupToolchainTrust);
        assert_eq!(selected.rustc, PathBuf::from("/tmp/rustup/trust/trustc"));

        let selected = select_native_rustc_discovery(
            None,
            None,
            &linked_toolchain_status(None),
            repo_candidates,
        )
        .expect("expected repo fallback");
        assert_eq!(selected.source, NativeRustcDiscoverySource::RepoLocalStage2);
        assert_eq!(selected.rustc, PathBuf::from("/tmp/repo/stage2/trustc"));
    }

    #[test]
    fn test_native_runtime_library_paths_include_sysroot_rustlib_and_stage_rustc_deps() {
        let root = temp_test_dir("runtime-paths");
        let rustc = root.join("build/host/stage1/bin/rustc");
        let sysroot_lib = root.join("build/host/stage1/lib");
        let rustlib_lib = root.join("build/host/stage1/lib/rustlib/test-triple/lib");
        let stage_deps = root.join("build/host/stage1-rustc/host/release/deps");

        std::fs::create_dir_all(rustc.parent().expect("rustc should have parent"))
            .expect("should create rustc bin dir");
        std::fs::write(&rustc, "").expect("should create rustc marker");
        std::fs::create_dir_all(&sysroot_lib).expect("should create sysroot lib");
        std::fs::create_dir_all(&rustlib_lib).expect("should create rustlib lib");
        std::fs::create_dir_all(&stage_deps).expect("should create stage deps dir");

        let paths = native_runtime_library_paths(&rustc);
        assert!(paths.contains(&canonicalize_or_self(sysroot_lib.clone())));
        assert!(paths.contains(&canonicalize_or_self(rustlib_lib.clone())));
        assert!(paths.contains(&canonicalize_or_self(stage_deps.clone())));

        std::fs::remove_dir_all(&root).expect("should remove temp dir");
    }

    #[test]
    fn test_merged_search_path_value_appends_existing_without_duplicates() {
        let root = temp_test_dir("merged-search-paths");
        let extra_a = root.join("extra-a");
        let extra_b = root.join("extra-b");
        let existing = root.join("existing");

        std::fs::create_dir_all(&extra_a).expect("should create extra_a");
        std::fs::create_dir_all(&extra_b).expect("should create extra_b");
        std::fs::create_dir_all(&existing).expect("should create existing");

        let existing_joined = env::join_paths([
            canonicalize_or_self(existing.clone()),
            canonicalize_or_self(extra_a.clone()),
        ])
        .expect("should join existing search path");

        let merged = merged_search_path_value(
            vec![canonicalize_or_self(extra_a.clone()), canonicalize_or_self(extra_b.clone())],
            Some(existing_joined.as_os_str()),
        )
        .expect("merged search path should exist");

        let split: Vec<PathBuf> = env::split_paths(&merged).collect();
        assert_eq!(
            split,
            vec![
                canonicalize_or_self(extra_a.clone()),
                canonicalize_or_self(extra_b.clone()),
                canonicalize_or_self(existing.clone()),
            ]
        );

        std::fs::remove_dir_all(&root).expect("should remove temp dir");
    }
}
