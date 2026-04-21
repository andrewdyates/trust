// cargo-trust pipeline: compiler invocation, rewrite loop, and standalone analysis
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::env;
use std::io::{BufRead, BufReader};
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode, Stdio};
use std::time::Instant;

use serde::Serialize;
use trust_cache::VerificationCache;

use crate::cli::SubcommandArgs;
use crate::config::TrustConfig;
use crate::report::{CompilerDiagnostic, ReportConfig, VerificationReport};
use crate::source_analysis;
use crate::types::{
    OutputFormat, Subcommand, VerificationOutcome, VerificationResult,
    parse_trust_note, transport_to_verification_result,
};

// ---------------------------------------------------------------------------
// Utility functions (used by pipeline and main)
// ---------------------------------------------------------------------------

pub(crate) fn has_edition(args: &[String]) -> bool {
    args.iter()
        .any(|arg| arg == "--edition" || arg.starts_with("--edition="))
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

pub(crate) fn merged_rustflags(level: &str) -> String {
    let trust_flags = format!(
        "-Z trust-verify -Z trust-verify-level={}",
        level_to_num(level)
    );
    match env::var("RUSTFLAGS") {
        Ok(flags) if flags.contains("trust-verify") => flags,
        Ok(flags) if flags.trim().is_empty() => trust_flags,
        Ok(flags) => format!("{flags} {trust_flags}"),
        Err(_) => trust_flags,
    }
}

pub(crate) fn find_native_rustc() -> Option<PathBuf> {
    // First: explicit env override.
    if let Ok(path) = env::var("TRUST_RUSTC") {
        let candidate = PathBuf::from(path);
        if candidate.is_file() {
            return Some(candidate);
        }
    }

    // Second: discover from repo layout.
    let trust_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..");
    let candidates = [
        trust_root.join("build/host/stage1/bin/rustc"),
        trust_root.join("build/aarch64-apple-darwin/stage1/bin/rustc"),
        trust_root.join("build/x86_64-unknown-linux-gnu/stage1/bin/rustc"),
        trust_root.join("build/x86_64-apple-darwin/stage1/bin/rustc"),
    ];

    candidates.into_iter().find(|candidate| candidate.is_file())
}

// ---------------------------------------------------------------------------
// Build command
// ---------------------------------------------------------------------------

/// Build the command for native stage1 rustc invocation.
pub(crate) fn build_native_command(
    rustc: &Path,
    subcommand: Subcommand,
    sub_args: &SubcommandArgs,
    config: &TrustConfig,
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
        if !has_edition(&sub_args.passthrough) {
            cmd_args.push("--edition".to_string());
            cmd_args.push("2021".to_string());
        }
        cmd_args.extend(sub_args.passthrough.iter().cloned());
        cmd_args
    } else {
        // Cargo-based invocation for a crate.
        let cargo_cmd = match subcommand {
            Subcommand::Check | Subcommand::Report | Subcommand::Loop | Subcommand::Diff
            | Subcommand::Solvers | Subcommand::Init => {
                "check"
            }
            Subcommand::Build => "build",
        };
        let mut cmd_args = vec!["cargo".to_string(), cargo_cmd.to_string()];
        cmd_args.extend(sub_args.passthrough.iter().cloned());
        // RUSTC and RUSTFLAGS are set via env in run_compiler
        cmd_args
    }
}

// ---------------------------------------------------------------------------
// Compiler execution
// ---------------------------------------------------------------------------

/// Run a compiler command, capture diagnostics, produce a report.
pub(crate) fn run_compiler(
    cmd_args: &[String],
    rustc_path: &Path,
    config: &TrustConfig,
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

    // For cargo-based invocations, set RUSTC and RUSTFLAGS.
    if program == "cargo" {
        cmd.env("RUSTC", rustc_path);
        cmd.env("RUSTFLAGS", merged_rustflags(&config.level));
    }

    let mut child = match cmd.spawn() {
        Ok(c) => c,
        Err(e) => {
            eprintln!("cargo-trust: failed to spawn `{program}`: {e}");
            return ExitCode::from(2);
        }
    };

    // Capture stderr: parse tRust notes, pass through everything else.
    // tRust #542: Also parse TRUST_JSON: lines for structured transport.
    // When structured data is available, it is preferred over text parsing.
    let mut verification_results = Vec::new();
    let mut structured_results: Vec<VerificationResult> = Vec::new();
    let mut compiler_diagnostics = Vec::new();
    let mut has_structured = false;

    if let Some(stderr) = child.stderr.take() {
        let reader = BufReader::new(stderr);
        for line in reader.lines() {
            let line = match line {
                Ok(l) => l,
                Err(_) => continue,
            };

            // tRust #542: Check for structured JSON transport lines first.
            if line.starts_with(trust_types::TRANSPORT_PREFIX) {
                // Don't pass through JSON transport lines to the user's terminal.
                if let Some(msg) = trust_types::parse_transport_line(&line) {
                    has_structured = true;
                    if let trust_types::TransportMessage::FunctionResult(func_result) = msg {
                        for r in &func_result.results {
                            structured_results.push(transport_to_verification_result(r));
                        }
                    }
                }
                continue;
            }

            // Pass through all other output to the user's terminal.
            eprintln!("{line}");

            // Try to parse as a tRust verification note (text fallback).
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
    }

    // tRust #542: Prefer structured results when available.
    if has_structured {
        verification_results = structured_results;
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
    let proved = verification_results
        .iter()
        .filter(|r| r.outcome == VerificationOutcome::Proved)
        .count();
    let failed = verification_results
        .iter()
        .filter(|r| r.outcome == VerificationOutcome::Failed)
        .count();
    let unknown = verification_results
        .iter()
        .filter(|r| r.outcome == VerificationOutcome::Unknown)
        .count();
    let total = verification_results.len();

    // tRust #580: Store verification results in incremental cache.
    for result in &verification_results {
        let cache_key = format!("{}:{}", result.kind, result.message);
        let verdict = match result.outcome {
            VerificationOutcome::Proved => trust_types::FunctionVerdict::Verified,
            VerificationOutcome::Failed => trust_types::FunctionVerdict::HasViolations,
            VerificationOutcome::Unknown => trust_types::FunctionVerdict::Inconclusive,
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
            proved: if result.outcome == VerificationOutcome::Proved {
                1
            } else {
                0
            },
            failed: if result.outcome == VerificationOutcome::Failed {
                1
            } else {
                0
            },
            unknown: if result.outcome == VerificationOutcome::Unknown {
                1
            } else {
                0
            },
            runtime_checked: 0,
            cached_at: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map(|d| d.as_secs())
                .unwrap_or(0),
            spec_hash: String::new(),
        };
        cache.store(&cache_key, entry);
    }

    // Success = compiler succeeded AND no verification failures.
    let success = compiler_exit == 0 && failed == 0;

    let report = VerificationReport {
        success,
        exit_code: compiler_exit,
        proved,
        failed,
        unknown,
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

    if success {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}

// ---------------------------------------------------------------------------
// Compiler capture (for rewrite loop)
// ---------------------------------------------------------------------------

/// Outcome of a single compiler invocation, for use in the rewrite loop.
#[allow(dead_code)] // Fields used as loop evolves to apply rewrites.
pub(crate) struct CompilerRunResult {
    pub(crate) exit_code: i32,
    pub(crate) verification_results: Vec<VerificationResult>,
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

    if program == "cargo" {
        cmd.env("RUSTC", rustc_path);
        cmd.env("RUSTFLAGS", merged_rustflags(&config.level));
    }

    let mut child = match cmd.spawn() {
        Ok(c) => c,
        Err(e) => {
            eprintln!("cargo-trust: failed to spawn `{program}`: {e}");
            return Err(ExitCode::from(2));
        }
    };

    let mut verification_results = Vec::new();

    if let Some(stderr) = child.stderr.take() {
        let reader = BufReader::new(stderr);
        for line in reader.lines() {
            let line = match line {
                Ok(l) => l,
                Err(_) => continue,
            };
            if !quiet {
                eprintln!("{line}");
            }
            if let Some(result) = parse_trust_note(&line) {
                verification_results.push(result);
            }
        }
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
        duration_ms: start.elapsed().as_millis() as u64,
    })
}

// ---------------------------------------------------------------------------
// Rewrite loop
// ---------------------------------------------------------------------------

/// Run the prove-strengthen-backprop convergence loop.
///
/// First attempts to delegate to trust-driver's production pipeline phases,
/// falls back to the ad-hoc CLI loop if trust-driver invocation fails.
pub(crate) fn run_rewrite_loop(
    rustc: &Path,
    subcommand: Subcommand,
    sub_args: &SubcommandArgs,
    config: &TrustConfig,
) -> ExitCode {
    // tRust #541: Try trust-driver production pipeline first.
    if let Some(exit_code) = try_driver_loop(rustc, sub_args, config) {
        return exit_code;
    }

    // Fallback: ad-hoc CLI loop.
    eprintln!("cargo-trust: falling back to CLI rewrite loop");
    run_rewrite_loop_fallback(rustc, subcommand, sub_args, config)
}

/// Attempt to run the rewrite loop via trust-driver's production pipeline.
///
/// Returns `Some(ExitCode)` on success (including verification failures),
/// or `None` if trust-driver cannot be used and the caller should fall back.
fn try_driver_loop(
    rustc: &Path,
    sub_args: &SubcommandArgs,
    config: &TrustConfig,
) -> Option<ExitCode> {
    use trust_driver::{
        LoopConfig, ProductionBackpropPhase, ProductionStrengthenPhase,
        ProductionVerifyPhase, TerminationReason,
    };
    use trust_backprop::GovernancePolicy;
    use trust_strengthen::StrengthenConfig;

    // Derive the stage1 directory from the rustc binary path.
    let stage1_dir = rustc.parent().and_then(|bin| bin.parent())?;

    eprintln!(
        "cargo-trust: using trust-driver production pipeline (stage1: {})",
        stage1_dir.display()
    );

    let verify = ProductionVerifyPhase::new(stage1_dir.to_path_buf());
    let strengthen = ProductionStrengthenPhase::heuristic_only(StrengthenConfig::default());
    let backprop = ProductionBackpropPhase::new(GovernancePolicy {
        protected_functions: config.skip_functions.clone(),
        ..GovernancePolicy::default()
    });

    let loop_config = LoopConfig {
        max_iterations: sub_args.max_iterations as u32,
        stable_round_limit: 2,
        allow_rewrite: true,
        run_debug: false,
    };

    let source_path = if sub_args.is_single_file {
        PathBuf::from(&sub_args.passthrough[0])
    } else {
        env::current_dir().unwrap_or_else(|_| PathBuf::from("."))
    };

    let loop_start = Instant::now();
    let result = trust_driver::run_loop(
        &source_path,
        &loop_config,
        &verify,
        &strengthen,
        &backprop,
    );
    let total_elapsed = loop_start.elapsed();

    // Report results.
    eprintln!();
    eprintln!("=== tRust Production Loop Summary ===");
    eprintln!("  Iterations: {}", result.iterations);
    eprintln!(
        "  Final frontier: {} trusted, {} failed, {} unknown",
        result.final_frontier.trusted,
        result.final_frontier.failed,
        result.final_frontier.unknown,
    );

    let outcome_str = match &result.reason {
        TerminationReason::AllProved => "ALL PROVED",
        TerminationReason::Converged { stable_rounds } => {
            eprintln!("  Stable rounds: {stable_rounds}");
            "CONVERGED"
        }
        TerminationReason::IterationLimit { iterations } => {
            eprintln!("  Hit limit at {iterations} iterations");
            "ITERATION LIMIT"
        }
        TerminationReason::Regressed => "REGRESSED",
        TerminationReason::NoProposals => "NO PROPOSALS",
    };
    eprintln!("  Outcome: {outcome_str}");
    eprintln!("  Total time: {}ms", total_elapsed.as_millis());
    eprintln!("=====================================");

    if result.final_frontier.failed == 0 {
        Some(ExitCode::SUCCESS)
    } else {
        Some(ExitCode::FAILURE)
    }
}

/// Ad-hoc CLI rewrite loop fallback when trust-driver is not available.
fn run_rewrite_loop_fallback(
    rustc: &Path,
    subcommand: Subcommand,
    sub_args: &SubcommandArgs,
    config: &TrustConfig,
) -> ExitCode {
    use crate::rewrite_loop::{
        BackpropEngine, ConvergenceTracker, LoopDecision, ProofFrontier,
        print_iteration_header, print_iteration_summary, print_loop_summary,
        propose_rewrites,
    };

    let max_iterations = sub_args.max_iterations;
    let mut tracker = ConvergenceTracker::new(max_iterations);
    let mut backprop = BackpropEngine::with_protected(&config.skip_functions);

    if sub_args.is_single_file {
        let file_path = std::fs::canonicalize(&sub_args.passthrough[0])
            .unwrap_or_else(|_| PathBuf::from(&sub_args.passthrough[0]));
        backprop.set_default_source_file(file_path.display().to_string());
    }

    let loop_start = Instant::now();
    let mut last_frontier = ProofFrontier { proved: 0, failed: 0, unknown: 0 };
    let mut last_decision = LoopDecision::Continue { verdict: "starting" };

    eprintln!();
    eprintln!("cargo-trust: starting rewrite loop (max {} iterations)", max_iterations);

    for iteration in 0..max_iterations {
        let iter_start = Instant::now();
        print_iteration_header(iteration, max_iterations);

        // Step 1: Prove -- run the compiler and capture results.
        let cmd_args = build_native_command(rustc, subcommand, sub_args, config);
        let run_result = match run_compiler_capture(&cmd_args, rustc, config, iteration > 0) {
            Ok(r) => r,
            Err(exit_code) => return exit_code,
        };

        // Step 2: Strengthen -- analyze failures and propose rewrites.
        let frontier = ProofFrontier::from_results(&run_result.verification_results);
        let proposals = propose_rewrites(&run_result.verification_results);

        // Step 3: Backprop -- apply rewrites to source via trust-backprop.
        if !proposals.is_empty() {
            let bp_result = backprop.apply(&proposals, &run_result.verification_results);
            eprintln!(
                "  Backprop: {} rewrites applied to {} files ({} governance skips, {} limit skips)",
                bp_result.rewrites_applied,
                bp_result.files_modified,
                bp_result.governance_skips,
                bp_result.limit_skips,
            );
        }

        // Step 4: Converge -- check if the loop should continue.
        let decision = tracker.observe(frontier.clone());
        let iter_elapsed = iter_start.elapsed();
        print_iteration_summary(&frontier, &proposals, &decision, &iter_elapsed);

        last_frontier = frontier;
        last_decision = decision.clone();

        match &decision {
            LoopDecision::Continue { .. } => {
                if last_frontier.failed == 0 && last_frontier.unknown == 0 {
                    eprintln!("  All obligations proved -- stopping early.");
                    last_decision = LoopDecision::Converged { stable_rounds: 1 };
                    break;
                }
                if proposals.is_empty() && last_frontier.failed > 0 {
                    eprintln!("  No proposals generated for {} failures -- stopping.",
                        last_frontier.failed);
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

    if last_frontier.failed == 0 {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}

// ---------------------------------------------------------------------------
// Standalone source-level analysis mode
// ---------------------------------------------------------------------------

/// Run standalone source-level analysis without invoking the compiler.
pub(crate) fn run_standalone_check(sub_args: &SubcommandArgs, crate_root: &Path) -> ExitCode {
    let start = Instant::now();

    let summary = if sub_args.is_single_file {
        let file = PathBuf::from(&sub_args.passthrough[0]);
        if !file.exists() {
            eprintln!(
                "cargo-trust: error: file not found: {}",
                file.display()
            );
            return ExitCode::from(2);
        }
        eprintln!(
            "cargo-trust: standalone analysis of {}",
            file.display()
        );
        source_analysis::analyze_file(&file)
    } else {
        eprintln!(
            "cargo-trust: standalone analysis of crate at {}",
            crate_root.display()
        );
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

    if summary.failed == 0 {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}

fn render_standalone_terminal(
    summary: &source_analysis::SourceAnalysisSummary,
    duration_ms: u64,
) {
    eprintln!();
    eprintln!("=== tRust Standalone Verification Report ===");
    eprintln!(
        "Mode: source analysis | Duration: {}ms",
        duration_ms
    );
    eprintln!();
    eprintln!(
        "Files analyzed:      {}",
        summary.files_analyzed
    );
    eprintln!(
        "Functions found:     {}",
        summary.functions_found
    );
    eprintln!(
        "  Public:            {}",
        summary.public_functions
    );
    eprintln!(
        "  Unsafe:            {}",
        summary.unsafe_functions
    );
    eprintln!(
        "  With specs:        {}",
        summary.specified_functions
    );
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
            eprintln!(
                "  [{icon}] [{kind_str}] {}",
                vc.description
            );
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

fn render_standalone_json(
    summary: &source_analysis::SourceAnalysisSummary,
    duration_ms: u64,
) {
    #[derive(Serialize)]
    struct JsonReport<'a> {
        mode: &'static str,
        duration_ms: u64,
        #[serde(flatten)]
        summary: &'a source_analysis::SourceAnalysisSummary,
    }
    let report = JsonReport {
        mode: "standalone",
        duration_ms,
        summary,
    };
    match serde_json::to_string_pretty(&report) {
        Ok(json) => println!("{json}"),
        Err(e) => eprintln!("cargo-trust: failed to serialize report: {e}"),
    }
}
