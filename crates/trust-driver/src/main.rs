// trustc: The tRust compiler driver (DEPRECATED)
//
// DEPRECATED: This standalone wrapper is superseded by the native trust_verify
// MIR pass in compiler/rustc_mir_transform/src/trust_verify.rs. Use the
// stage1 rustc built by `./x.py build` with TRUST_VERIFY=1 instead:
//
//   TRUST_VERIFY=1 ./build/<host>/stage1/bin/rustc --edition 2021 file.rs
//
// This binary remains temporarily because:
//   1. It contains the working z4 backend (z4_backend.rs) — the only place
//      z4 is used as a direct dependency in tRust.
//   2. The E2E golden test (tests/e2e_midpoint.sh) still uses it.
//   3. cargo-trust invokes it.
//
// These will be migrated to the native compiler path as part of issue #1
// (native compiler integration epic).
//
// Legacy usage:
//   trustc <rustc args>
//   trustc --loop <rustc args>         # iterative verification loop
//   RUSTC_WRAPPER=trustc cargo check
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;

use std::process::ExitCode;
use std::sync::OnceLock;

/// tRust #737: Thread-safe storage for the --format=<fmt> CLI override.
/// Replaces the previous `unsafe { env::set_var("TRUST_REPORT_FORMAT", fmt) }`
/// with a safe `OnceLock` that `verify_crate()` reads after loading config.
static FORMAT_OVERRIDE: OnceLock<String> = OnceLock::new();

use rustc_driver::Compilation;
use rustc_interface::interface;
use rustc_middle::ty::TyCtxt;
use trust_config::ReportFormat;
use trust_report::{build_report, format_summary};
use trust_router::Router;
// tRust #527: CachePolicy consolidated into trust-cache.
use trust_cache::result_cache::CachePolicy;
use trust_router::solver_cache::SolverCachedRouter;
// tRust #798: SunderBackend and ZaniBackend subprocess backends removed --
// Pipeline v2 (default) uses trust-sunder-lib and trust-zani-lib directly.
// CertusBackend remains as it has no pipeline-v2 replacement yet.
use trust_router::certus_backend::CertusBackend;
use trust_types::*;
use trust_vcgen::{generate_vcs, generate_vcs_with_discharge};

// tRust: loop orchestration types from the library crate
use trust_driver::{
    LoopOutcome, ProofFrontier, VerificationLoop, VerificationLoopConfig, VerifyOutput,
};
// tRust: production phase implementations for the verification loop
use trust_driver::phases::{
    ProductionBackpropPhase, ProductionStrengthenPhase, ProductionVerifyPhase,
};
use trust_backprop::GovernancePolicy;
use trust_strengthen::StrengthenConfig;

// tRust: Z4 backend lives in trust-driver (not trust-router) because z4's
// transitive dependencies (stacker, cc) conflict with compiler-pinned versions.
// trust-router provides the VerificationBackend trait; this module implements it.
// NOTE: z4_backend is production code that will migrate to trust-z4 crate.
mod z4_backend;

// ---------------------------------------------------------------------------
// Single-pass callbacks (existing behavior, default)
// ---------------------------------------------------------------------------

/// TrustCallbacks: runs verification after rustc analysis completes.
///
/// DEPRECATED: Use the native trust_verify MIR pass instead.
/// This wrapper remains for backward compatibility with the E2E test suite.
struct TrustCallbacks;

impl rustc_driver::Callbacks for TrustCallbacks {
    fn after_analysis<'tcx>(
        &mut self,
        _compiler: &interface::Compiler,
        tcx: TyCtxt<'tcx>,
    ) -> Compilation {
        // Run verification on all functions in the crate
        verify_crate(tcx);
        // Continue compilation — verification is additive, never blocks codegen
        Compilation::Continue
    }
}

// ---------------------------------------------------------------------------
// Iterative loop callbacks (--loop flag)
// ---------------------------------------------------------------------------

/// TrustLoopCallbacks: runs the iterative verification loop after analysis.
///
/// Uses VerificationLoop to orchestrate: verify -> strengthen -> backprop -> repeat
/// until convergence, refutation, timeout, or divergence.
struct TrustLoopCallbacks;

impl rustc_driver::Callbacks for TrustLoopCallbacks {
    fn after_analysis<'tcx>(
        &mut self,
        _compiler: &interface::Compiler,
        tcx: TyCtxt<'tcx>,
    ) -> Compilation {
        verify_crate_loop(tcx);
        Compilation::Continue
    }
}

// ---------------------------------------------------------------------------
// Router construction with all available solver backends
// ---------------------------------------------------------------------------

/// Create a Router with z4 (primary) and all available dMATH solver backends.
///
/// tRust #798: SunderBackend and ZaniBackend subprocess backends removed --
/// Pipeline v2 uses trust-sunder-lib and trust-zani-lib directly via MirRouter.
/// CertusBackend (ownership) and z4_backend remain.
fn create_router() -> Router {
    Router::with_backends(vec![
        Box::new(z4_backend::Z4Backend::new()),
        Box::new(CertusBackend::new()),
    ])
}

/// tRust #520: Create a SolverCachedRouter wrapping the production router.
///
/// Before dispatching a VC to a solver backend, checks the result cache for
/// a previous result with the same formula hash and solver name. Cache key
/// is (formula_hash, solver_identity). Stores results after dispatch.
fn create_cached_router() -> SolverCachedRouter {
    SolverCachedRouter::new(create_router(), CachePolicy::AlwaysCache)
}

// ---------------------------------------------------------------------------
// TyCtxt-based direct verification (used for initial pass in --loop mode)
// ---------------------------------------------------------------------------

/// Verify all functions in the crate using the in-process TyCtxt and z4 backend.
///
/// This runs MIR extraction + VC generation + solver dispatch using the
/// already-running compiler session. Used for the initial diagnostic report
/// in `--loop` mode before handing off to the production phase loop.
///
/// tRust #520: Uses SolverCachedRouter so repeated VCs with the same formula
/// and solver identity are served from cache instead of re-dispatched.
fn verify_with_tcx<'tcx>(tcx: TyCtxt<'tcx>) -> VerifyOutput {
    let router = create_cached_router();
    let mut vcs_dispatched: usize = 0;
    let mut vcs_failed: usize = 0;
    let mut vcs_proved: usize = 0;

    for &local_def_id in tcx.mir_keys(()) {
        let def_id = local_def_id.to_def_id();
        if !tcx.is_mir_available(def_id) {
            continue;
        }

        let body = tcx.optimized_mir(def_id);
        let func = trust_mir_extract::extract_function(tcx, body);
        // tRust #357, #428: Use abstract interp pre-pass to discharge easy VCs.
        let (solver_vcs, discharged) = generate_vcs_with_discharge(&func);
        if solver_vcs.is_empty() && discharged.is_empty() {
            continue;
        }

        // Count discharged VCs as proved.
        for (_vc, _result) in &discharged {
            vcs_dispatched += 1;
            vcs_proved += 1;
        }

        // Dispatch remaining VCs to solver backends.
        let results = router.verify_all(&solver_vcs);
        for (_vc, result) in &results {
            vcs_dispatched += 1;
            match result {
                VerificationResult::Proved { .. } => vcs_proved += 1,
                _ => vcs_failed += 1,
            }
        }
    }

    VerifyOutput {
        frontier: ProofFrontier {
            trusted: vcs_proved as u32,
            certified: 0,
            runtime_checked: 0,
            failed: vcs_failed as u32,
            unknown: 0,
        },
        fingerprint: None,
        vcs_dispatched,
        vcs_failed,
    }
}

/// Determine the stage1 compiler directory for the production verify phase.
///
/// Checks `TRUST_STAGE1_DIR` env var, then falls back to `build/host/stage1`.
fn find_stage1_dir() -> std::path::PathBuf {
    if let Ok(dir) = std::env::var("TRUST_STAGE1_DIR") {
        return std::path::PathBuf::from(dir);
    }
    std::path::PathBuf::from("build/host/stage1")
}

// ---------------------------------------------------------------------------
// Core verification logic
// ---------------------------------------------------------------------------

/// Verify all functions in the crate (single-pass, existing behavior).
///
/// tRust #520: Uses SolverCachedRouter so repeated VCs with the same formula
/// and solver identity are served from cache instead of re-dispatched.
fn verify_crate<'tcx>(tcx: TyCtxt<'tcx>) {
    let mut all_results: Vec<(VerificationCondition, VerificationResult)> = Vec::new();
    let mut functions_checked = 0;

    // tRust #520: Create cached router for VC-level solver result caching.
    let router = create_cached_router();

    // Iterate over all functions with MIR
    for &local_def_id in tcx.mir_keys(()) {
        let def_id = local_def_id.to_def_id();

        // Skip non-function items (statics, constants, etc.)
        if !tcx.is_mir_available(def_id) {
            continue;
        }

        let body = tcx.optimized_mir(def_id);

        // Extract verification model from MIR
        let func = trust_mir_extract::extract_function(tcx, body);

        // tRust #357, #428: Generate VCs with abstract interp discharge pre-pass.
        let (solver_vcs, discharged) = generate_vcs_with_discharge(&func);

        if solver_vcs.is_empty() && discharged.is_empty() {
            continue;
        }

        functions_checked += 1;

        // Include discharged VCs in results (already proved by abstract interp).
        all_results.extend(discharged);

        // Route remaining VCs to solver backends.
        let results = router.verify_all(&solver_vcs);

        all_results.extend(results);
    }

    if functions_checked == 0 {
        return;
    }

    // Build and display the report
    let crate_name = tcx.crate_name(rustc_span::def_id::LOCAL_CRATE).to_string();
    let output_dir = std::path::PathBuf::from("target/trust");

    // tRust #622, #737: Resolve report format from config/env/CLI.
    // CLI --format flag (stored in FORMAT_OVERRIDE) takes precedence over
    // config file and TRUST_REPORT_FORMAT env var.
    let mut config = trust_config::TrustConfig::load(std::path::Path::new("."));
    if let Some(cli_fmt) = FORMAT_OVERRIDE.get() {
        config.report_format = Some(cli_fmt.clone());
    }
    let format = config.resolved_report_format();

    // Legacy report (text + JSON)
    let report = build_report(&crate_name, &all_results);

    if format.includes_text() {
        let summary = format_summary(&report);
        eprintln!();
        eprintln!("=== tRust Verification Report ===");
        eprintln!("{summary}");
        eprintln!();
    }

    if format.includes_json() {
        if let Err(e) = trust_report::write_report(&report, &output_dir) {
            eprintln!("warning: could not write JSON proof report: {e}");
        }
    }

    // tRust #622: Generate self-contained HTML report with per-function badges.
    if format.includes_html() {
        if let Err(e) =
            trust_report::html::write_html_report(&crate_name, &all_results, &output_dir)
        {
            eprintln!("warning: could not write HTML proof report: {e}");
        } else {
            eprintln!(
                "HTML proof report: {}/report.html",
                output_dir.display()
            );
        }
    }
}

/// Verify all functions using the iterative verification loop (--loop mode).
///
/// Runs an initial TyCtxt-based verify pass for diagnostics, then orchestrates
/// the full production loop: verify -> strengthen -> backprop -> repeat.
fn verify_crate_loop<'tcx>(tcx: TyCtxt<'tcx>) {
    // Run initial verification using TyCtxt directly (since we have it)
    let initial_output = verify_with_tcx(tcx);

    let crate_name = tcx.crate_name(rustc_span::def_id::LOCAL_CRATE).to_string();

    eprintln!();
    eprintln!("=== tRust Iterative Verification Loop ===");
    eprintln!("crate: {crate_name}");

    if initial_output.vcs_dispatched == 0 {
        eprintln!("No verification conditions found.");
        eprintln!();
        return;
    }

    // Report initial pass results
    eprintln!("Initial pass — VCs dispatched: {}", initial_output.vcs_dispatched);
    eprintln!(
        "Initial pass — VCs proved: {} | failed: {}",
        initial_output.frontier.trusted, initial_output.frontier.failed,
    );

    // tRust: Build the VerificationLoop with production phase implementations.
    // - ProductionVerifyPhase: invokes stage1 compiler externally
    // - ProductionStrengthenPhase: heuristic-only spec inference (no LLM yet)
    // - ProductionBackpropPhase: governance-checked source rewrites
    let stage1_dir = find_stage1_dir();
    let prod_verify = ProductionVerifyPhase::new(stage1_dir);
    let prod_strengthen = ProductionStrengthenPhase::heuristic_only(StrengthenConfig::default());
    let prod_backprop = ProductionBackpropPhase::new(GovernancePolicy::default());

    let config = VerificationLoopConfig::default();
    let mut vloop = VerificationLoop::new(
        config,
        &prod_verify,
        &prod_strengthen,
        &prod_backprop,
    );

    // Run the production loop. The source_path is used by production phases
    // to invoke the external compiler and apply rewrites.
    let source_path = std::path::PathBuf::from(".");
    let (outcome, history) = vloop.run(&source_path);

    eprintln!("Loop iterations: {}", history.len());
    eprintln!("Loop outcome: {outcome:?}");

    // Determine the effective outcome: use the initial TyCtxt pass as ground
    // truth (it ran in-process with z4), combined with the loop's convergence.
    let effective_outcome = if initial_output.vcs_failed == 0 {
        "VERIFIED"
    } else {
        match &outcome {
            LoopOutcome::Verified { .. } => "VERIFIED (loop converged)",
            LoopOutcome::Refuted { .. } => "REFUTED (failures remain)",
            LoopOutcome::Timeout { .. } => "TIMEOUT (loop did not converge)",
            LoopOutcome::Diverged { .. } => "DIVERGED (proof frontier oscillating)",
        }
    };
    eprintln!("Effective result: {effective_outcome}");
    eprintln!();
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

fn main() -> ExitCode {
    // Collect args, inserting --sysroot if not already present
    let mut args: Vec<String> = std::env::args().collect();

    // If invoked via RUSTC_WRAPPER, the first arg after the binary name
    // is the path to rustc itself. We consume it.
    // RUSTC_WRAPPER protocol: trustc rustc <args>
    if args.len() > 1 && args[1].ends_with("rustc") {
        args.remove(1);
    }

    // tRust: Extract --loop flag before passing args to rustc.
    // --loop enables the iterative verification loop instead of single-pass.
    let use_loop = args.iter().any(|a| a == "--loop");
    args.retain(|a| a != "--loop");

    // tRust #622, #737: Extract --format=<fmt> flag for verify_crate.
    // Stored in FORMAT_OVERRIDE (OnceLock) instead of env var to avoid unsafe.
    if let Some(pos) = args.iter().position(|a| a.starts_with("--format=")) {
        let arg = args.remove(pos);
        if let Some(fmt) = arg.strip_prefix("--format=") {
            if ReportFormat::from_name(fmt).is_some() {
                let _ = FORMAT_OVERRIDE.set(fmt.to_string());
            } else {
                eprintln!("warning: unknown --format='{}'; expected text/json/html/all", fmt);
            }
        }
    }

    // Ensure --sysroot is set so rustc can find std
    if !args.iter().any(|a| a.starts_with("--sysroot")) {
        if let Some(sysroot) = find_sysroot() {
            args.push("--sysroot".to_string());
            args.push(sysroot);
        }
    }

    if use_loop {
        let mut callbacks = TrustLoopCallbacks;
        rustc_driver::catch_with_exit_code(|| rustc_driver::run_compiler(&args, &mut callbacks))
    } else {
        let mut callbacks = TrustCallbacks;
        rustc_driver::catch_with_exit_code(|| rustc_driver::run_compiler(&args, &mut callbacks))
    }
}

/// Find the sysroot for the current toolchain.
fn find_sysroot() -> Option<String> {
    // Try SYSROOT env var first
    if let Ok(sysroot) = std::env::var("SYSROOT") {
        return Some(sysroot);
    }

    // Try nightly sysroot first (trust-driver requires nightly rustc_private)
    let output = std::process::Command::new("rustup")
        .args(["run", "nightly", "rustc", "--print", "sysroot"])
        .output()
        .ok()?;

    if output.status.success() {
        Some(String::from_utf8(output.stdout).ok()?.trim().to_string())
    } else {
        None
    }
}
