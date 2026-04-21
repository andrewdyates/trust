// cargo-trust: Cargo subcommand for tRust verification
//
// Usage:
//   cargo trust check            -- verify the current crate (check only, no codegen)
//   cargo trust check path.rs    -- verify a single file
//   cargo trust build            -- verify and build (check + codegen)
//   cargo trust check --format json
//
// cargo-trust invokes the stage1 rustc with -Z trust-verify, captures the
// verification diagnostics from stderr, parses PROVED/FAILED results, and
// produces a summary report.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::env;
use std::path::PathBuf;
use std::process::ExitCode;

mod cli;
mod config;
mod diff;
mod diff_git;
mod diff_report;
mod init;
mod pipeline;
mod report;
mod rewrite_loop;
mod solver_detect;
mod source_analysis;
mod types;

#[cfg(test)]
mod tests;

use cli::{SubcommandArgs, parse_subcommand_args, print_usage};
use config::TrustConfig;
use pipeline::{
    build_native_command, find_native_rustc, run_compiler, run_rewrite_loop,
    run_standalone_check,
};
use types::{OutputFormat, Subcommand};

fn main() -> ExitCode {
    let args: Vec<String> = env::args().collect();

    // cargo invokes us as: cargo-trust trust <subcommand> [args...]
    let start = if args.get(1).is_some_and(|a| a == "trust") {
        2
    } else {
        1
    };

    let subcommand = args.get(start).map(|s| s.as_str());

    match subcommand {
        Some("check") => run_subcommand(Subcommand::Check, &args[start + 1..]),
        Some("build") => run_subcommand(Subcommand::Build, &args[start + 1..]),
        Some("report") => run_subcommand(Subcommand::Report, &args[start + 1..]),
        Some("loop") => run_subcommand(Subcommand::Loop, &args[start + 1..]),
        Some("diff") => run_subcommand(Subcommand::Diff, &args[start + 1..]),
        Some("init") => run_init_subcommand(&args[start + 1..]),
        Some("solvers") | Some("doctor") => run_subcommand(Subcommand::Solvers, &args[start + 1..]),
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
        return diff_report::run_diff(&sub_args);
    }

    // Handle `solvers` subcommand -- detect and report solver status.
    if subcommand == Subcommand::Solvers {
        return run_solvers(&sub_args);
    }

    // Discover trust.toml from crate root (current directory).
    let crate_root = env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    let config = TrustConfig::load(&crate_root);
    // tRust #580: Load incremental verification cache.
    let cache_path = crate_root.join("target/trust-cache/verification.json");
    let mut cache = if sub_args.fresh {
        eprintln!("cargo-trust: --fresh: bypassing verification cache");
        trust_cache::VerificationCache::in_memory()
    } else {
        match trust_cache::VerificationCache::load(&cache_path) {
            Ok(c) => {
                if !c.is_empty() {
                    eprintln!(
                        "cargo-trust: loaded {} cached verification results",
                        c.len()
                    );
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
            eprintln!(
                "cargo-trust: warning: solver `{solver_name}` not found on PATH"
            );
            eprintln!(
                "  Run `cargo trust solvers` to check solver status"
            );
        } else if let Some(ref path) = info.path {
            eprintln!(
                "cargo-trust: using solver `{solver_name}` at {}",
                path.display()
            );
        }
        // Set env var for downstream trust-router to pick up.
        env::set_var("TRUST_SOLVER", solver_name);
    }

    // Standalone mode: source-level analysis without invoking rustc.
    let use_standalone = sub_args.standalone || find_native_rustc().is_none();

    if use_standalone && (subcommand == Subcommand::Check || subcommand == Subcommand::Report) {
        if !sub_args.standalone {
            eprintln!(
                "cargo-trust: stage1 rustc not found, falling back to standalone source analysis"
            );
        }
        return run_standalone_check(&sub_args, &crate_root);
    }

    if let Some(rustc) = find_native_rustc() {
        eprintln!(
            "cargo-trust: using native compiler at {}",
            rustc.display()
        );

        // `loop` subcommand always runs the rewrite loop.
        if subcommand == Subcommand::Loop || sub_args.rewrite {
            return run_rewrite_loop(
                &rustc,
                if subcommand == Subcommand::Loop { Subcommand::Check } else { subcommand },
                &sub_args,
                &config,
            );
        }

        // `report` runs check + renders in the requested format.
        let compile_cmd = match subcommand {
            Subcommand::Report => Subcommand::Check,
            other => other,
        };

        let exit_code = run_compiler(
            &build_native_command(&rustc, compile_cmd, &sub_args, &config),
            &rustc,
            &config,
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

    eprintln!("cargo-trust: error: stage1 rustc not found");
    eprintln!();
    eprintln!("Build the tRust compiler first:");
    eprintln!("  python3 x.py build compiler library");
    eprintln!();
    eprintln!("Or set TRUST_RUSTC=/path/to/stage1/rustc");
    eprintln!("Or use --standalone for source-level analysis without the compiler.");
    ExitCode::from(2)
}

// ---------------------------------------------------------------------------
// Solver detection subcommand
// ---------------------------------------------------------------------------

/// Run the `solvers` subcommand: detect all known dMATH solver binaries and
/// report their status. Also aliased as `cargo trust doctor`.
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
    if any_available {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
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

    let crate_root = env::current_dir().unwrap_or_else(|_| PathBuf::from("."));

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
            "cargo-trust: scanning {} for annotation scaffolding",
            file.display()
        );
        init::scaffold_file(&file)
    } else {
        eprintln!(
            "cargo-trust: scanning crate at {} for annotation scaffolding",
            crate_root.display()
        );
        init::scaffold_crate(&crate_root)
    };

    // Write .trust.toml if it doesn't exist
    let toml_path = crate_root.join("trust.toml");
    if !toml_path.exists() {
        let toml_content = init::generate_trust_toml();
        match std::fs::write(&toml_path, &toml_content) {
            Ok(()) => {
                eprintln!("cargo-trust: created {}", toml_path.display());
            }
            Err(e) => {
                eprintln!(
                    "cargo-trust: warning: failed to write {}: {e}",
                    toml_path.display()
                );
            }
        }
    } else {
        eprintln!(
            "cargo-trust: {} already exists, skipping",
            toml_path.display()
        );
    }

    // Output annotations
    if sub_args.inline {
        if summary.annotations.is_empty() {
            eprintln!("cargo-trust: no annotations to write");
        } else {
            match init::write_inline_annotations(&summary.annotations) {
                Ok(count) => {
                    eprintln!(
                        "cargo-trust: wrote annotations for {count} functions inline"
                    );
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
