// cargo-trust CLI: argument parsing and usage output
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use anyhow::{Context, Result};

use crate::diff_git;
use crate::solver_detect;
use crate::types::OutputFormat;

pub(crate) struct SubcommandArgs {
    pub(crate) format: OutputFormat,
    pub(crate) passthrough: Vec<String>,
    pub(crate) is_single_file: bool,
    /// When true, bypass the incremental verification cache (--fresh).
    pub(crate) fresh: bool,
    /// When true, run the prove-strengthen-backprop loop instead of one-shot.
    pub(crate) rewrite: bool,
    /// Maximum number of rewrite loop iterations (default: 10).
    pub(crate) max_iterations: usize,
    /// Path to a baseline report JSON file for `diff` subcommand.
    pub(crate) baseline: Option<String>,
    /// Git ref for the "from" side of a diff (e.g., `main`, `HEAD~3`).
    pub(crate) from_ref: Option<String>,
    /// Git ref for the "to" side of a diff (e.g., `feature`, `HEAD`).
    pub(crate) to_ref: Option<String>,
    /// Scope filter for git diff (e.g., `crates/`, `src/`).
    pub(crate) scope: Option<String>,
    /// Path to a current report JSON file for `diff` subcommand.
    pub(crate) current: Option<String>,
    /// When true, use standalone source-level analysis instead of invoking rustc.
    pub(crate) standalone: bool,
    /// Output directory for proof report files (JSON, HTML, NDJSON).
    pub(crate) report_dir: Option<String>,
    /// Force a specific solver backend (e.g., z4, zani, sunder).
    pub(crate) solver: Option<String>,
    /// When true, write annotations inline into source files (for `init`).
    pub(crate) inline: bool,
}

pub(crate) fn parse_subcommand_args(args: &[String]) -> Result<SubcommandArgs> {
    let mut format = OutputFormat::Terminal;
    let mut passthrough = Vec::new();
    let mut fresh = false;
    let mut rewrite = false;
    let mut max_iterations: usize = 10;
    let mut baseline: Option<String> = None;
    let mut from_ref: Option<String> = None;
    let mut to_ref: Option<String> = None;
    let mut scope: Option<String> = None;
    let mut current: Option<String> = None;
    let mut standalone = false;
    let mut report_dir: Option<String> = None;
    let mut solver: Option<String> = None;
    let mut inline = false;
    let mut i = 0;

    while i < args.len() {
        match args[i].as_str() {
            "--format" => {
                i += 1;
                let value = args
                    .get(i)
                    .context("--format requires a value (terminal, json, html)")?;
                format = OutputFormat::from_str(value)?;
            }
            s if s.starts_with("--format=") => {
                let value = s.strip_prefix("--format=").expect("invariant: prefix checked");
                format = OutputFormat::from_str(value)?;
            }
            "--rewrite" => {
                rewrite = true;
            }
            "--fresh" => {
                fresh = true;
            }
            "--standalone" => {
                standalone = true;
            }
            "--inline" => {
                inline = true;
            }
            "--max-iterations" => {
                i += 1;
                let value = args
                    .get(i)
                    .context("--max-iterations requires a numeric value")?;
                max_iterations = value.parse::<usize>()
                    .context("--max-iterations must be a positive integer")?;
                if max_iterations == 0 {
                    anyhow::bail!("--max-iterations must be at least 1");
                }
            }
            s if s.starts_with("--max-iterations=") => {
                let value = s.strip_prefix("--max-iterations=")
                    .expect("invariant: prefix checked");
                max_iterations = value.parse::<usize>()
                    .context("--max-iterations must be a positive integer")?;
                if max_iterations == 0 {
                    anyhow::bail!("--max-iterations must be at least 1");
                }
            }
            "--baseline" => {
                i += 1;
                let value = args
                    .get(i)
                    .context("--baseline requires a file path")?;
                baseline = Some(value.clone());
            }
            s if s.starts_with("--baseline=") => {
                let value = s.strip_prefix("--baseline=")
                    .expect("invariant: prefix checked");
                baseline = Some(value.to_string());
            }
            "--current" => {
                i += 1;
                let value = args
                    .get(i)
                    .context("--current requires a file path")?;
                current = Some(value.clone());
            }
            s if s.starts_with("--current=") => {
                let value = s.strip_prefix("--current=")
                    .expect("invariant: prefix checked");
                current = Some(value.to_string());
            }
            "--report-dir" => {
                i += 1;
                let value = args
                    .get(i)
                    .context("--report-dir requires a directory path")?;
                report_dir = Some(value.clone());
            }
            s if s.starts_with("--report-dir=") => {
                let value = s.strip_prefix("--report-dir=")
                    .expect("invariant: prefix checked");
                report_dir = Some(value.to_string());
            }
            "--solver" => {
                i += 1;
                let value = args
                    .get(i)
                    .context("--solver requires a solver name (z4, zani, sunder, certus, tla2, lean5)")?;
                if !solver_detect::is_known_solver(value) {
                    let known = solver_detect::known_solver_names().join(", ");
                    anyhow::bail!(
                        "unknown solver `{value}`: known solvers are {known}"
                    );
                }
                solver = Some(value.clone());
            }
            s if s.starts_with("--solver=") => {
                let value = s.strip_prefix("--solver=")
                    .expect("invariant: prefix checked");
                if !solver_detect::is_known_solver(value) {
                    let known = solver_detect::known_solver_names().join(", ");
                    anyhow::bail!(
                        "unknown solver `{value}`: known solvers are {known}"
                    );
                }
                solver = Some(value.to_string());
            }
            "--from" => {
                i += 1;
                let value = args
                    .get(i)
                    .context("--from requires a git ref")?;
                from_ref = Some(value.clone());
            }
            s if s.starts_with("--from=") => {
                let value = s.strip_prefix("--from=")
                    .expect("invariant: prefix checked");
                from_ref = Some(value.to_string());
            }
            "--to" => {
                i += 1;
                let value = args
                    .get(i)
                    .context("--to requires a git ref")?;
                to_ref = Some(value.clone());
            }
            s if s.starts_with("--to=") => {
                let value = s.strip_prefix("--to=")
                    .expect("invariant: prefix checked");
                to_ref = Some(value.to_string());
            }
            "--scope" => {
                i += 1;
                let value = args
                    .get(i)
                    .context("--scope requires a path prefix")?;
                scope = Some(value.clone());
            }
            s if s.starts_with("--scope=") => {
                let value = s.strip_prefix("--scope=")
                    .expect("invariant: prefix checked");
                scope = Some(value.to_string());
            }
            _ => passthrough.push(args[i].clone()),
        }
        i += 1;
    }

    // tRust #625: Check for ref-range syntax (e.g., "main..feature") in passthrough.
    // If found, extract as from_ref/to_ref and remove from passthrough.
    if from_ref.is_none() && to_ref.is_none() {
        let mut ref_range_idx = None;
        for (idx, arg) in passthrough.iter().enumerate() {
            if diff_git::parse_ref_range(arg).is_some() {
                ref_range_idx = Some(idx);
                break;
            }
        }
        if let Some(idx) = ref_range_idx {
            let arg = passthrough.remove(idx);
            if let Some(range) = diff_git::parse_ref_range(&arg) {
                from_ref = Some(range.from);
                to_ref = Some(range.to);
            }
        }
    }

    let is_single_file = passthrough
        .first()
        .is_some_and(|a| a.ends_with(".rs") && !a.starts_with('-'));

    Ok(SubcommandArgs {
        format,
        passthrough,
        is_single_file,
        fresh,
        rewrite,
        max_iterations,
        baseline,
        from_ref,
        to_ref,
        scope,
        current,
        standalone,
        report_dir,
        solver,
        inline,
    })
}

pub(crate) fn print_usage() {
    eprintln!("cargo-trust: tRust verification driver");
    eprintln!();
    eprintln!("Subcommands:");
    eprintln!(
        "  cargo trust check [file]       Verify the current crate or a single file"
    );
    eprintln!(
        "  cargo trust build [file]       Verify and build the crate or a single file"
    );
    eprintln!(
        "  cargo trust report [file]      Generate a verification report"
    );
    eprintln!(
        "  cargo trust loop [file]        Run the prove-strengthen-backprop loop"
    );
    eprintln!(
        "  cargo trust diff <ref>..<ref>   Compare verification between git refs"
    );
    eprintln!(
        "  cargo trust diff [file]        Compare verification state against a baseline"
    );
    eprintln!(
        "  cargo trust init [file]        Scaffold #[requires]/#[ensures] annotations"
    );
    eprintln!(
        "  cargo trust solvers            Detect and report dMATH solver status"
    );
    eprintln!(
        "  cargo trust doctor             Alias for `solvers`"
    );
    eprintln!("  cargo trust help               Show this help");
    eprintln!();
    eprintln!("Options:");
    eprintln!(
        "  --format <fmt>            Output format: terminal (default), json, html"
    );
    eprintln!(
        "  --standalone              Use source-level analysis (no compiler needed)"
    );
    eprintln!(
        "  --fresh                   Bypass verification cache (re-verify everything)"
    );
    eprintln!(
        "  --rewrite                 Enable rewrite loop mode on check/build"
    );
    eprintln!(
        "  --max-iterations <N>      Maximum loop iterations (default: 10)"
    );
    eprintln!(
        "  --from <ref>              Git ref for the 'from' side of diff"
    );
    eprintln!(
        "  --to <ref>                Git ref for the 'to' side of diff (default: HEAD)"
    );
    eprintln!(
        "  --scope <path>            Scope git diff to a path prefix (e.g., crates/)"
    );
    eprintln!(
        "  --baseline <path>         Baseline report JSON for diff subcommand"
    );
    eprintln!(
        "  --current <path>          Current report JSON for diff (compare two reports)"
    );
    eprintln!(
        "  --report-dir <dir>        Write proof report files (JSON, HTML, NDJSON) to dir"
    );
    eprintln!(
        "  --inline                  Write annotations directly into source files (init)"
    );
    eprintln!(
        "  --solver <name>           Force a specific solver (z4, zani, sunder, certus, tla2, lean5)"
    );
    eprintln!();
    eprintln!("Examples:");
    eprintln!(
        "  cargo trust check                     Verify the current crate"
    );
    eprintln!(
        "  cargo trust check path.rs             Verify a single file"
    );
    eprintln!(
        "  cargo trust check --standalone        Source-level analysis (no rustc)"
    );
    eprintln!(
        "  cargo trust report --format json       JSON verification report"
    );
    eprintln!(
        "  cargo trust report --format html       HTML verification report"
    );
    eprintln!(
        "  cargo trust loop file.rs --max-iterations 5"
    );
    eprintln!(
        "  cargo trust diff main..feature         Git ref verification diff"
    );
    eprintln!(
        "  cargo trust diff --from HEAD~5 --to HEAD  Diff last 5 commits"
    );
    eprintln!(
        "  cargo trust diff main..HEAD --scope crates/  Scope to crates/"
    );
    eprintln!(
        "  cargo trust diff main..HEAD --format json   JSON diff output"
    );
    eprintln!(
        "  cargo trust diff --baseline base.json --current cur.json"
    );
    eprintln!(
        "  cargo trust diff --baseline report.json   # baseline vs empty (CI gate)"
    );
    eprintln!(
        "  cargo trust init                      Scaffold annotations for crate"
    );
    eprintln!(
        "  cargo trust init --inline             Write annotations into source files"
    );
    eprintln!(
        "  cargo trust init src/lib.rs           Scaffold annotations for one file"
    );
    eprintln!(
        "  cargo trust solvers                   Show solver status"
    );
    eprintln!(
        "  cargo trust solvers --format json     Solver status as JSON"
    );
    eprintln!(
        "  cargo trust check --solver z4         Force z4 solver"
    );
    eprintln!();
    eprintln!("Configuration:");
    eprintln!(
        "  Place a trust.toml in your crate root to control verification."
    );
    eprintln!("  See trust-config crate docs for available options.");
    eprintln!();
    eprintln!("Behavior:");
    eprintln!(
        "  Invokes the stage1 rustc with -Z trust-verify."
    );
    eprintln!(
        "  Falls back to --standalone source analysis if rustc is not found."
    );
    eprintln!(
        "  Set TRUST_RUSTC=/path/to/rustc to override stage1 rustc discovery."
    );
    eprintln!();
    eprintln!("Exit codes:");
    eprintln!("  0  All obligations proved, no compiler errors");
    eprintln!("  1  Verification failures or compiler errors");
    eprintln!("  2  Internal error (e.g., rustc not found, missing --baseline)");
}
