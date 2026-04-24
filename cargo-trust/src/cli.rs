// cargo-trust CLI: argument parsing and usage output
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use anyhow::{Context, Result};

use crate::config::{known_codegen_backend_names, normalize_codegen_backend};
use crate::diff_git;
use crate::solver_detect;
use crate::types::OutputFormat;

pub(crate) struct SubcommandArgs {
    pub(crate) format: OutputFormat,
    pub(crate) passthrough: Vec<String>,
    pub(crate) manifest_path: Option<String>,
    pub(crate) single_file: Option<String>,
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
    /// When true, use standalone source-level analysis instead of invoking trustc.
    pub(crate) standalone: bool,
    /// Output directory for proof report files (JSON, HTML, NDJSON).
    pub(crate) report_dir: Option<String>,
    /// Force a specific solver backend (e.g., z4, zani, sunder).
    pub(crate) solver: Option<String>,
    /// Force a specific codegen backend (llvm or llvm2).
    pub(crate) backend: Option<String>,
    /// When true, write annotations inline into source files (for `init`).
    pub(crate) inline: bool,
    /// Entry address for `lift`, accepted as decimal or 0x-prefixed hex.
    pub(crate) entry: Option<String>,
    /// When true, lift all detected functions instead of the binary entry.
    pub(crate) all_functions: bool,
    /// When true, unsupported lift coverage makes `lift` fail.
    pub(crate) strict: bool,
}

impl SubcommandArgs {
    pub(crate) fn single_file_path(&self) -> Option<&str> {
        self.single_file.as_deref()
    }
}

pub(crate) fn parse_subcommand_args(args: &[String]) -> Result<SubcommandArgs> {
    let mut format = OutputFormat::Terminal;
    let mut passthrough = Vec::new();
    let mut manifest_path: Option<String> = None;
    let mut single_file: Option<String> = None;
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
    let mut backend: Option<String> = None;
    let mut inline = false;
    let mut entry: Option<String> = None;
    let mut all_functions = false;
    let mut strict = true;
    let mut i = 0;

    while i < args.len() {
        match args[i].as_str() {
            "--json" => {
                format = OutputFormat::Json;
            }
            "--format" => {
                i += 1;
                let value =
                    args.get(i).context("--format requires a value (terminal, json, html)")?;
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
            "--all" => {
                all_functions = true;
            }
            "--strict" => {
                strict = true;
            }
            "--allow-unsupported" => {
                strict = false;
            }
            "--entry" => {
                i += 1;
                let value = args.get(i).context("--entry requires an address")?;
                entry = Some(value.clone());
            }
            s if s.starts_with("--entry=") => {
                let value = s.strip_prefix("--entry=").expect("invariant: prefix checked");
                entry = Some(value.to_string());
            }
            "--max-iterations" => {
                i += 1;
                let value = args.get(i).context("--max-iterations requires a numeric value")?;
                max_iterations = value
                    .parse::<usize>()
                    .context("--max-iterations must be a positive integer")?;
                if max_iterations == 0 {
                    anyhow::bail!("--max-iterations must be at least 1");
                }
            }
            s if s.starts_with("--max-iterations=") => {
                let value = s.strip_prefix("--max-iterations=").expect("invariant: prefix checked");
                max_iterations = value
                    .parse::<usize>()
                    .context("--max-iterations must be a positive integer")?;
                if max_iterations == 0 {
                    anyhow::bail!("--max-iterations must be at least 1");
                }
            }
            "--baseline" => {
                i += 1;
                let value = args.get(i).context("--baseline requires a file path")?;
                baseline = Some(value.clone());
            }
            s if s.starts_with("--baseline=") => {
                let value = s.strip_prefix("--baseline=").expect("invariant: prefix checked");
                baseline = Some(value.to_string());
            }
            "--current" => {
                i += 1;
                let value = args.get(i).context("--current requires a file path")?;
                current = Some(value.clone());
            }
            s if s.starts_with("--current=") => {
                let value = s.strip_prefix("--current=").expect("invariant: prefix checked");
                current = Some(value.to_string());
            }
            "--report-dir" => {
                i += 1;
                let value = args.get(i).context("--report-dir requires a directory path")?;
                report_dir = Some(value.clone());
            }
            s if s.starts_with("--report-dir=") => {
                let value = s.strip_prefix("--report-dir=").expect("invariant: prefix checked");
                report_dir = Some(value.to_string());
            }
            "--solver" => {
                i += 1;
                let value = args.get(i).context(
                    "--solver requires a solver name (z4, zani, sunder, certus, tla2, lean5)",
                )?;
                if !solver_detect::is_known_solver(value) {
                    let known = solver_detect::known_solver_names().join(", ");
                    anyhow::bail!("unknown solver `{value}`: known solvers are {known}");
                }
                solver = Some(value.clone());
            }
            s if s.starts_with("--solver=") => {
                let value = s.strip_prefix("--solver=").expect("invariant: prefix checked");
                if !solver_detect::is_known_solver(value) {
                    let known = solver_detect::known_solver_names().join(", ");
                    anyhow::bail!("unknown solver `{value}`: known solvers are {known}");
                }
                solver = Some(value.to_string());
            }
            "--backend" => {
                i += 1;
                let value =
                    args.get(i).context("--backend requires a backend name (llvm, llvm2)")?;
                let backend_name = normalize_codegen_backend(value).ok_or_else(|| {
                    let known = known_codegen_backend_names().join(", ");
                    anyhow::anyhow!("unknown backend `{value}`: known backends are {known}")
                })?;
                backend = Some(backend_name.to_string());
            }
            s if s.starts_with("--backend=") => {
                let value = s.strip_prefix("--backend=").expect("invariant: prefix checked");
                let backend_name = normalize_codegen_backend(value).ok_or_else(|| {
                    let known = known_codegen_backend_names().join(", ");
                    anyhow::anyhow!("unknown backend `{value}`: known backends are {known}")
                })?;
                backend = Some(backend_name.to_string());
            }
            "--from" => {
                i += 1;
                let value = args.get(i).context("--from requires a git ref")?;
                from_ref = Some(value.clone());
            }
            s if s.starts_with("--from=") => {
                let value = s.strip_prefix("--from=").expect("invariant: prefix checked");
                from_ref = Some(value.to_string());
            }
            "--to" => {
                i += 1;
                let value = args.get(i).context("--to requires a git ref")?;
                to_ref = Some(value.clone());
            }
            s if s.starts_with("--to=") => {
                let value = s.strip_prefix("--to=").expect("invariant: prefix checked");
                to_ref = Some(value.to_string());
            }
            "--scope" => {
                i += 1;
                let value = args.get(i).context("--scope requires a path prefix")?;
                scope = Some(value.clone());
            }
            s if s.starts_with("--scope=") => {
                let value = s.strip_prefix("--scope=").expect("invariant: prefix checked");
                scope = Some(value.to_string());
            }
            "--manifest-path" => {
                i += 1;
                let value = args.get(i).context("--manifest-path requires a file path")?;
                manifest_path = Some(value.clone());
                passthrough.push("--manifest-path".to_string());
                passthrough.push(value.clone());
            }
            s if s.starts_with("--manifest-path=") => {
                let value = s.strip_prefix("--manifest-path=").expect("invariant: prefix checked");
                manifest_path = Some(value.to_string());
                passthrough.push(args[i].clone());
            }
            _ => {
                let arg = args[i].clone();
                if manifest_path.is_none()
                    && single_file.is_none()
                    && arg.ends_with(".rs")
                    && !arg.starts_with('-')
                {
                    single_file = Some(arg.clone());
                }
                passthrough.push(arg);
            }
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

    let is_single_file = single_file.is_some();

    Ok(SubcommandArgs {
        format,
        passthrough,
        manifest_path,
        single_file,
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
        backend,
        inline,
        entry,
        all_functions,
        strict,
    })
}

pub(crate) fn usage_text() -> String {
    [
        "cargo-trust: tRust verification driver",
        "",
        "Subcommands:",
        "  cargo trust check [file]       Verify the current crate or a single file",
        "  cargo trust build [file]       Verify and build the crate or a single file",
        "  cargo trust lift <binary>      Lift a binary into tMIR and summarize coverage",
        "  cargo trust report [file]      Generate a verification report",
        "  cargo trust loop [file]        Run the prove-strengthen-backprop loop",
        "  cargo trust diff <ref>..<ref>   Compare verification between git refs",
        "  cargo trust diff [file]        Compare verification state against a baseline",
        "  cargo trust init [file]        Scaffold #[requires]/#[ensures] annotations",
        "  cargo trust solvers            Detect and report dMATH solver status",
        "  cargo trust doctor             Show compiler/setup status and solver availability",
        "  cargo trust help               Show this help",
        "",
        "Options:",
        "  --format <fmt>            Output format: terminal (default), json, html",
        "  --json                    Alias for --format json",
        "  --standalone              Use source-level analysis (no compiler needed)",
        "  --fresh                   Bypass verification cache (re-verify everything)",
        "  --rewrite                 Enable rewrite loop mode on check/build",
        "  --max-iterations <N>      Maximum loop iterations (default: 10)",
        "  --from <ref>              Git ref for the 'from' side of diff",
        "  --to <ref>                Git ref for the 'to' side of diff (default: HEAD)",
        "  --scope <path>            Scope git diff to a path prefix (e.g., crates/)",
        "  --baseline <path>         Baseline report JSON for diff subcommand",
        "  --current <path>          Current report JSON for diff (compare two reports)",
        "  --report-dir <dir>        Write proof report files (JSON, HTML, NDJSON) to dir",
        "  --inline                  Write annotations directly into source files (init)",
        "  --entry <addr>            Entry address for lift (decimal or 0x-prefixed hex)",
        "  --all                     Lift all detected function symbols",
        "  --strict                  Fail lift when unsupported code is encountered (default)",
        "  --allow-unsupported       Permit partial lift coverage",
        "  --backend <name>          Codegen backend: llvm (default) or llvm2",
        "  --solver <name>           Force a specific solver (z4, zani, sunder, certus, tla2, lean5)",
        "  --manifest-path <path>    Anchor crate-mode commands to a specific Cargo.toml",
        "",
        "Examples:",
        "  cargo trust check                     Verify the current crate",
        "  cargo trust check path.rs             Verify a single file",
        "  cargo trust lift ./target/release/app  Lift binary functions into tMIR",
        "  cargo trust lift app --all --allow-unsupported",
        "  cargo trust lift app --entry 0x401000 --json",
        "  cargo trust lift app --strict          Fail on unsupported lift coverage",
        "  cargo trust check --standalone        Source-level analysis (no compiler)",
        "  cargo trust build --backend llvm2     Verify and build with the LLVM2 backend",
        "  cargo trust report --format json       JSON verification report",
        "  cargo trust report --format html       HTML verification report",
        "  cargo trust loop file.rs --max-iterations 5",
        "  cargo trust diff main..feature         Git ref verification diff",
        "  cargo trust diff --from HEAD~5 --to HEAD  Diff last 5 commits",
        "  cargo trust diff main..HEAD --scope crates/  Scope to crates/",
        "  cargo trust diff main..HEAD --format json   JSON diff output",
        "  cargo trust diff --baseline base.json --current cur.json",
        "  cargo trust diff --baseline report.json   # baseline vs empty (CI gate)",
        "  cargo trust init                      Scaffold annotations for crate",
        "  cargo trust init --inline             Write annotations into source files",
        "  cargo trust init src/lib.rs           Scaffold annotations for one file",
        "  cargo trust doctor                    Show compiler, backend, config, transport, and solver status",
        "  cargo trust doctor --format json      Machine-readable setup status",
        "  cargo trust solvers                   Show solver status",
        "  cargo trust solvers --format json     Solver status as JSON",
        "  cargo trust check --solver z4         Force z4 solver",
        "",
        "Configuration:",
        "  Place a trust.toml in your crate root to control verification.",
        "  See trust-config crate docs for available options.",
        "",
        "Behavior:",
        "  Invokes the discovered trust cargo/trustc toolchain with -Z trust-verify.",
        "  Compiler discovery priority: TRUSTC, sibling trustc next to cargo-trust, linked rustup toolchain `trust`, then repo-local builds.",
        "  Check/report fall back to --standalone source analysis if compiler discovery fails.",
        "  Set TRUSTC=/path/to/trustc to override compiler discovery; cargo-trust uses sibling cargo.",
        "",
        "Exit codes:",
        "  0  All obligations proved, no compiler errors",
        "  1  Verification failures, runtime-checked or inconclusive results, or compiler errors",
        "  2  Internal error (e.g., trustc not found, missing --baseline)",
    ]
    .join("\n")
        + "\n"
}

pub(crate) fn print_usage() {
    eprint!("{}", usage_text());
}
