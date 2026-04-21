// cargo-trust diff report: comparison of verification state between baselines
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::env;
use std::path::PathBuf;
use std::process::ExitCode;

use crate::cli::SubcommandArgs;
use crate::diff_git;
use crate::types::OutputFormat;

/// Run the `diff` subcommand: compare verification state between git refs,
/// or against a baseline JSON report.
///
/// tRust #625: Enhanced diff with function-level comparison, color-coded
/// terminal output, and CI gate (exit non-zero on regressions).
///
/// Usage:
///   cargo trust diff main..feature                            # git ref comparison
///   cargo trust diff --baseline report.json                   # baseline vs empty
///   cargo trust diff --baseline base.json --current cur.json  # compare two reports
pub(crate) fn run_diff(sub_args: &SubcommandArgs) -> ExitCode {
    // tRust #625: Git-aware diff mode when --from/--to or ref..ref is provided.
    if let Some(ref from) = sub_args.from_ref {
        let to = sub_args
            .to_ref
            .clone()
            .unwrap_or_else(|| "HEAD".to_string());
        let repo_dir = env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
        let range = diff_git::GitRefRange {
            from: from.clone(),
            to,
        };

        match diff_git::run_git_diff(&range, &repo_dir, sub_args.scope.as_deref()) {
            Ok(report) => {
                match sub_args.format {
                    OutputFormat::Json => report.render_json(),
                    OutputFormat::Terminal | OutputFormat::Html => report.render_terminal(),
                }
                if report.has_regressions() {
                    return ExitCode::FAILURE;
                }
                return ExitCode::SUCCESS;
            }
            Err(e) => {
                eprintln!("cargo-trust: git diff failed: {e}");
                return ExitCode::from(2);
            }
        }
    }

    // Legacy baseline-file mode.
    let baseline_path = match &sub_args.baseline {
        Some(p) => p.clone(),
        None => {
            eprintln!("cargo-trust: diff requires --from <ref> or --baseline <path>");
            eprintln!("Usage:");
            eprintln!("  cargo trust diff main..feature             Git ref comparison");
            eprintln!("  cargo trust diff --from main --to HEAD     Explicit git refs");
            eprintln!("  cargo trust diff --baseline <path>         Baseline JSON file");
            eprintln!("  cargo trust diff --baseline <path> --current <path>  Compare two reports");
            return ExitCode::from(2);
        }
    };

    let current_path = sub_args.current.as_deref();
    crate::diff::run_diff_command(&baseline_path, current_path, sub_args.format)
}
