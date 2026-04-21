// Git-aware verification diff: compare verification state between git refs.
//
// Uses `git show <ref>:<path>` to read file contents at each ref without
// requiring checkout. Runs lightweight source analysis on both versions
// and reports function-level verification status changes.
//
// Part of #625: cargo trust diff -- show verification delta between commits/branches
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::HashMap;
use std::path::Path;
use std::process::Command;

use serde::Serialize;

use crate::source_analysis::{
    self, ParsedFunction, SourceAnalysisSummary, StandaloneOutcome,
};

// ---------------------------------------------------------------------------
// Git ref range parsing
// ---------------------------------------------------------------------------

/// A pair of git refs to compare.
#[derive(Debug, Clone)]
pub(crate) struct GitRefRange {
    pub(crate) from: String,
    pub(crate) to: String,
}

/// Parse a ref range from CLI arguments.
///
/// Supports:
///   - `main..feature` (double-dot syntax)
///   - `--from main --to feature` (explicit flags, handled by caller)
///   - `HEAD~3` (single ref, compares to working tree)
pub(crate) fn parse_ref_range(arg: &str) -> Option<GitRefRange> {
    if let Some((from, to)) = arg.split_once("..") {
        let from = from.trim();
        let to = to.trim();
        if from.is_empty() || to.is_empty() {
            return None;
        }
        Some(GitRefRange {
            from: from.to_string(),
            to: to.to_string(),
        })
    } else {
        None
    }
}

// ---------------------------------------------------------------------------
// Git operations
// ---------------------------------------------------------------------------

/// Resolve a git ref to a full commit hash.
pub(crate) fn resolve_ref(git_ref: &str, repo_dir: &Path) -> Result<String, String> {
    let output = Command::new("git")
        .args(["rev-parse", "--verify", git_ref])
        .current_dir(repo_dir)
        .output()
        .map_err(|e| format!("failed to run git: {e}"))?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        return Err(format!("unknown git ref `{git_ref}`: {}", stderr.trim()));
    }

    Ok(String::from_utf8_lossy(&output.stdout).trim().to_string())
}

/// Get file contents at a specific git ref.
///
/// Uses `git show <ref>:<path>` to avoid checkout.
/// Returns `None` if the file doesn't exist at that ref.
fn git_show_file(git_ref: &str, file_path: &str, repo_dir: &Path) -> Option<String> {
    let spec = format!("{git_ref}:{file_path}");
    let output = Command::new("git")
        .args(["show", &spec])
        .current_dir(repo_dir)
        .output()
        .ok()?;

    if output.status.success() {
        Some(String::from_utf8_lossy(&output.stdout).to_string())
    } else {
        None
    }
}

/// List Rust source files that changed between two refs.
///
/// Returns paths relative to the repo root.
fn changed_rs_files(from_ref: &str, to_ref: &str, repo_dir: &Path) -> Vec<String> {
    let output = Command::new("git")
        .args([
            "diff",
            "--name-only",
            "--diff-filter=ACMR",
            from_ref,
            to_ref,
            "--",
            "*.rs",
        ])
        .current_dir(repo_dir)
        .output();

    match output {
        Ok(out) if out.status.success() => String::from_utf8_lossy(&out.stdout)
            .lines()
            .filter(|l| !l.is_empty())
            .map(String::from)
            .collect(),
        _ => Vec::new(),
    }
}

/// List Rust source files that were deleted between two refs.
fn deleted_rs_files(from_ref: &str, to_ref: &str, repo_dir: &Path) -> Vec<String> {
    let output = Command::new("git")
        .args([
            "diff",
            "--name-only",
            "--diff-filter=D",
            from_ref,
            to_ref,
            "--",
            "*.rs",
        ])
        .current_dir(repo_dir)
        .output();

    match output {
        Ok(out) if out.status.success() => String::from_utf8_lossy(&out.stdout)
            .lines()
            .filter(|l| !l.is_empty())
            .map(String::from)
            .collect(),
        _ => Vec::new(),
    }
}



// ---------------------------------------------------------------------------
// Function-level diff
// ---------------------------------------------------------------------------

/// A function's verification state at a single git ref.
#[derive(Debug, Clone, Serialize)]
pub(crate) struct FunctionState {
    pub(crate) name: String,
    pub(crate) file: String,
    pub(crate) is_public: bool,
    pub(crate) is_unsafe: bool,
    pub(crate) has_requires: bool,
    pub(crate) has_ensures: bool,
}

impl From<&ParsedFunction> for FunctionState {
    fn from(f: &ParsedFunction) -> Self {
        Self {
            name: f.name.clone(),
            file: f.file.to_string_lossy().to_string(),
            is_public: f.is_public,
            is_unsafe: f.is_unsafe,
            has_requires: f.has_requires,
            has_ensures: f.has_ensures,
        }
    }
}

/// How a function's verification state changed.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub(crate) enum FunctionChange {
    /// Function was added.
    Added,
    /// Function was removed.
    Removed,
    /// Function gained a spec (requires or ensures).
    GainedSpec,
    /// Function lost a spec.
    LostSpec,
    /// Function changed from safe to unsafe or vice versa.
    SafetyChanged,
    /// Function visibility changed.
    VisibilityChanged,
    /// No verification-relevant change.
    #[allow(dead_code)]
    Unchanged,
}

/// A single function-level diff entry.
#[derive(Debug, Clone, Serialize)]
pub(crate) struct FunctionDiffEntry {
    pub(crate) function: String,
    pub(crate) file: String,
    pub(crate) change: FunctionChange,
    pub(crate) detail: String,
    pub(crate) from_state: Option<FunctionState>,
    pub(crate) to_state: Option<FunctionState>,
}

/// Full git-aware diff report.
#[derive(Debug, Clone, Serialize)]
pub(crate) struct GitDiffReport {
    pub(crate) from_ref: String,
    pub(crate) to_ref: String,
    pub(crate) from_commit: String,
    pub(crate) to_commit: String,
    pub(crate) files_changed: usize,
    pub(crate) files_deleted: usize,
    pub(crate) from_summary: DiffSummaryStats,
    pub(crate) to_summary: DiffSummaryStats,
    pub(crate) functions_added: usize,
    pub(crate) functions_removed: usize,
    pub(crate) specs_gained: usize,
    pub(crate) specs_lost: usize,
    pub(crate) safety_changes: usize,
    pub(crate) entries: Vec<FunctionDiffEntry>,
}

/// Summary statistics from source analysis at a ref.
#[derive(Debug, Clone, Serialize)]
pub(crate) struct DiffSummaryStats {
    pub(crate) functions: usize,
    pub(crate) public_functions: usize,
    pub(crate) unsafe_functions: usize,
    pub(crate) specified_functions: usize,
    pub(crate) total_vcs: usize,
    pub(crate) proved: usize,
    pub(crate) unknown: usize,
}

impl From<&SourceAnalysisSummary> for DiffSummaryStats {
    fn from(s: &SourceAnalysisSummary) -> Self {
        Self {
            functions: s.functions_found,
            public_functions: s.public_functions,
            unsafe_functions: s.unsafe_functions,
            specified_functions: s.specified_functions,
            total_vcs: s.total_vcs,
            proved: s.proved,
            unknown: s.unknown,
        }
    }
}

// ---------------------------------------------------------------------------
// Core diff computation
// ---------------------------------------------------------------------------

/// Run the full git-aware diff between two refs.
///
/// Analyzes changed Rust source files at both refs and produces a
/// function-level diff of verification state.
pub(crate) fn run_git_diff(
    range: &GitRefRange,
    repo_dir: &Path,
    scope: Option<&str>,
) -> Result<GitDiffReport, String> {
    // Resolve refs to commit hashes.
    let from_commit = resolve_ref(&range.from, repo_dir)?;
    let to_commit = resolve_ref(&range.to, repo_dir)?;

    eprintln!(
        "cargo-trust: diff {} ({}) .. {} ({})",
        range.from,
        &from_commit[..8.min(from_commit.len())],
        range.to,
        &to_commit[..8.min(to_commit.len())],
    );

    // Find changed and deleted files.
    let changed = changed_rs_files(&from_commit, &to_commit, repo_dir);
    let deleted = deleted_rs_files(&from_commit, &to_commit, repo_dir);

    // Filter by scope if provided (e.g., "crates/" or "src/").
    let changed: Vec<String> = if let Some(scope_prefix) = scope {
        changed
            .into_iter()
            .filter(|f| f.starts_with(scope_prefix))
            .collect()
    } else {
        changed
    };
    let deleted: Vec<String> = if let Some(scope_prefix) = scope {
        deleted
            .into_iter()
            .filter(|f| f.starts_with(scope_prefix))
            .collect()
    } else {
        deleted
    };

    eprintln!(
        "cargo-trust: {} files changed, {} files deleted",
        changed.len(),
        deleted.len()
    );

    // Analyze functions at both refs for changed files.
    let mut from_functions: HashMap<String, ParsedFunction> = HashMap::new();
    let mut to_functions: HashMap<String, ParsedFunction> = HashMap::new();

    let mut from_all_funcs: Vec<ParsedFunction> = Vec::new();
    let mut to_all_funcs: Vec<ParsedFunction> = Vec::new();

    for file_path in &changed {
        // Get file at from-ref.
        if let Some(content) = git_show_file(&from_commit, file_path, repo_dir) {
            let funcs = source_analysis::extract_functions_from_source(
                &content,
                Path::new(file_path),
            );
            for f in &funcs {
                let key = format!("{}::{}", file_path, f.name);
                from_functions.insert(key, f.clone());
            }
            from_all_funcs.extend(funcs);
        }

        // Get file at to-ref.
        if let Some(content) = git_show_file(&to_commit, file_path, repo_dir) {
            let funcs = source_analysis::extract_functions_from_source(
                &content,
                Path::new(file_path),
            );
            for f in &funcs {
                let key = format!("{}::{}", file_path, f.name);
                to_functions.insert(key, f.clone());
            }
            to_all_funcs.extend(funcs);
        }
    }

    // Also analyze deleted files (only in from-ref).
    for file_path in &deleted {
        if let Some(content) = git_show_file(&from_commit, file_path, repo_dir) {
            let funcs = source_analysis::extract_functions_from_source(
                &content,
                Path::new(file_path),
            );
            for f in &funcs {
                let key = format!("{}::{}", file_path, f.name);
                from_functions.insert(key, f.clone());
            }
            from_all_funcs.extend(funcs);
        }
    }

    // Compute function-level diff.
    let mut entries = Vec::new();
    let mut functions_added = 0usize;
    let mut functions_removed = 0usize;
    let mut specs_gained = 0usize;
    let mut specs_lost = 0usize;
    let mut safety_changes = 0usize;

    // Check all functions in to-ref: new or changed?
    for (key, to_func) in &to_functions {
        match from_functions.get(key) {
            None => {
                // New function.
                functions_added += 1;
                let detail = if to_func.has_requires || to_func.has_ensures {
                    "new function with specifications".to_string()
                } else if to_func.is_unsafe {
                    "new unsafe function".to_string()
                } else if to_func.is_public {
                    "new public function (no specs)".to_string()
                } else {
                    "new private function".to_string()
                };
                entries.push(FunctionDiffEntry {
                    function: to_func.name.clone(),
                    file: key.split("::").next().unwrap_or("").to_string(),
                    change: FunctionChange::Added,
                    detail,
                    from_state: None,
                    to_state: Some(FunctionState::from(to_func)),
                });
            }
            Some(from_func) => {
                // Existing function -- check for changes.
                let gained_spec = (!from_func.has_requires && to_func.has_requires)
                    || (!from_func.has_ensures && to_func.has_ensures);
                let lost_spec = (from_func.has_requires && !to_func.has_requires)
                    || (from_func.has_ensures && !to_func.has_ensures);
                let safety_changed = from_func.is_unsafe != to_func.is_unsafe;
                let vis_changed = from_func.is_public != to_func.is_public;

                if gained_spec {
                    specs_gained += 1;
                    let mut parts = Vec::new();
                    if !from_func.has_requires && to_func.has_requires {
                        parts.push("#[requires] added");
                    }
                    if !from_func.has_ensures && to_func.has_ensures {
                        parts.push("#[ensures] added");
                    }
                    entries.push(FunctionDiffEntry {
                        function: to_func.name.clone(),
                        file: key.split("::").next().unwrap_or("").to_string(),
                        change: FunctionChange::GainedSpec,
                        detail: parts.join(", "),
                        from_state: Some(FunctionState::from(from_func)),
                        to_state: Some(FunctionState::from(to_func)),
                    });
                }

                if lost_spec {
                    specs_lost += 1;
                    let mut parts = Vec::new();
                    if from_func.has_requires && !to_func.has_requires {
                        parts.push("#[requires] removed");
                    }
                    if from_func.has_ensures && !to_func.has_ensures {
                        parts.push("#[ensures] removed");
                    }
                    entries.push(FunctionDiffEntry {
                        function: to_func.name.clone(),
                        file: key.split("::").next().unwrap_or("").to_string(),
                        change: FunctionChange::LostSpec,
                        detail: parts.join(", "),
                        from_state: Some(FunctionState::from(from_func)),
                        to_state: Some(FunctionState::from(to_func)),
                    });
                }

                if safety_changed {
                    safety_changes += 1;
                    let detail = if to_func.is_unsafe {
                        "became unsafe".to_string()
                    } else {
                        "became safe".to_string()
                    };
                    entries.push(FunctionDiffEntry {
                        function: to_func.name.clone(),
                        file: key.split("::").next().unwrap_or("").to_string(),
                        change: FunctionChange::SafetyChanged,
                        detail,
                        from_state: Some(FunctionState::from(from_func)),
                        to_state: Some(FunctionState::from(to_func)),
                    });
                }

                if vis_changed && !gained_spec && !lost_spec && !safety_changed {
                    let detail = if to_func.is_public {
                        "became public".to_string()
                    } else {
                        "became private".to_string()
                    };
                    entries.push(FunctionDiffEntry {
                        function: to_func.name.clone(),
                        file: key.split("::").next().unwrap_or("").to_string(),
                        change: FunctionChange::VisibilityChanged,
                        detail,
                        from_state: Some(FunctionState::from(from_func)),
                        to_state: Some(FunctionState::from(to_func)),
                    });
                }
            }
        }
    }

    // Check for removed functions.
    for (key, from_func) in &from_functions {
        if !to_functions.contains_key(key) {
            functions_removed += 1;
            let detail = if from_func.has_requires || from_func.has_ensures {
                "removed function (had specifications)".to_string()
            } else {
                "removed function".to_string()
            };
            entries.push(FunctionDiffEntry {
                function: from_func.name.clone(),
                file: key.split("::").next().unwrap_or("").to_string(),
                change: FunctionChange::Removed,
                detail,
                from_state: Some(FunctionState::from(from_func)),
                to_state: None,
            });
        }
    }

    // Sort entries: regressions first (lost specs, safety changes, removed),
    // then improvements (gained specs, added).
    entries.sort_by(|a, b| {
        fn change_priority(c: FunctionChange) -> u8 {
            match c {
                FunctionChange::LostSpec => 0,
                FunctionChange::SafetyChanged => 1,
                FunctionChange::Removed => 2,
                FunctionChange::GainedSpec => 3,
                FunctionChange::Added => 4,
                FunctionChange::VisibilityChanged => 5,
                FunctionChange::Unchanged => 6,
            }
        }
        change_priority(a.change)
            .cmp(&change_priority(b.change))
            .then_with(|| a.file.cmp(&b.file))
            .then_with(|| a.function.cmp(&b.function))
    });

    // Build summary stats.
    let from_vcs = source_analysis::generate_standalone_vcs(&from_all_funcs);
    let to_vcs = source_analysis::generate_standalone_vcs(&to_all_funcs);

    let from_summary = DiffSummaryStats {
        functions: from_all_funcs.len(),
        public_functions: from_all_funcs.iter().filter(|f| f.is_public).count(),
        unsafe_functions: from_all_funcs.iter().filter(|f| f.is_unsafe).count(),
        specified_functions: from_all_funcs
            .iter()
            .filter(|f| f.has_requires || f.has_ensures)
            .count(),
        total_vcs: from_vcs.len(),
        proved: from_vcs
            .iter()
            .filter(|v| v.outcome == StandaloneOutcome::Proved)
            .count(),
        unknown: from_vcs
            .iter()
            .filter(|v| v.outcome == StandaloneOutcome::Unknown)
            .count(),
    };

    let to_summary = DiffSummaryStats {
        functions: to_all_funcs.len(),
        public_functions: to_all_funcs.iter().filter(|f| f.is_public).count(),
        unsafe_functions: to_all_funcs.iter().filter(|f| f.is_unsafe).count(),
        specified_functions: to_all_funcs
            .iter()
            .filter(|f| f.has_requires || f.has_ensures)
            .count(),
        total_vcs: to_vcs.len(),
        proved: to_vcs
            .iter()
            .filter(|v| v.outcome == StandaloneOutcome::Proved)
            .count(),
        unknown: to_vcs
            .iter()
            .filter(|v| v.outcome == StandaloneOutcome::Unknown)
            .count(),
    };

    Ok(GitDiffReport {
        from_ref: range.from.clone(),
        to_ref: range.to.clone(),
        from_commit,
        to_commit,
        files_changed: changed.len(),
        files_deleted: deleted.len(),
        from_summary,
        to_summary,
        functions_added,
        functions_removed,
        specs_gained,
        specs_lost,
        safety_changes,
        entries,
    })
}

// ---------------------------------------------------------------------------
// Rendering
// ---------------------------------------------------------------------------

impl GitDiffReport {
    pub(crate) fn render_terminal(&self) {
        eprintln!();
        eprintln!("=== tRust Verification Diff ===");
        eprintln!(
            "  {} ({}) .. {} ({})",
            self.from_ref,
            &self.from_commit[..8.min(self.from_commit.len())],
            self.to_ref,
            &self.to_commit[..8.min(self.to_commit.len())],
        );
        eprintln!(
            "  {} files changed, {} files deleted",
            self.files_changed, self.files_deleted
        );
        eprintln!();

        // Summary table.
        eprintln!(
            "  {:>20}  {:>8}  {:>8}",
            "", &self.from_ref, &self.to_ref
        );
        eprintln!(
            "  {:>20}  {:>8}  {:>8}",
            "Functions",
            self.from_summary.functions,
            self.to_summary.functions,
        );
        eprintln!(
            "  {:>20}  {:>8}  {:>8}",
            "Public",
            self.from_summary.public_functions,
            self.to_summary.public_functions,
        );
        eprintln!(
            "  {:>20}  {:>8}  {:>8}",
            "Unsafe",
            self.from_summary.unsafe_functions,
            self.to_summary.unsafe_functions,
        );
        eprintln!(
            "  {:>20}  {:>8}  {:>8}",
            "With specs",
            self.from_summary.specified_functions,
            self.to_summary.specified_functions,
        );
        eprintln!(
            "  {:>20}  {:>8}  {:>8}",
            "VCs (proved)",
            self.from_summary.proved,
            self.to_summary.proved,
        );
        eprintln!(
            "  {:>20}  {:>8}  {:>8}",
            "VCs (unknown)",
            self.from_summary.unknown,
            self.to_summary.unknown,
        );
        eprintln!();

        // Individual changes.
        if self.entries.is_empty() {
            eprintln!("  No verification-relevant changes.");
        } else {
            for entry in &self.entries {
                let icon = match entry.change {
                    FunctionChange::GainedSpec | FunctionChange::Added => "+",
                    FunctionChange::LostSpec | FunctionChange::Removed => "-",
                    FunctionChange::SafetyChanged => "!",
                    FunctionChange::VisibilityChanged => "~",
                    FunctionChange::Unchanged => " ",
                };
                eprintln!(
                    "  [{icon}] {}::{} -- {}",
                    entry.file, entry.function, entry.detail
                );
            }
        }

        eprintln!();

        // Delta summary.
        let delta_specs =
            self.to_summary.specified_functions as i64 - self.from_summary.specified_functions as i64;
        let delta_proved = self.to_summary.proved as i64 - self.from_summary.proved as i64;
        let delta_unsafe =
            self.to_summary.unsafe_functions as i64 - self.from_summary.unsafe_functions as i64;

        eprintln!(
            "Delta: specs {:+}, proved VCs {:+}, unsafe {:+}",
            delta_specs, delta_proved, delta_unsafe
        );
        eprintln!(
            "Summary: {} added, {} removed, {} gained specs, {} lost specs, {} safety changes",
            self.functions_added,
            self.functions_removed,
            self.specs_gained,
            self.specs_lost,
            self.safety_changes,
        );

        // Verdict.
        if self.has_regressions() {
            eprintln!("Result: REGRESSIONS DETECTED");
        } else if self.has_improvements() {
            eprintln!("Result: IMPROVED");
        } else {
            eprintln!("Result: NO CHANGE");
        }
        eprintln!("===============================");
    }

    pub(crate) fn render_json(&self) {
        match serde_json::to_string_pretty(self) {
            Ok(json) => println!("{json}"),
            Err(e) => eprintln!("cargo-trust: failed to serialize git diff: {e}"),
        }
    }

    /// Returns true if the diff contains regressions (lost specs, removed
    /// specified functions, or functions that became unsafe).
    pub(crate) fn has_regressions(&self) -> bool {
        self.specs_lost > 0
            || self.entries.iter().any(|e| {
                e.change == FunctionChange::Removed
                    && e.from_state
                        .as_ref()
                        .is_some_and(|s| s.has_requires || s.has_ensures)
            })
            || self.entries.iter().any(|e| {
                e.change == FunctionChange::SafetyChanged
                    && e.to_state.as_ref().is_some_and(|s| s.is_unsafe)
            })
    }

    /// Returns true if the diff contains improvements.
    pub(crate) fn has_improvements(&self) -> bool {
        self.specs_gained > 0
            || self.entries.iter().any(|e| {
                e.change == FunctionChange::SafetyChanged
                    && e.to_state.as_ref().is_some_and(|s| !s.is_unsafe)
            })
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    #[test]
    fn test_parse_ref_range_double_dot() {
        let range = parse_ref_range("main..feature").expect("should parse");
        assert_eq!(range.from, "main");
        assert_eq!(range.to, "feature");
    }

    #[test]
    fn test_parse_ref_range_with_slashes() {
        let range = parse_ref_range("origin/main..HEAD").expect("should parse");
        assert_eq!(range.from, "origin/main");
        assert_eq!(range.to, "HEAD");
    }

    #[test]
    fn test_parse_ref_range_with_tilde() {
        let range = parse_ref_range("HEAD~5..HEAD").expect("should parse");
        assert_eq!(range.from, "HEAD~5");
        assert_eq!(range.to, "HEAD");
    }

    #[test]
    fn test_parse_ref_range_empty_from() {
        assert!(parse_ref_range("..HEAD").is_none());
    }

    #[test]
    fn test_parse_ref_range_empty_to() {
        assert!(parse_ref_range("main..").is_none());
    }

    #[test]
    fn test_parse_ref_range_no_dots() {
        assert!(parse_ref_range("main").is_none());
    }

    #[test]
    fn test_parse_ref_range_commit_hashes() {
        let range = parse_ref_range("abc123..def456").expect("should parse");
        assert_eq!(range.from, "abc123");
        assert_eq!(range.to, "def456");
    }

    #[test]
    fn test_function_state_from_parsed() {
        let func = ParsedFunction {
            name: "test_fn".into(),
            file: PathBuf::from("src/lib.rs"),
            line: 10,
            is_public: true,
            is_unsafe: false,
            has_requires: true,
            has_ensures: false,
            return_type: Some("i32".into()),
            params: vec!["x".into()],
            typed_params: vec![],
        };
        let state = FunctionState::from(&func);
        assert_eq!(state.name, "test_fn");
        assert!(state.is_public);
        assert!(state.has_requires);
        assert!(!state.has_ensures);
    }

    #[test]
    fn test_git_diff_report_has_regressions() {
        let report = GitDiffReport {
            from_ref: "main".into(),
            to_ref: "feature".into(),
            from_commit: "abc".into(),
            to_commit: "def".into(),
            files_changed: 1,
            files_deleted: 0,
            from_summary: DiffSummaryStats {
                functions: 1,
                public_functions: 1,
                unsafe_functions: 0,
                specified_functions: 1,
                total_vcs: 1,
                proved: 1,
                unknown: 0,
            },
            to_summary: DiffSummaryStats {
                functions: 1,
                public_functions: 1,
                unsafe_functions: 0,
                specified_functions: 0,
                total_vcs: 0,
                proved: 0,
                unknown: 0,
            },
            functions_added: 0,
            functions_removed: 0,
            specs_gained: 0,
            specs_lost: 1,
            safety_changes: 0,
            entries: vec![FunctionDiffEntry {
                function: "foo".into(),
                file: "src/lib.rs".into(),
                change: FunctionChange::LostSpec,
                detail: "#[requires] removed".into(),
                from_state: Some(FunctionState {
                    name: "foo".into(),
                    file: "src/lib.rs".into(),
                    is_public: true,
                    is_unsafe: false,
                    has_requires: true,
                    has_ensures: false,
                }),
                to_state: Some(FunctionState {
                    name: "foo".into(),
                    file: "src/lib.rs".into(),
                    is_public: true,
                    is_unsafe: false,
                    has_requires: false,
                    has_ensures: false,
                }),
            }],
        };
        assert!(report.has_regressions());
        assert!(!report.has_improvements());
    }

    #[test]
    fn test_git_diff_report_has_improvements() {
        let report = GitDiffReport {
            from_ref: "main".into(),
            to_ref: "feature".into(),
            from_commit: "abc".into(),
            to_commit: "def".into(),
            files_changed: 1,
            files_deleted: 0,
            from_summary: DiffSummaryStats {
                functions: 1,
                public_functions: 1,
                unsafe_functions: 0,
                specified_functions: 0,
                total_vcs: 0,
                proved: 0,
                unknown: 0,
            },
            to_summary: DiffSummaryStats {
                functions: 1,
                public_functions: 1,
                unsafe_functions: 0,
                specified_functions: 1,
                total_vcs: 1,
                proved: 1,
                unknown: 0,
            },
            functions_added: 0,
            functions_removed: 0,
            specs_gained: 1,
            specs_lost: 0,
            safety_changes: 0,
            entries: vec![FunctionDiffEntry {
                function: "foo".into(),
                file: "src/lib.rs".into(),
                change: FunctionChange::GainedSpec,
                detail: "#[ensures] added".into(),
                from_state: None,
                to_state: None,
            }],
        };
        assert!(!report.has_regressions());
        assert!(report.has_improvements());
    }

    #[test]
    fn test_git_diff_report_no_changes() {
        let report = GitDiffReport {
            from_ref: "main".into(),
            to_ref: "feature".into(),
            from_commit: "abc".into(),
            to_commit: "def".into(),
            files_changed: 0,
            files_deleted: 0,
            from_summary: DiffSummaryStats {
                functions: 0,
                public_functions: 0,
                unsafe_functions: 0,
                specified_functions: 0,
                total_vcs: 0,
                proved: 0,
                unknown: 0,
            },
            to_summary: DiffSummaryStats {
                functions: 0,
                public_functions: 0,
                unsafe_functions: 0,
                specified_functions: 0,
                total_vcs: 0,
                proved: 0,
                unknown: 0,
            },
            functions_added: 0,
            functions_removed: 0,
            specs_gained: 0,
            specs_lost: 0,
            safety_changes: 0,
            entries: vec![],
        };
        assert!(!report.has_regressions());
        assert!(!report.has_improvements());
    }

    #[test]
    fn test_git_diff_report_json_serialization() {
        let report = GitDiffReport {
            from_ref: "main".into(),
            to_ref: "HEAD".into(),
            from_commit: "abc123".into(),
            to_commit: "def456".into(),
            files_changed: 2,
            files_deleted: 1,
            from_summary: DiffSummaryStats {
                functions: 5,
                public_functions: 3,
                unsafe_functions: 1,
                specified_functions: 2,
                total_vcs: 4,
                proved: 2,
                unknown: 2,
            },
            to_summary: DiffSummaryStats {
                functions: 6,
                public_functions: 4,
                unsafe_functions: 0,
                specified_functions: 3,
                total_vcs: 5,
                proved: 3,
                unknown: 2,
            },
            functions_added: 2,
            functions_removed: 1,
            specs_gained: 1,
            specs_lost: 0,
            safety_changes: 1,
            entries: vec![],
        };
        let json = serde_json::to_string(&report).expect("should serialize");
        assert!(json.contains("\"from_ref\":\"main\""));
        assert!(json.contains("\"specs_gained\":1"));
    }
}
