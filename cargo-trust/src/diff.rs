// cargo-trust diff: Compare verification state against a baseline JSON report
//
// Loads a baseline `JsonProofReport` (or legacy `SavedReport`) and compares
// against a current report. Produces function-level diff with color-coded
// terminal output. Exits non-zero on regressions for CI gate use.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap;
use std::path::Path;
use std::process::ExitCode;

use serde::{Deserialize, Serialize};
use trust_types::{FunctionVerdict, JsonProofReport};

use crate::types::OutputFormat;

// ---------------------------------------------------------------------------
// Diff data structures
// ---------------------------------------------------------------------------

/// The status of a function in a verification report, normalized for comparison.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum FunctionStatus {
    Verified,
    RuntimeChecked,
    HasViolations,
    Inconclusive,
    NoObligations,
}

impl FunctionStatus {
    fn from_verdict(v: FunctionVerdict) -> Self {
        match v {
            FunctionVerdict::Verified => Self::Verified,
            FunctionVerdict::RuntimeChecked => Self::RuntimeChecked,
            FunctionVerdict::HasViolations => Self::HasViolations,
            FunctionVerdict::Inconclusive => Self::Inconclusive,
            FunctionVerdict::NoObligations => Self::NoObligations,
            _ => Self::Inconclusive, // future-proof for non_exhaustive
        }
    }

    fn label(self) -> &'static str {
        match self {
            Self::Verified => "proved",
            Self::RuntimeChecked => "runtime_checked",
            Self::HasViolations => "failed",
            Self::Inconclusive => "unknown",
            Self::NoObligations => "no_obligations",
        }
    }

    /// True if this status represents a "good" state (proved or no obligations).
    fn is_good(self) -> bool {
        matches!(self, Self::Verified | Self::NoObligations | Self::RuntimeChecked)
    }
}

/// Per-function snapshot: status + obligation counts.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct FunctionSnapshot {
    pub status: FunctionStatus,
    pub proved: usize,
    pub failed: usize,
    pub unknown: usize,
    pub total: usize,
}

/// Direction of change for a single function.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum ChangeDirection {
    /// Function went from bad to good (e.g., failed -> proved).
    Improved,
    /// Function went from good to bad (e.g., proved -> failed).
    Regressed,
    /// Function is new in the current report.
    Added,
    /// Function was removed from the current report.
    Removed,
    /// Obligation counts changed but verdict stayed the same.
    ObligationChanged,
    /// No change.
    Unchanged,
}

impl ChangeDirection {
    #[cfg(test)]
    fn label(self) -> &'static str {
        match self {
            Self::Improved => "improved",
            Self::Regressed => "REGRESSED",
            Self::Added => "added",
            Self::Removed => "removed",
            Self::ObligationChanged => "changed",
            Self::Unchanged => "unchanged",
        }
    }
}

/// A single entry in the diff report.
#[derive(Debug, Clone, Serialize)]
pub(crate) struct DiffEntry {
    pub function: String,
    pub direction: ChangeDirection,
    pub baseline: Option<FunctionSnapshot>,
    pub current: Option<FunctionSnapshot>,
}

/// Complete diff report between baseline and current verification state.
#[derive(Debug, Clone, Serialize)]
pub(crate) struct FullDiffReport {
    // Baseline summary
    pub baseline_functions: usize,
    pub baseline_proved: usize,
    pub baseline_failed: usize,
    pub baseline_unknown: usize,
    pub baseline_total_obligations: usize,

    // Current summary
    pub current_functions: usize,
    pub current_proved: usize,
    pub current_failed: usize,
    pub current_unknown: usize,
    pub current_total_obligations: usize,

    // Diff counts
    pub improvements: usize,
    pub regressions: usize,
    pub added: usize,
    pub removed: usize,
    pub obligation_changes: usize,
    pub unchanged: usize,

    // Detailed entries (only changed functions)
    pub entries: Vec<DiffEntry>,

    // CI gate: true if any regressions
    pub has_regressions: bool,
}

// ---------------------------------------------------------------------------
// Building the diff
// ---------------------------------------------------------------------------

/// Extract a function name -> snapshot map from a `JsonProofReport`.
fn extract_function_map(report: &JsonProofReport) -> BTreeMap<String, FunctionSnapshot> {
    let mut map = BTreeMap::new();
    for func in &report.functions {
        let snap = FunctionSnapshot {
            status: FunctionStatus::from_verdict(func.summary.verdict),
            proved: func.summary.proved,
            failed: func.summary.failed,
            unknown: func.summary.unknown,
            total: func.summary.total_obligations,
        };
        map.insert(func.function.clone(), snap);
    }
    map
}

/// Build a full diff report from two `JsonProofReport` instances.
pub(crate) fn build_diff(
    baseline: &JsonProofReport,
    current: &JsonProofReport,
) -> FullDiffReport {
    let base_map = extract_function_map(baseline);
    let curr_map = extract_function_map(current);

    let mut entries = Vec::new();
    let mut improvements = 0usize;
    let mut regressions = 0usize;
    let mut added = 0usize;
    let mut removed = 0usize;
    let mut obligation_changes = 0usize;
    let mut unchanged = 0usize;

    // Check functions in current report against baseline.
    for (name, curr_snap) in &curr_map {
        if let Some(base_snap) = base_map.get(name) {
            let direction = classify_change(base_snap, curr_snap);
            match direction {
                ChangeDirection::Improved => improvements += 1,
                ChangeDirection::Regressed => regressions += 1,
                ChangeDirection::ObligationChanged => obligation_changes += 1,
                ChangeDirection::Unchanged => {
                    unchanged += 1;
                    continue; // Don't include unchanged in entries
                }
                _ => {}
            }
            entries.push(DiffEntry {
                function: name.clone(),
                direction,
                baseline: Some(base_snap.clone()),
                current: Some(curr_snap.clone()),
            });
        } else {
            // New function.
            added += 1;
            entries.push(DiffEntry {
                function: name.clone(),
                direction: ChangeDirection::Added,
                baseline: None,
                current: Some(curr_snap.clone()),
            });
        }
    }

    // Check for removed functions (in baseline but not in current).
    for (name, base_snap) in &base_map {
        if !curr_map.contains_key(name) {
            removed += 1;
            entries.push(DiffEntry {
                function: name.clone(),
                direction: ChangeDirection::Removed,
                baseline: Some(base_snap.clone()),
                current: None,
            });
        }
    }

    // Sort entries: regressions first, then removed, then added, then changes.
    entries.sort_by_key(|e| match e.direction {
        ChangeDirection::Regressed => 0,
        ChangeDirection::Removed => 1,
        ChangeDirection::Added => 2,
        ChangeDirection::Improved => 3,
        ChangeDirection::ObligationChanged => 4,
        ChangeDirection::Unchanged => 5,
    });

    let has_regressions = regressions > 0;

    FullDiffReport {
        baseline_functions: base_map.len(),
        baseline_proved: baseline.summary.total_proved,
        baseline_failed: baseline.summary.total_failed,
        baseline_unknown: baseline.summary.total_unknown,
        baseline_total_obligations: baseline.summary.total_obligations,

        current_functions: curr_map.len(),
        current_proved: current.summary.total_proved,
        current_failed: current.summary.total_failed,
        current_unknown: current.summary.total_unknown,
        current_total_obligations: current.summary.total_obligations,

        improvements,
        regressions,
        added,
        removed,
        obligation_changes,
        unchanged,

        entries,
        has_regressions,
    }
}

/// Classify how a function's verification status changed.
fn classify_change(baseline: &FunctionSnapshot, current: &FunctionSnapshot) -> ChangeDirection {
    if baseline.status == current.status
        && baseline.proved == current.proved
        && baseline.failed == current.failed
        && baseline.unknown == current.unknown
        && baseline.total == current.total
    {
        return ChangeDirection::Unchanged;
    }

    let base_good = baseline.status.is_good();
    let curr_good = current.status.is_good();

    if !base_good && curr_good {
        ChangeDirection::Improved
    } else if base_good && !curr_good {
        ChangeDirection::Regressed
    } else {
        // Same category but counts changed.
        ChangeDirection::ObligationChanged
    }
}

// ---------------------------------------------------------------------------
// Rendering
// ---------------------------------------------------------------------------

// ANSI color codes for terminal output.
const RED: &str = "\x1b[31m";
const GREEN: &str = "\x1b[32m";
const YELLOW: &str = "\x1b[33m";
const CYAN: &str = "\x1b[36m";
const BOLD: &str = "\x1b[1m";
const RESET: &str = "\x1b[0m";

/// Check if color output should be used (respects NO_COLOR env var).
fn use_color() -> bool {
    std::env::var("NO_COLOR").is_err()
}

fn color(code: &str, text: &str) -> String {
    if use_color() {
        format!("{code}{text}{RESET}")
    } else {
        text.to_string()
    }
}

fn bold(text: &str) -> String {
    if use_color() {
        format!("{BOLD}{text}{RESET}")
    } else {
        text.to_string()
    }
}

impl FullDiffReport {
    pub(crate) fn render(&self, format: OutputFormat) {
        match format {
            OutputFormat::Json => {
                match serde_json::to_string_pretty(self) {
                    Ok(json) => println!("{json}"),
                    Err(e) => eprintln!("cargo-trust: failed to serialize diff: {e}"),
                }
            }
            OutputFormat::Terminal | OutputFormat::Html => {
                self.render_terminal();
            }
        }
    }

    fn render_terminal(&self) {
        eprintln!();
        eprintln!("{}", bold("=== tRust Verification Diff ==="));
        eprintln!();

        // Summary comparison
        eprintln!(
            "  Baseline: {} functions, {} proved / {} failed / {} unknown  ({} obligations)",
            self.baseline_functions,
            self.baseline_proved,
            self.baseline_failed,
            self.baseline_unknown,
            self.baseline_total_obligations,
        );
        eprintln!(
            "  Current:  {} functions, {} proved / {} failed / {} unknown  ({} obligations)",
            self.current_functions,
            self.current_proved,
            self.current_failed,
            self.current_unknown,
            self.current_total_obligations,
        );

        // Delta
        let dp = self.current_proved as i64 - self.baseline_proved as i64;
        let df = self.current_failed as i64 - self.baseline_failed as i64;
        let du = self.current_unknown as i64 - self.baseline_unknown as i64;
        let dt = self.current_total_obligations as i64 - self.baseline_total_obligations as i64;
        eprintln!(
            "  Delta:    proved {:+}, failed {:+}, unknown {:+}, obligations {:+}",
            dp, df, du, dt,
        );
        eprintln!();

        // Detailed entries
        if self.entries.is_empty() {
            eprintln!("  No changes detected.");
        } else {
            for entry in &self.entries {
                let (icon, colored_status) = match entry.direction {
                    ChangeDirection::Improved => (
                        color(GREEN, "+"),
                        color(GREEN, "IMPROVED"),
                    ),
                    ChangeDirection::Regressed => (
                        color(RED, "-"),
                        color(RED, "REGRESSED"),
                    ),
                    ChangeDirection::Added => (
                        color(CYAN, "+"),
                        color(CYAN, "ADDED"),
                    ),
                    ChangeDirection::Removed => (
                        color(YELLOW, "-"),
                        color(YELLOW, "REMOVED"),
                    ),
                    ChangeDirection::ObligationChanged => (
                        color(YELLOW, "~"),
                        color(YELLOW, "CHANGED"),
                    ),
                    ChangeDirection::Unchanged => (
                        " ".to_string(),
                        "unchanged".to_string(),
                    ),
                };

                let detail = match (&entry.baseline, &entry.current) {
                    (Some(b), Some(c)) => {
                        format!(
                            "{} -> {}  ({}/{} -> {}/{})",
                            b.status.label(),
                            c.status.label(),
                            b.proved,
                            b.total,
                            c.proved,
                            c.total,
                        )
                    }
                    (None, Some(c)) => {
                        format!(
                            "(new) {}  ({}/{})",
                            c.status.label(),
                            c.proved,
                            c.total,
                        )
                    }
                    (Some(b), None) => {
                        format!(
                            "{} -> (removed)  (was {}/{})",
                            b.status.label(),
                            b.proved,
                            b.total,
                        )
                    }
                    (None, None) => String::new(),
                };

                eprintln!(
                    "  [{icon}] {colored_status:>12}  {}  {detail}",
                    bold(&entry.function),
                );
            }
        }

        eprintln!();

        // Counts summary
        eprintln!(
            "  {} improvements, {} regressions, {} added, {} removed, {} obligation changes",
            color(GREEN, &self.improvements.to_string()),
            color(if self.regressions > 0 { RED } else { GREEN }, &self.regressions.to_string()),
            color(CYAN, &self.added.to_string()),
            color(YELLOW, &self.removed.to_string()),
            self.obligation_changes,
        );

        // CI gate result
        if self.has_regressions {
            eprintln!(
                "  {}",
                color(RED, "FAIL: verification regressions detected (exit 1)"),
            );
        } else {
            eprintln!(
                "  {}",
                color(GREEN, "PASS: no verification regressions"),
            );
        }

        eprintln!("{}", bold("================================"));
    }
}

// ---------------------------------------------------------------------------
// Loading reports from files
// ---------------------------------------------------------------------------

/// Load a `JsonProofReport` from a JSON file.
///
/// Supports both the canonical `JsonProofReport` format and the legacy
/// `SavedReport` format (which only has `results: Vec<VerificationResult>`).
pub(crate) fn load_report(path: &Path) -> Result<JsonProofReport, String> {
    let content = std::fs::read_to_string(path)
        .map_err(|e| format!("failed to read `{}`: {e}", path.display()))?;

    // Try canonical format first.
    if let Ok(report) = serde_json::from_str::<JsonProofReport>(&content) {
        return Ok(report);
    }

    // Try legacy format: { results: [...] }
    if let Ok(legacy) = serde_json::from_str::<LegacySavedReport>(&content) {
        return Ok(legacy_to_json_proof_report(&legacy));
    }

    Err(format!(
        "failed to parse `{}` as JsonProofReport or legacy report",
        path.display()
    ))
}

/// Legacy saved report format for backward compatibility.
#[derive(Debug, Deserialize)]
struct LegacySavedReport {
    #[serde(default)]
    results: Vec<LegacyResult>,
}

#[derive(Debug, Deserialize)]
struct LegacyResult {
    kind: String,
    message: String,
    outcome: LegacyOutcome,
    backend: String,
    time_ms: Option<u64>,
}

#[derive(Debug, Clone, Copy, Deserialize, PartialEq, Eq)]
enum LegacyOutcome {
    Proved,
    Failed,
    Unknown,
}

/// Convert a legacy saved report into the canonical `JsonProofReport` format.
fn legacy_to_json_proof_report(legacy: &LegacySavedReport) -> JsonProofReport {
    use trust_types::*;

    // Group results by kind as pseudo-functions.
    let mut groups: BTreeMap<String, Vec<&LegacyResult>> = BTreeMap::new();
    for r in &legacy.results {
        groups.entry(r.kind.clone()).or_default().push(r);
    }

    let mut functions = Vec::new();
    let mut total_proved = 0usize;
    let mut total_failed = 0usize;
    let mut total_unknown = 0usize;

    for (kind, results) in &groups {
        let proved = results.iter().filter(|r| r.outcome == LegacyOutcome::Proved).count();
        let failed = results.iter().filter(|r| r.outcome == LegacyOutcome::Failed).count();
        let unknown = results.iter().filter(|r| r.outcome == LegacyOutcome::Unknown).count();
        let total = results.len();

        total_proved += proved;
        total_failed += failed;
        total_unknown += unknown;

        let verdict = if failed > 0 {
            FunctionVerdict::HasViolations
        } else if unknown > 0 {
            FunctionVerdict::Inconclusive
        } else {
            FunctionVerdict::Verified
        };

        let obligations: Vec<ObligationReport> = results
            .iter()
            .map(|r| {
                let outcome = match r.outcome {
                    LegacyOutcome::Proved => ObligationOutcome::Proved {
                        strength: ProofStrength::smt_unsat(),
                    },
                    LegacyOutcome::Failed => ObligationOutcome::Failed {
                        counterexample: None,
                    },
                    LegacyOutcome::Unknown => ObligationOutcome::Unknown {
                        reason: "unknown".to_string(),
                    },
                };
                ObligationReport {
                    description: r.message.clone(),
                    kind: r.kind.clone(),
                    proof_level: ProofLevel::L0Safety,
                    location: None,
                    outcome,
                    solver: r.backend.clone(),
                    time_ms: r.time_ms.unwrap_or(0),
                    evidence: None,
                }
            })
            .collect();

        let total_time_ms: u64 = results.iter().filter_map(|r| r.time_ms).sum();

        functions.push(FunctionProofReport {
            function: kind.clone(),
            summary: FunctionSummary {
                total_obligations: total,
                proved,
                runtime_checked: 0,
                failed,
                unknown,
                total_time_ms,
                max_proof_level: Some(ProofLevel::L0Safety),
                verdict,
            },
            obligations,
        });
    }

    let total = total_proved + total_failed + total_unknown;
    let functions_verified = functions
        .iter()
        .filter(|f| f.summary.verdict == FunctionVerdict::Verified)
        .count();
    let functions_with_violations = functions
        .iter()
        .filter(|f| f.summary.verdict == FunctionVerdict::HasViolations)
        .count();
    let functions_inconclusive = functions
        .iter()
        .filter(|f| f.summary.verdict == FunctionVerdict::Inconclusive)
        .count();

    let verdict = if total_failed > 0 {
        CrateVerdict::HasViolations
    } else if total_unknown > 0 {
        CrateVerdict::Inconclusive
    } else if total_proved > 0 {
        CrateVerdict::Verified
    } else {
        CrateVerdict::NoObligations
    };

    JsonProofReport {
        metadata: ReportMetadata {
            schema_version: "1.0".to_string(),
            trust_version: "legacy".to_string(),
            timestamp: String::new(),
            total_time_ms: 0,
        },
        crate_name: "unknown".to_string(),
        summary: CrateSummary {
            functions_analyzed: functions.len(),
            functions_verified,
            functions_runtime_checked: 0,
            functions_with_violations,
            functions_inconclusive,
            total_obligations: total,
            total_proved,
            total_runtime_checked: 0,
            total_failed,
            total_unknown,
            verdict,
        },
        functions,
    }
}

// ---------------------------------------------------------------------------
// Subcommand entry point
// ---------------------------------------------------------------------------

/// Run the `cargo trust diff` subcommand.
///
/// Requires `--baseline <path>` pointing to a saved JSON report.
/// Optionally accepts a second positional argument `--current <path>` for
/// comparing two saved reports (otherwise compares baseline against the
/// current verification run or an empty report).
pub(crate) fn run_diff_command(
    baseline_path: &str,
    current_path: Option<&str>,
    format: OutputFormat,
) -> ExitCode {
    // Load baseline.
    let baseline = match load_report(Path::new(baseline_path)) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("cargo-trust: {e}");
            return ExitCode::from(2);
        }
    };

    // Load current report (or use an empty one if no current path given).
    let current = if let Some(path) = current_path {
        match load_report(Path::new(path)) {
            Ok(r) => r,
            Err(e) => {
                eprintln!("cargo-trust: {e}");
                return ExitCode::from(2);
            }
        }
    } else {
        // Show baseline summary against empty.
        eprintln!("cargo-trust: no --current specified, showing baseline summary against empty");
        empty_report()
    };

    let diff = build_diff(&baseline, &current);
    diff.render(format);

    if diff.has_regressions {
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    }
}

/// Create an empty `JsonProofReport` for comparison.
fn empty_report() -> JsonProofReport {
    use trust_types::*;
    JsonProofReport {
        metadata: ReportMetadata {
            schema_version: "1.0".to_string(),
            trust_version: "empty".to_string(),
            timestamp: String::new(),
            total_time_ms: 0,
        },
        crate_name: "empty".to_string(),
        summary: CrateSummary {
            functions_analyzed: 0,
            functions_verified: 0,
            functions_runtime_checked: 0,
            functions_with_violations: 0,
            functions_inconclusive: 0,
            total_obligations: 0,
            total_proved: 0,
            total_runtime_checked: 0,
            total_failed: 0,
            total_unknown: 0,
            verdict: CrateVerdict::NoObligations,
        },
        functions: vec![],
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use trust_types::*;

    fn make_report(functions: Vec<(&str, FunctionVerdict, usize, usize, usize)>) -> JsonProofReport {
        let mut funcs = Vec::new();
        let mut tp = 0;
        let mut tf = 0;
        let mut tu = 0;

        for (name, verdict, proved, failed, unknown) in &functions {
            tp += proved;
            tf += failed;
            tu += unknown;
            let total = proved + failed + unknown;

            let obligations = Vec::new(); // not needed for diff tests

            funcs.push(FunctionProofReport {
                function: name.to_string(),
                summary: FunctionSummary {
                    total_obligations: total,
                    proved: *proved,
                    runtime_checked: 0,
                    failed: *failed,
                    unknown: *unknown,
                    total_time_ms: 0,
                    max_proof_level: Some(ProofLevel::L0Safety),
                    verdict: *verdict,
                },
                obligations,
            });
        }

        let fv = funcs.iter().filter(|f| f.summary.verdict == FunctionVerdict::Verified).count();
        let fviol = funcs.iter().filter(|f| f.summary.verdict == FunctionVerdict::HasViolations).count();
        let finc = funcs.iter().filter(|f| f.summary.verdict == FunctionVerdict::Inconclusive).count();

        let verdict = if tf > 0 {
            CrateVerdict::HasViolations
        } else if tu > 0 {
            CrateVerdict::Inconclusive
        } else if tp > 0 {
            CrateVerdict::Verified
        } else {
            CrateVerdict::NoObligations
        };

        JsonProofReport {
            metadata: ReportMetadata {
                schema_version: "1.0".to_string(),
                trust_version: "test".to_string(),
                timestamp: String::new(),
                total_time_ms: 0,
            },
            crate_name: "test_crate".to_string(),
            summary: CrateSummary {
                functions_analyzed: funcs.len(),
                functions_verified: fv,
                functions_runtime_checked: 0,
                functions_with_violations: fviol,
                functions_inconclusive: finc,
                total_obligations: tp + tf + tu,
                total_proved: tp,
                total_runtime_checked: 0,
                total_failed: tf,
                total_unknown: tu,
                verdict,
            },
            functions: funcs,
        }
    }

    #[test]
    fn test_diff_no_changes() {
        let baseline = make_report(vec![
            ("safe_add", FunctionVerdict::Verified, 2, 0, 0),
            ("safe_div", FunctionVerdict::Verified, 1, 0, 0),
        ]);
        let current = make_report(vec![
            ("safe_add", FunctionVerdict::Verified, 2, 0, 0),
            ("safe_div", FunctionVerdict::Verified, 1, 0, 0),
        ]);

        let diff = build_diff(&baseline, &current);
        assert_eq!(diff.improvements, 0);
        assert_eq!(diff.regressions, 0);
        assert_eq!(diff.added, 0);
        assert_eq!(diff.removed, 0);
        assert_eq!(diff.unchanged, 2);
        assert!(diff.entries.is_empty());
        assert!(!diff.has_regressions);
    }

    #[test]
    fn test_diff_regression() {
        let baseline = make_report(vec![
            ("safe_add", FunctionVerdict::Verified, 2, 0, 0),
        ]);
        let current = make_report(vec![
            ("safe_add", FunctionVerdict::HasViolations, 1, 1, 0),
        ]);

        let diff = build_diff(&baseline, &current);
        assert_eq!(diff.regressions, 1);
        assert_eq!(diff.improvements, 0);
        assert!(diff.has_regressions);
        assert_eq!(diff.entries.len(), 1);
        assert_eq!(diff.entries[0].direction, ChangeDirection::Regressed);
    }

    #[test]
    fn test_diff_improvement() {
        let baseline = make_report(vec![
            ("buggy_fn", FunctionVerdict::HasViolations, 0, 2, 0),
        ]);
        let current = make_report(vec![
            ("buggy_fn", FunctionVerdict::Verified, 2, 0, 0),
        ]);

        let diff = build_diff(&baseline, &current);
        assert_eq!(diff.improvements, 1);
        assert_eq!(diff.regressions, 0);
        assert!(!diff.has_regressions);
        assert_eq!(diff.entries.len(), 1);
        assert_eq!(diff.entries[0].direction, ChangeDirection::Improved);
    }

    #[test]
    fn test_diff_added_function() {
        let baseline = make_report(vec![
            ("old_fn", FunctionVerdict::Verified, 1, 0, 0),
        ]);
        let current = make_report(vec![
            ("old_fn", FunctionVerdict::Verified, 1, 0, 0),
            ("new_fn", FunctionVerdict::Verified, 2, 0, 0),
        ]);

        let diff = build_diff(&baseline, &current);
        assert_eq!(diff.added, 1);
        assert_eq!(diff.unchanged, 1);
        assert!(!diff.has_regressions);
        assert_eq!(diff.entries.len(), 1);
        assert_eq!(diff.entries[0].direction, ChangeDirection::Added);
        assert_eq!(diff.entries[0].function, "new_fn");
    }

    #[test]
    fn test_diff_removed_function() {
        let baseline = make_report(vec![
            ("old_fn", FunctionVerdict::Verified, 1, 0, 0),
            ("removed_fn", FunctionVerdict::HasViolations, 0, 1, 0),
        ]);
        let current = make_report(vec![
            ("old_fn", FunctionVerdict::Verified, 1, 0, 0),
        ]);

        let diff = build_diff(&baseline, &current);
        assert_eq!(diff.removed, 1);
        assert_eq!(diff.unchanged, 1);
        assert!(!diff.has_regressions);
        assert_eq!(diff.entries.len(), 1);
        assert_eq!(diff.entries[0].direction, ChangeDirection::Removed);
        assert_eq!(diff.entries[0].function, "removed_fn");
    }

    #[test]
    fn test_diff_obligation_count_change() {
        let baseline = make_report(vec![
            ("fn_a", FunctionVerdict::Verified, 2, 0, 0),
        ]);
        let current = make_report(vec![
            ("fn_a", FunctionVerdict::Verified, 3, 0, 0),
        ]);

        let diff = build_diff(&baseline, &current);
        assert_eq!(diff.obligation_changes, 1);
        assert_eq!(diff.regressions, 0);
        assert!(!diff.has_regressions);
        assert_eq!(diff.entries.len(), 1);
        assert_eq!(diff.entries[0].direction, ChangeDirection::ObligationChanged);
    }

    #[test]
    fn test_diff_mixed_changes() {
        let baseline = make_report(vec![
            ("proved_fn", FunctionVerdict::Verified, 2, 0, 0),
            ("failed_fn", FunctionVerdict::HasViolations, 0, 1, 0),
            ("will_remove", FunctionVerdict::Verified, 1, 0, 0),
            ("stable_fn", FunctionVerdict::Verified, 1, 0, 0),
        ]);
        let current = make_report(vec![
            ("proved_fn", FunctionVerdict::HasViolations, 1, 1, 0),  // regressed
            ("failed_fn", FunctionVerdict::Verified, 1, 0, 0),       // improved
            ("new_fn", FunctionVerdict::Verified, 2, 0, 0),          // added
            ("stable_fn", FunctionVerdict::Verified, 1, 0, 0),       // unchanged
        ]);

        let diff = build_diff(&baseline, &current);
        assert_eq!(diff.regressions, 1);
        assert_eq!(diff.improvements, 1);
        assert_eq!(diff.added, 1);
        assert_eq!(diff.removed, 1);
        assert_eq!(diff.unchanged, 1);
        assert!(diff.has_regressions);

        // Check sort order: regressions first
        assert_eq!(diff.entries[0].direction, ChangeDirection::Regressed);
    }

    #[test]
    fn test_diff_ci_gate_no_regressions() {
        let baseline = make_report(vec![
            ("fn_a", FunctionVerdict::HasViolations, 0, 1, 0),
        ]);
        let current = make_report(vec![
            ("fn_a", FunctionVerdict::HasViolations, 0, 1, 0),
            ("fn_b", FunctionVerdict::HasViolations, 0, 2, 0),
        ]);

        let diff = build_diff(&baseline, &current);
        // fn_a unchanged (still bad), fn_b is new (not a regression)
        assert!(!diff.has_regressions);
    }

    #[test]
    fn test_diff_json_serialization() {
        let baseline = make_report(vec![
            ("fn_a", FunctionVerdict::Verified, 2, 0, 0),
        ]);
        let current = make_report(vec![
            ("fn_a", FunctionVerdict::HasViolations, 1, 1, 0),
        ]);

        let diff = build_diff(&baseline, &current);
        let json = serde_json::to_string(&diff).expect("should serialize FullDiffReport");
        assert!(json.contains("\"has_regressions\":true"));
        assert!(json.contains("\"regressions\":1"));
        assert!(json.contains("\"Regressed\""));
    }

    #[test]
    fn test_diff_empty_baseline_all_added() {
        let baseline = make_report(vec![]);
        let current = make_report(vec![
            ("fn_a", FunctionVerdict::Verified, 1, 0, 0),
            ("fn_b", FunctionVerdict::HasViolations, 0, 1, 0),
        ]);

        let diff = build_diff(&baseline, &current);
        assert_eq!(diff.added, 2);
        assert_eq!(diff.regressions, 0);
        assert!(!diff.has_regressions);
    }

    #[test]
    fn test_diff_empty_current_all_removed() {
        let baseline = make_report(vec![
            ("fn_a", FunctionVerdict::Verified, 1, 0, 0),
            ("fn_b", FunctionVerdict::HasViolations, 0, 1, 0),
        ]);
        let current = make_report(vec![]);

        let diff = build_diff(&baseline, &current);
        assert_eq!(diff.removed, 2);
        assert_eq!(diff.regressions, 0);
        assert!(!diff.has_regressions);
    }

    #[test]
    fn test_function_status_labels() {
        assert_eq!(FunctionStatus::Verified.label(), "proved");
        assert_eq!(FunctionStatus::HasViolations.label(), "failed");
        assert_eq!(FunctionStatus::Inconclusive.label(), "unknown");
        assert_eq!(FunctionStatus::RuntimeChecked.label(), "runtime_checked");
        assert_eq!(FunctionStatus::NoObligations.label(), "no_obligations");
    }

    #[test]
    fn test_function_status_is_good() {
        assert!(FunctionStatus::Verified.is_good());
        assert!(FunctionStatus::NoObligations.is_good());
        assert!(FunctionStatus::RuntimeChecked.is_good());
        assert!(!FunctionStatus::HasViolations.is_good());
        assert!(!FunctionStatus::Inconclusive.is_good());
    }

    #[test]
    fn test_change_direction_labels() {
        assert_eq!(ChangeDirection::Improved.label(), "improved");
        assert_eq!(ChangeDirection::Regressed.label(), "REGRESSED");
        assert_eq!(ChangeDirection::Added.label(), "added");
        assert_eq!(ChangeDirection::Removed.label(), "removed");
    }

    #[test]
    fn test_unknown_to_proved_is_improvement() {
        let baseline = make_report(vec![
            ("fn_a", FunctionVerdict::Inconclusive, 0, 0, 2),
        ]);
        let current = make_report(vec![
            ("fn_a", FunctionVerdict::Verified, 2, 0, 0),
        ]);

        let diff = build_diff(&baseline, &current);
        assert_eq!(diff.improvements, 1);
        assert!(!diff.has_regressions);
    }

    #[test]
    fn test_proved_to_unknown_is_regression() {
        let baseline = make_report(vec![
            ("fn_a", FunctionVerdict::Verified, 2, 0, 0),
        ]);
        let current = make_report(vec![
            ("fn_a", FunctionVerdict::Inconclusive, 0, 0, 2),
        ]);

        let diff = build_diff(&baseline, &current);
        assert_eq!(diff.regressions, 1);
        assert!(diff.has_regressions);
    }

    #[test]
    fn test_legacy_report_conversion() {
        let legacy = LegacySavedReport {
            results: vec![
                LegacyResult {
                    kind: "overflow:add".to_string(),
                    message: "arithmetic overflow".to_string(),
                    outcome: LegacyOutcome::Proved,
                    backend: "z4".to_string(),
                    time_ms: Some(5),
                },
                LegacyResult {
                    kind: "div_by_zero".to_string(),
                    message: "division by zero".to_string(),
                    outcome: LegacyOutcome::Failed,
                    backend: "z4".to_string(),
                    time_ms: Some(3),
                },
            ],
        };

        let report = legacy_to_json_proof_report(&legacy);
        assert_eq!(report.functions.len(), 2);
        assert_eq!(report.summary.total_proved, 1);
        assert_eq!(report.summary.total_failed, 1);

        // Check that div_by_zero function has violations
        let div_fn = report.functions.iter().find(|f| f.function == "div_by_zero").unwrap();
        assert_eq!(div_fn.summary.verdict, FunctionVerdict::HasViolations);

        // Check that overflow function is verified
        let ov_fn = report.functions.iter().find(|f| f.function == "overflow:add").unwrap();
        assert_eq!(ov_fn.summary.verdict, FunctionVerdict::Verified);
    }
}
