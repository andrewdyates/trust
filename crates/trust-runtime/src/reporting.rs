// trust-runtime/reporting.rs: Aggregate runtime check results and hot path analysis
//
// After runtime checks execute, this module collects results, computes
// statistics, and identifies hot-path checks that need optimization.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;

use serde::{Deserialize, Serialize};

use crate::instrumentation::CheckOverhead;
use crate::RuntimeCheck;

// ---------------------------------------------------------------------------
// CheckResult
// ---------------------------------------------------------------------------

/// Outcome of a single runtime check execution.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub(crate) enum CheckOutcome {
    /// Check passed (condition held).
    Passed,
    /// Check failed (condition violated).
    Failed { message: String },
    /// Check was skipped (sampling decided not to execute).
    Skipped,
}

/// A recorded check execution with its outcome and timing.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct CheckResult {
    /// The check that was executed.
    pub check: RuntimeCheck,
    /// The outcome.
    pub outcome: CheckOutcome,
    /// Execution time in nanoseconds (0 if skipped).
    pub time_ns: u64,
}

// ---------------------------------------------------------------------------
// RuntimeReport
// ---------------------------------------------------------------------------

/// Aggregated report of runtime check execution across a program run.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct RuntimeReport {
    /// Total number of check invocations (including skipped).
    pub total_invocations: u64,
    /// Number of checks that passed.
    pub passed: u64,
    /// Number of checks that failed.
    pub failed: u64,
    /// Number of checks that were skipped (sampling).
    pub skipped: u64,
    /// Total execution time in nanoseconds.
    pub total_time_ns: u64,
    /// Per-function summaries.
    pub function_summaries: Vec<FunctionSummary>,
    /// Hot path analysis results.
    pub hot_paths: Vec<HotPathEntry>,
}

/// Summary of check results for a single function.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct FunctionSummary {
    /// Function name.
    pub function: String,
    /// Number of distinct checks in this function.
    pub check_count: usize,
    /// Total invocations for this function's checks.
    pub invocations: u64,
    /// Number of failures in this function.
    pub failures: u64,
    /// Total execution time in nanoseconds for this function's checks.
    pub time_ns: u64,
}

/// A check identified as being on a hot path.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct HotPathEntry {
    /// The check.
    pub check: RuntimeCheck,
    /// Number of invocations.
    pub invocations: u64,
    /// Total time spent in nanoseconds.
    pub total_time_ns: u64,
    /// Average time per execution in nanoseconds.
    pub avg_time_ns: u64,
    /// Why this was flagged as hot.
    pub reason: HotPathReason,
}

/// Reason a check was flagged as a hot path candidate.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
#[allow(clippy::enum_variant_names)]
pub(crate) enum HotPathReason {
    /// High invocation count (above threshold).
    HighInvocationCount { count: u64, threshold: u64 },
    /// High total time (above threshold).
    HighTotalTime { time_ns: u64, threshold_ns: u64 },
    /// High per-invocation cost (expensive check called frequently).
    HighPerInvocationCost { avg_ns: u64, threshold_ns: u64 },
}

// ---------------------------------------------------------------------------
// RuntimeReporter
// ---------------------------------------------------------------------------

/// Collects check results and produces aggregated reports.
pub(crate) struct RuntimeReporter {
    results: Vec<CheckResult>,
    /// Minimum invocation count to be considered a hot path.
    hot_invocation_threshold: u64,
    /// Minimum total time (ns) to be considered a hot path.
    hot_time_threshold_ns: u64,
    /// Minimum avg time per invocation (ns) for expensive checks.
    hot_avg_threshold_ns: u64,
}

impl RuntimeReporter {
    /// Create a new reporter with default thresholds.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            results: Vec::new(),
            hot_invocation_threshold: 1000,
            hot_time_threshold_ns: 1_000_000, // 1ms
            hot_avg_threshold_ns: 1000,        // 1us
        }
    }

    /// Set the hot path invocation threshold.
    #[must_use]
    pub(crate) fn with_invocation_threshold(mut self, threshold: u64) -> Self {
        self.hot_invocation_threshold = threshold;
        self
    }

    /// Set the hot path total time threshold (nanoseconds).
    #[must_use]
    pub(crate) fn with_time_threshold_ns(mut self, threshold_ns: u64) -> Self {
        self.hot_time_threshold_ns = threshold_ns;
        self
    }

    /// Set the hot path average time threshold (nanoseconds).
    #[must_use]
    pub(crate) fn with_avg_threshold_ns(mut self, threshold_ns: u64) -> Self {
        self.hot_avg_threshold_ns = threshold_ns;
        self
    }

    /// Record a check result.
    pub(crate) fn record(&mut self, result: CheckResult) {
        self.results.push(result);
    }

    /// Record multiple check results.
    pub(crate) fn record_batch(&mut self, results: impl IntoIterator<Item = CheckResult>) {
        self.results.extend(results);
    }

    /// Generate the aggregated report.
    #[must_use]
    pub(crate) fn report(&self) -> RuntimeReport {
        let mut passed = 0u64;
        let mut failed = 0u64;
        let mut skipped = 0u64;
        let mut total_time_ns = 0u64;

        for r in &self.results {
            match r.outcome {
                CheckOutcome::Passed => passed += 1,
                CheckOutcome::Failed { .. } => failed += 1,
                CheckOutcome::Skipped => skipped += 1,
            }
            total_time_ns += r.time_ns;
        }

        let function_summaries = self.build_function_summaries();
        let hot_paths = self.hot_path_analysis();

        RuntimeReport {
            total_invocations: passed + failed + skipped,
            passed,
            failed,
            skipped,
            total_time_ns,
            function_summaries,
            hot_paths,
        }
    }

    /// Identify checks on hot paths based on configured thresholds.
    #[must_use]
    pub(crate) fn hot_path_analysis(&self) -> Vec<HotPathEntry> {
        // Aggregate by (function, check kind description, location line).
        // We use a string key since CheckKind doesn't implement Hash.
        let mut aggregated: FxHashMap<String, (RuntimeCheck, u64, u64, u64)> = FxHashMap::default();

        for r in &self.results {
            let key = format!(
                "{}:{}:{}",
                r.check.function,
                r.check.location.line_start,
                r.check.description,
            );
            let entry = aggregated
                .entry(key)
                .or_insert_with(|| (r.check.clone(), 0, 0, 0));
            entry.1 += 1; // invocations
            entry.2 += r.time_ns; // total time
            if matches!(r.outcome, CheckOutcome::Failed { .. }) {
                entry.3 += 1; // failures
            }
        }

        let mut hot_paths = Vec::new();
        for (check, invocations, total_time, _failures) in aggregated.values() {
            let avg_time = if *invocations > 0 {
                *total_time / *invocations
            } else {
                0
            };

            if *invocations >= self.hot_invocation_threshold {
                hot_paths.push(HotPathEntry {
                    check: check.clone(),
                    invocations: *invocations,
                    total_time_ns: *total_time,
                    avg_time_ns: avg_time,
                    reason: HotPathReason::HighInvocationCount {
                        count: *invocations,
                        threshold: self.hot_invocation_threshold,
                    },
                });
            } else if *total_time >= self.hot_time_threshold_ns {
                hot_paths.push(HotPathEntry {
                    check: check.clone(),
                    invocations: *invocations,
                    total_time_ns: *total_time,
                    avg_time_ns: avg_time,
                    reason: HotPathReason::HighTotalTime {
                        time_ns: *total_time,
                        threshold_ns: self.hot_time_threshold_ns,
                    },
                });
            } else if avg_time >= self.hot_avg_threshold_ns && *invocations > 0 {
                hot_paths.push(HotPathEntry {
                    check: check.clone(),
                    invocations: *invocations,
                    total_time_ns: *total_time,
                    avg_time_ns: avg_time,
                    reason: HotPathReason::HighPerInvocationCost {
                        avg_ns: avg_time,
                        threshold_ns: self.hot_avg_threshold_ns,
                    },
                });
            }
        }

        // Sort by total time descending for stable output.
        hot_paths.sort_by(|a, b| b.total_time_ns.cmp(&a.total_time_ns));
        hot_paths
    }

    /// Build per-function summaries.
    fn build_function_summaries(&self) -> Vec<FunctionSummary> {
        let mut by_fn: FxHashMap<String, (usize, u64, u64, u64)> = FxHashMap::default();

        // Track distinct checks per function.
        let mut seen_checks: FxHashMap<String, Vec<String>> = FxHashMap::default();

        for r in &self.results {
            let entry = by_fn
                .entry(r.check.function.clone())
                .or_insert((0, 0, 0, 0));
            entry.1 += 1; // invocations
            if matches!(r.outcome, CheckOutcome::Failed { .. }) {
                entry.2 += 1; // failures
            }
            entry.3 += r.time_ns;

            // Track distinct check descriptions per function.
            let check_key = format!(
                "{}:{}",
                r.check.location.line_start, r.check.description
            );
            let fn_checks = seen_checks.entry(r.check.function.clone()).or_default();
            if !fn_checks.contains(&check_key) {
                fn_checks.push(check_key);
                entry.0 += 1; // distinct check count
            }
        }

        let mut summaries: Vec<FunctionSummary> = by_fn
            .into_iter()
            .map(|(function, (check_count, invocations, failures, time_ns))| {
                FunctionSummary {
                    function,
                    check_count,
                    invocations,
                    failures,
                    time_ns,
                }
            })
            .collect();

        summaries.sort_by(|a, b| b.time_ns.cmp(&a.time_ns));
        summaries
    }

    /// Number of recorded results.
    #[must_use]
    pub(crate) fn result_count(&self) -> usize {
        self.results.len()
    }

    /// Clear all recorded results.
    pub(crate) fn clear(&mut self) {
        self.results.clear();
    }
}

impl Default for RuntimeReporter {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Convenience: overhead-based hot path hint
// ---------------------------------------------------------------------------

/// Check whether a runtime check is likely to be on a hot path based on
/// its overhead classification and a call count estimate.
#[must_use]
pub(crate) fn is_likely_hot_path(overhead: CheckOverhead, estimated_calls: u64) -> bool {
    match overhead {
        CheckOverhead::ZeroCost => false, // never hot regardless of call count
        CheckOverhead::Lightweight => estimated_calls > 10_000,
        CheckOverhead::Expensive => estimated_calls > 100,
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CheckKind, CheckStrategy, RuntimeCheck};
    use trust_types::SourceSpan;

    fn span(line: u32) -> SourceSpan {
        SourceSpan {
            file: "src/lib.rs".to_string(),
            line_start: line,
            col_start: 5,
            line_end: line,
            col_end: 20,
        }
    }

    fn make_check(function: &str, kind: CheckKind, line: u32) -> RuntimeCheck {
        RuntimeCheck {
            kind: kind.clone(),
            location: span(line),
            description: format!("{kind:?} at line {line}"),
            strategy: CheckStrategy::BoundsCheck,
            function: function.to_string(),
        }
    }

    fn passed_result(check: RuntimeCheck, time_ns: u64) -> CheckResult {
        CheckResult {
            check,
            outcome: CheckOutcome::Passed,
            time_ns,
        }
    }

    fn failed_result(check: RuntimeCheck, time_ns: u64) -> CheckResult {
        CheckResult {
            check,
            outcome: CheckOutcome::Failed {
                message: "violation".to_string(),
            },
            time_ns,
        }
    }

    fn skipped_result(check: RuntimeCheck) -> CheckResult {
        CheckResult {
            check,
            outcome: CheckOutcome::Skipped,
            time_ns: 0,
        }
    }

    // -----------------------------------------------------------------------
    // RuntimeReporter basics
    // -----------------------------------------------------------------------

    #[test]
    fn test_reporter_empty() {
        let reporter = RuntimeReporter::new();
        let report = reporter.report();
        assert_eq!(report.total_invocations, 0);
        assert_eq!(report.passed, 0);
        assert_eq!(report.failed, 0);
        assert_eq!(report.skipped, 0);
        assert_eq!(report.total_time_ns, 0);
        assert!(report.function_summaries.is_empty());
        assert!(report.hot_paths.is_empty());
    }

    #[test]
    fn test_reporter_counts() {
        let mut reporter = RuntimeReporter::new();
        let check = make_check("f", CheckKind::IndexOutOfBounds, 10);

        reporter.record(passed_result(check.clone(), 100));
        reporter.record(passed_result(check.clone(), 200));
        reporter.record(failed_result(check.clone(), 300));
        reporter.record(skipped_result(check));

        let report = reporter.report();
        assert_eq!(report.total_invocations, 4);
        assert_eq!(report.passed, 2);
        assert_eq!(report.failed, 1);
        assert_eq!(report.skipped, 1);
        assert_eq!(report.total_time_ns, 600);
    }

    #[test]
    fn test_reporter_record_batch() {
        let mut reporter = RuntimeReporter::new();
        let check = make_check("f", CheckKind::IndexOutOfBounds, 10);

        reporter.record_batch(vec![
            passed_result(check.clone(), 100),
            failed_result(check, 200),
        ]);

        assert_eq!(reporter.result_count(), 2);
    }

    #[test]
    fn test_reporter_clear() {
        let mut reporter = RuntimeReporter::new();
        let check = make_check("f", CheckKind::IndexOutOfBounds, 10);

        reporter.record(passed_result(check, 100));
        assert_eq!(reporter.result_count(), 1);

        reporter.clear();
        assert_eq!(reporter.result_count(), 0);
    }

    // -----------------------------------------------------------------------
    // Function summaries
    // -----------------------------------------------------------------------

    #[test]
    fn test_function_summaries() {
        let mut reporter = RuntimeReporter::new();

        let check_f = make_check("f", CheckKind::IndexOutOfBounds, 10);
        let check_g = make_check("g", CheckKind::DivisionByZero, 20);

        reporter.record(passed_result(check_f.clone(), 100));
        reporter.record(failed_result(check_f, 200));
        reporter.record(passed_result(check_g, 50));

        let report = reporter.report();
        assert_eq!(report.function_summaries.len(), 2);

        // Sorted by time_ns descending: f (300) before g (50).
        assert_eq!(report.function_summaries[0].function, "f");
        assert_eq!(report.function_summaries[0].invocations, 2);
        assert_eq!(report.function_summaries[0].failures, 1);
        assert_eq!(report.function_summaries[0].time_ns, 300);
        assert_eq!(report.function_summaries[0].check_count, 1);

        assert_eq!(report.function_summaries[1].function, "g");
        assert_eq!(report.function_summaries[1].invocations, 1);
        assert_eq!(report.function_summaries[1].failures, 0);
    }

    #[test]
    fn test_function_summary_distinct_checks() {
        let mut reporter = RuntimeReporter::new();

        let check1 = make_check("f", CheckKind::IndexOutOfBounds, 10);
        let check2 = make_check("f", CheckKind::DivisionByZero, 20);

        reporter.record(passed_result(check1.clone(), 100));
        reporter.record(passed_result(check1, 100));
        reporter.record(passed_result(check2, 100));

        let report = reporter.report();
        assert_eq!(report.function_summaries.len(), 1);
        assert_eq!(report.function_summaries[0].check_count, 2);
        assert_eq!(report.function_summaries[0].invocations, 3);
    }

    // -----------------------------------------------------------------------
    // Hot path analysis
    // -----------------------------------------------------------------------

    #[test]
    fn test_hot_path_high_invocation_count() {
        let mut reporter = RuntimeReporter::new().with_invocation_threshold(10);

        let check = make_check("f", CheckKind::IndexOutOfBounds, 10);
        for _ in 0..15 {
            reporter.record(passed_result(check.clone(), 10));
        }

        let report = reporter.report();
        assert_eq!(report.hot_paths.len(), 1);
        assert!(matches!(
            report.hot_paths[0].reason,
            HotPathReason::HighInvocationCount { count: 15, threshold: 10 }
        ));
    }

    #[test]
    fn test_hot_path_high_total_time() {
        let mut reporter = RuntimeReporter::new()
            .with_invocation_threshold(1000)
            .with_time_threshold_ns(100);

        let check = make_check("f", CheckKind::IndexOutOfBounds, 10);
        // 5 invocations with 50ns each = 250ns total, above 100ns threshold
        for _ in 0..5 {
            reporter.record(passed_result(check.clone(), 50));
        }

        let report = reporter.report();
        assert_eq!(report.hot_paths.len(), 1);
        assert!(matches!(
            report.hot_paths[0].reason,
            HotPathReason::HighTotalTime { .. }
        ));
    }

    #[test]
    fn test_hot_path_high_per_invocation_cost() {
        let mut reporter = RuntimeReporter::new()
            .with_invocation_threshold(1000)
            .with_time_threshold_ns(1_000_000)
            .with_avg_threshold_ns(100);

        let check = make_check("f", CheckKind::IndexOutOfBounds, 10);
        // 2 invocations with 500ns each = avg 500ns, above 100ns threshold
        reporter.record(passed_result(check.clone(), 500));
        reporter.record(passed_result(check, 500));

        let report = reporter.report();
        assert_eq!(report.hot_paths.len(), 1);
        assert!(matches!(
            report.hot_paths[0].reason,
            HotPathReason::HighPerInvocationCost { .. }
        ));
    }

    #[test]
    fn test_hot_path_no_hot_paths() {
        let mut reporter = RuntimeReporter::new()
            .with_invocation_threshold(1000)
            .with_time_threshold_ns(1_000_000)
            .with_avg_threshold_ns(100_000);

        let check = make_check("f", CheckKind::IndexOutOfBounds, 10);
        reporter.record(passed_result(check, 10));

        let report = reporter.report();
        assert!(report.hot_paths.is_empty());
    }

    #[test]
    fn test_hot_path_sorted_by_total_time() {
        let mut reporter = RuntimeReporter::new().with_invocation_threshold(2);

        let check1 = make_check("fast_fn", CheckKind::IndexOutOfBounds, 10);
        let check2 = make_check("slow_fn", CheckKind::DivisionByZero, 20);

        for _ in 0..5 {
            reporter.record(passed_result(check1.clone(), 10));
        }
        for _ in 0..5 {
            reporter.record(passed_result(check2.clone(), 100));
        }

        let report = reporter.report();
        assert_eq!(report.hot_paths.len(), 2);
        // slow_fn should be first (higher total time)
        assert_eq!(report.hot_paths[0].check.function, "slow_fn");
        assert_eq!(report.hot_paths[1].check.function, "fast_fn");
    }

    // -----------------------------------------------------------------------
    // is_likely_hot_path
    // -----------------------------------------------------------------------

    #[test]
    fn test_is_likely_hot_path_zero_cost_never_hot() {
        assert!(!is_likely_hot_path(CheckOverhead::ZeroCost, 1_000_000));
    }

    #[test]
    fn test_is_likely_hot_path_lightweight() {
        assert!(!is_likely_hot_path(CheckOverhead::Lightweight, 5_000));
        assert!(is_likely_hot_path(CheckOverhead::Lightweight, 50_000));
    }

    #[test]
    fn test_is_likely_hot_path_expensive() {
        assert!(!is_likely_hot_path(CheckOverhead::Expensive, 50));
        assert!(is_likely_hot_path(CheckOverhead::Expensive, 500));
    }

    // -----------------------------------------------------------------------
    // Serialization
    // -----------------------------------------------------------------------

    #[test]
    fn test_report_serialization_roundtrip() {
        let mut reporter = RuntimeReporter::new();
        let check = make_check("f", CheckKind::IndexOutOfBounds, 10);
        reporter.record(passed_result(check, 100));

        let report = reporter.report();
        let json = serde_json::to_string(&report).expect("serialize");
        let roundtrip: RuntimeReport = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(roundtrip.total_invocations, 1);
        assert_eq!(roundtrip.passed, 1);
    }

    #[test]
    fn test_check_outcome_serialization() {
        let outcomes = vec![
            CheckOutcome::Passed,
            CheckOutcome::Failed { message: "oops".to_string() },
            CheckOutcome::Skipped,
        ];

        for outcome in &outcomes {
            let json = serde_json::to_string(outcome).expect("serialize");
            let roundtrip: CheckOutcome = serde_json::from_str(&json).expect("deserialize");
            assert_eq!(&roundtrip, outcome);
        }
    }
}
