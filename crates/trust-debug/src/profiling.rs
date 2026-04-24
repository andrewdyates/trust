// trust-debug/profiling.rs: Function-level profiling for tRust compilation hot paths
//
// Provides a `ProfileScope` RAII guard that records start time and logs duration
// on drop, a global profiler controlled by `TRUST_PROFILE=1` env var, and a
// `ProfilingReport` that collects all timings and outputs a sorted top-10 summary.
//
// Part of #906: Profile tRust compiler: identify top 10 hot paths in compilation
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::fmt;
use std::sync::{Mutex, OnceLock};
use std::time::{Duration, Instant};

// ---------------------------------------------------------------------------
// Global profiler singleton
// ---------------------------------------------------------------------------

static GLOBAL_PROFILER: OnceLock<Mutex<Profiler>> = OnceLock::new();

/// Returns whether profiling is enabled via `TRUST_PROFILE=1`.
#[must_use]
pub fn is_profiling_enabled() -> bool {
    std::env::var("TRUST_PROFILE").is_ok_and(|v| v == "1")
}

/// Returns a reference to the global profiler, initializing on first call.
/// Returns `None` if profiling is disabled.
fn global_profiler() -> Option<&'static Mutex<Profiler>> {
    if !is_profiling_enabled() {
        return None;
    }
    Some(GLOBAL_PROFILER.get_or_init(|| Mutex::new(Profiler::new())))
}

/// Record a completed timing entry into the global profiler.
fn record_global(entry: TimingEntry) {
    if let Some(profiler) = global_profiler()
        && let Ok(mut p) = profiler.lock()
    {
        p.record(entry);
    }
}

/// Finalize the global profiler and return the profiling report.
/// Returns `None` if profiling is disabled or no entries were recorded.
#[must_use]
pub fn finalize_global_report() -> Option<ProfilingReport> {
    let profiler = global_profiler()?;
    let p = profiler.lock().ok()?;
    let report = p.report();
    if report.entries.is_empty() {
        return None;
    }
    Some(report)
}

/// Reset the global profiler (useful between test runs or pipeline invocations).
pub fn reset_global_profiler() {
    if let Some(profiler) = global_profiler()
        && let Ok(mut p) = profiler.lock()
    {
        p.entries.clear();
    }
}

/// Print the top-10 hot paths summary to stderr if profiling is enabled.
///
/// Call this at the end of compilation. If `TRUST_PROFILE=1` is not set or no
/// entries were recorded, this is a no-op.
pub fn print_profile_report() {
    if let Some(report) = finalize_global_report() {
        eprintln!("{report}");
    }
}

// ---------------------------------------------------------------------------
// TimingEntry
// ---------------------------------------------------------------------------

/// A single recorded timing for a named scope.
#[derive(Debug, Clone)]
pub struct TimingEntry {
    /// Name of the profiled scope (e.g., "vcgen::generate_vcs", "router::verify_all").
    pub name: String,
    /// Wall-clock duration of the scope.
    pub duration: Duration,
    /// Optional category for classification (e.g., "trust", "upstream", "llvm").
    pub category: Category,
}

/// Classification of a hot path for the profiling report.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Category {
    /// tRust verification pipeline code.
    Trust,
    /// Upstream rustc code.
    Upstream,
    /// LLVM backend code.
    Llvm,
    /// Unknown or unclassified.
    Unknown,
}

impl fmt::Display for Category {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Trust => write!(f, "trust"),
            Self::Upstream => write!(f, "upstream"),
            Self::Llvm => write!(f, "llvm"),
            Self::Unknown => write!(f, "unknown"),
        }
    }
}

// ---------------------------------------------------------------------------
// ProfileScope — RAII guard
// ---------------------------------------------------------------------------

/// RAII guard that records wall-clock time from creation to drop.
///
/// When dropped, the elapsed duration is recorded into the global profiler
/// (if profiling is enabled). If profiling is disabled, this is a no-op.
///
/// # Usage
///
/// ```rust,no_run
/// use trust_debug::profiling::{ProfileScope, Category};
///
/// fn expensive_function() {
///     let _guard = ProfileScope::new("expensive_function", Category::Trust);
///     // ... work happens here ...
///     // duration recorded automatically on drop
/// }
/// ```
pub struct ProfileScope {
    name: String,
    category: Category,
    start: Instant,
    enabled: bool,
}

impl ProfileScope {
    /// Create a new profiling scope. If `TRUST_PROFILE=1` is not set, this is
    /// essentially a no-op (timing is still captured but not recorded).
    #[must_use]
    pub fn new(name: &str, category: Category) -> Self {
        let enabled = is_profiling_enabled();
        Self { name: name.to_string(), category, start: Instant::now(), enabled }
    }

    /// Create a scope that records into a specific `Profiler` instance instead
    /// of the global one. Useful for testing.
    #[cfg(test)]
    #[must_use]
    pub(crate) fn with_profiler<'a>(
        name: &str,
        category: Category,
        profiler: &'a Mutex<Profiler>,
    ) -> ProfileScopeLocal<'a> {
        ProfileScopeLocal { name: name.to_string(), category, start: Instant::now(), profiler }
    }
}

impl Drop for ProfileScope {
    fn drop(&mut self) {
        if self.enabled {
            let duration = self.start.elapsed();
            record_global(TimingEntry {
                name: std::mem::take(&mut self.name),
                duration,
                category: self.category,
            });
        }
    }
}

/// A profiling scope that records into a specific `Profiler` instance.
#[cfg(test)]
pub(crate) struct ProfileScopeLocal<'a> {
    name: String,
    category: Category,
    start: Instant,
    profiler: &'a Mutex<Profiler>,
}

#[cfg(test)]
impl Drop for ProfileScopeLocal<'_> {
    fn drop(&mut self) {
        let duration = self.start.elapsed();
        if let Ok(mut p) = self.profiler.lock() {
            p.record(TimingEntry {
                name: std::mem::take(&mut self.name),
                duration,
                category: self.category,
            });
        }
    }
}

// ---------------------------------------------------------------------------
// Profiler — timing accumulator
// ---------------------------------------------------------------------------

/// Accumulator for profiling entries. Thread-safe via external `Mutex`.
#[derive(Debug)]
pub(crate) struct Profiler {
    entries: Vec<TimingEntry>,
}

impl Profiler {
    pub(crate) fn new() -> Self {
        Self { entries: Vec::new() }
    }

    pub(crate) fn record(&mut self, entry: TimingEntry) {
        self.entries.push(entry);
    }

    /// Build the aggregate report from all recorded entries.
    pub(crate) fn report(&self) -> ProfilingReport {
        ProfilingReport::from_entries(&self.entries)
    }
}

// ---------------------------------------------------------------------------
// HotPath — a single aggregated hot path entry
// ---------------------------------------------------------------------------

/// An aggregated hot path in the profiling report.
#[derive(Debug, Clone)]
pub struct HotPath {
    /// Name of the function/scope.
    pub name: String,
    /// Total wall-clock time across all invocations.
    pub total_duration: Duration,
    /// Number of invocations.
    pub call_count: usize,
    /// Average duration per call.
    pub avg_duration: Duration,
    /// Maximum single-call duration.
    pub max_duration: Duration,
    /// Percentage of total profiled time.
    pub pct_of_total: f64,
    /// Classification.
    pub category: Category,
}

// ---------------------------------------------------------------------------
// ProfilingReport
// ---------------------------------------------------------------------------

/// Aggregated profiling report with top-N hot paths.
#[derive(Debug, Clone)]
pub struct ProfilingReport {
    /// All aggregated entries, sorted by total duration (descending).
    pub entries: Vec<HotPath>,
    /// Total wall-clock time across all recorded scopes.
    pub total_time: Duration,
    /// Total number of individual timing recordings.
    pub total_recordings: usize,
}

impl ProfilingReport {
    /// Build from raw timing entries, aggregating by name.
    fn from_entries(entries: &[TimingEntry]) -> Self {
        use std::collections::BTreeMap;

        let total_time: Duration = entries.iter().map(|e| e.duration).sum();
        let total_recordings = entries.len();
        let total_secs = total_time.as_secs_f64();

        // Aggregate by name
        let mut agg: BTreeMap<String, (Duration, usize, Duration, Category)> = BTreeMap::new();
        for entry in entries {
            let (total, count, max, _cat) = agg.entry(entry.name.clone()).or_insert((
                Duration::ZERO,
                0,
                Duration::ZERO,
                entry.category,
            ));
            *total += entry.duration;
            *count += 1;
            if entry.duration > *max {
                *max = entry.duration;
            }
        }

        let mut hot_paths: Vec<HotPath> = agg
            .into_iter()
            .map(|(name, (total_duration, call_count, max_duration, category))| {
                let avg_duration = if call_count > 0 {
                    total_duration / call_count as u32
                } else {
                    Duration::ZERO
                };
                let pct_of_total = if total_secs > 0.0 {
                    (total_duration.as_secs_f64() / total_secs) * 100.0
                } else {
                    0.0
                };
                HotPath {
                    name,
                    total_duration,
                    call_count,
                    avg_duration,
                    max_duration,
                    pct_of_total,
                    category,
                }
            })
            .collect();

        // Sort by total duration descending
        hot_paths.sort_by_key(|b| std::cmp::Reverse(b.total_duration));

        Self { entries: hot_paths, total_time, total_recordings }
    }

    /// Return only the top N hot paths.
    #[must_use]
    pub fn top_n(&self, n: usize) -> Vec<&HotPath> {
        self.entries.iter().take(n).collect()
    }

    /// Format the top-10 hot paths as a human-readable table.
    #[must_use]
    pub fn top_10_summary(&self) -> String {
        let mut out = String::new();
        out.push_str("=== tRust Compilation Hot Paths (Top 10) ===\n");
        out.push_str(&format!(
            "Total profiled time: {:.3}ms ({} recordings)\n\n",
            self.total_time.as_secs_f64() * 1000.0,
            self.total_recordings,
        ));
        out.push_str(&format!(
            "{:<4} {:<40} {:>10} {:>8} {:>10} {:>10} {:>8}\n",
            "Rank", "Function", "Total(ms)", "% Time", "Calls", "Avg(ms)", "Category"
        ));
        out.push_str(&"-".repeat(92));
        out.push('\n');

        for (i, hp) in self.entries.iter().take(10).enumerate() {
            out.push_str(&format!(
                "{:<4} {:<40} {:>10.3} {:>7.1}% {:>10} {:>10.3} {:>8}\n",
                i + 1,
                truncate_name(&hp.name, 40),
                hp.total_duration.as_secs_f64() * 1000.0,
                hp.pct_of_total,
                hp.call_count,
                hp.avg_duration.as_secs_f64() * 1000.0,
                hp.category,
            ));
        }

        out
    }
}

impl fmt::Display for ProfilingReport {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.top_10_summary())
    }
}

/// Truncate a name to fit within `max_len`, adding "..." if truncated.
fn truncate_name(name: &str, max_len: usize) -> String {
    if name.len() <= max_len {
        name.to_string()
    } else if max_len > 3 {
        format!("{}...", &name[..max_len - 3])
    } else {
        name[..max_len].to_string()
    }
}

// ---------------------------------------------------------------------------
// Convenience profiling scope constructors for pipeline stages
// ---------------------------------------------------------------------------

/// Create a profiling scope for VC generation.
///
/// Records the wall-clock time of the scope under the name
/// `"vcgen::<detail>"` with category `Trust`.
#[must_use]
pub fn scope_vcgen(detail: &str) -> ProfileScope {
    ProfileScope::new(&format!("vcgen::{detail}"), Category::Trust)
}

/// Create a profiling scope for solver dispatch / routing.
///
/// Records the wall-clock time of the scope under the name
/// `"router::<detail>"` with category `Trust`.
#[must_use]
pub fn scope_router(detail: &str) -> ProfileScope {
    ProfileScope::new(&format!("router::{detail}"), Category::Trust)
}

/// Create a profiling scope for the strengthen (spec inference) phase.
///
/// Records the wall-clock time of the scope under the name
/// `"strengthen::<detail>"` with category `Trust`.
#[must_use]
pub fn scope_strengthen(detail: &str) -> ProfileScope {
    ProfileScope::new(&format!("strengthen::{detail}"), Category::Trust)
}

/// Create a profiling scope for the convergence (fixed-point detection) phase.
///
/// Records the wall-clock time of the scope under the name
/// `"convergence::<detail>"` with category `Trust`.
#[must_use]
pub fn scope_convergence(detail: &str) -> ProfileScope {
    ProfileScope::new(&format!("convergence::{detail}"), Category::Trust)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Mutex;

    #[test]
    fn test_profiler_records_entries() {
        let profiler = Mutex::new(Profiler::new());

        {
            let _scope = ProfileScope::with_profiler("test::func_a", Category::Trust, &profiler);
            std::thread::sleep(Duration::from_millis(5));
        }
        {
            let _scope = ProfileScope::with_profiler("test::func_b", Category::Upstream, &profiler);
            std::thread::sleep(Duration::from_millis(10));
        }

        let report = profiler.lock().expect("lock").report();
        assert_eq!(report.entries.len(), 2);
        assert_eq!(report.total_recordings, 2);
        // func_b should be first (longer duration)
        assert_eq!(report.entries[0].name, "test::func_b");
        assert_eq!(report.entries[1].name, "test::func_a");
    }

    #[test]
    fn test_profiler_aggregates_same_name() {
        let profiler = Mutex::new(Profiler::new());

        for _ in 0..5 {
            let _scope = ProfileScope::with_profiler("test::repeated", Category::Trust, &profiler);
            std::thread::sleep(Duration::from_millis(2));
        }

        let report = profiler.lock().expect("lock").report();
        assert_eq!(report.entries.len(), 1);
        assert_eq!(report.entries[0].call_count, 5);
        assert_eq!(report.entries[0].name, "test::repeated");
        assert!(report.entries[0].total_duration >= Duration::from_millis(8));
    }

    #[test]
    fn test_hot_path_percentage() {
        let entries = vec![
            TimingEntry {
                name: "fast".to_string(),
                duration: Duration::from_millis(100),
                category: Category::Trust,
            },
            TimingEntry {
                name: "slow".to_string(),
                duration: Duration::from_millis(900),
                category: Category::Upstream,
            },
        ];

        let report = ProfilingReport::from_entries(&entries);
        assert_eq!(report.entries.len(), 2);
        // slow should be first
        assert_eq!(report.entries[0].name, "slow");
        assert!((report.entries[0].pct_of_total - 90.0).abs() < 1.0);
        assert_eq!(report.entries[1].name, "fast");
        assert!((report.entries[1].pct_of_total - 10.0).abs() < 1.0);
    }

    #[test]
    fn test_top_n() {
        let entries: Vec<TimingEntry> = (0..20)
            .map(|i| TimingEntry {
                name: format!("func_{i}"),
                duration: Duration::from_millis(i * 10),
                category: Category::Trust,
            })
            .collect();

        let report = ProfilingReport::from_entries(&entries);
        let top5 = report.top_n(5);
        assert_eq!(top5.len(), 5);
        // Should be sorted by total duration descending
        assert_eq!(top5[0].name, "func_19");
        assert_eq!(top5[4].name, "func_15");
    }

    #[test]
    fn test_top_10_summary_format() {
        let entries = vec![
            TimingEntry {
                name: "vcgen::generate_vcs".to_string(),
                duration: Duration::from_millis(500),
                category: Category::Trust,
            },
            TimingEntry {
                name: "router::verify_all".to_string(),
                duration: Duration::from_millis(300),
                category: Category::Trust,
            },
            TimingEntry {
                name: "mir_extract::convert".to_string(),
                duration: Duration::from_millis(200),
                category: Category::Trust,
            },
        ];

        let report = ProfilingReport::from_entries(&entries);
        let summary = report.top_10_summary();
        assert!(summary.contains("tRust Compilation Hot Paths"));
        assert!(summary.contains("vcgen::generate_vcs"));
        assert!(summary.contains("router::verify_all"));
        assert!(summary.contains("mir_extract::convert"));
        assert!(summary.contains("trust"));
    }

    #[test]
    fn test_category_display() {
        assert_eq!(Category::Trust.to_string(), "trust");
        assert_eq!(Category::Upstream.to_string(), "upstream");
        assert_eq!(Category::Llvm.to_string(), "llvm");
        assert_eq!(Category::Unknown.to_string(), "unknown");
    }

    #[test]
    fn test_truncate_name() {
        assert_eq!(truncate_name("short", 40), "short");
        assert_eq!(
            truncate_name("this_is_a_very_long_function_name_that_exceeds_limit", 20),
            "this_is_a_very_lo..."
        );
    }

    #[test]
    fn test_empty_report() {
        let report = ProfilingReport::from_entries(&[]);
        assert!(report.entries.is_empty());
        assert_eq!(report.total_time, Duration::ZERO);
        assert_eq!(report.total_recordings, 0);
    }

    #[test]
    fn test_max_duration_tracking() {
        let entries = vec![
            TimingEntry {
                name: "func".to_string(),
                duration: Duration::from_millis(10),
                category: Category::Trust,
            },
            TimingEntry {
                name: "func".to_string(),
                duration: Duration::from_millis(100),
                category: Category::Trust,
            },
            TimingEntry {
                name: "func".to_string(),
                duration: Duration::from_millis(50),
                category: Category::Trust,
            },
        ];

        let report = ProfilingReport::from_entries(&entries);
        assert_eq!(report.entries.len(), 1);
        assert_eq!(report.entries[0].max_duration, Duration::from_millis(100));
        assert_eq!(report.entries[0].call_count, 3);
    }

    #[test]
    fn test_profile_scope_disabled_is_noop() {
        // When TRUST_PROFILE is not set to "1", ProfileScope should not record
        let scope = ProfileScope::new("should_not_record", Category::Trust);
        assert!(!scope.enabled || std::env::var("TRUST_PROFILE").map_or(false, |v| v == "1"));
    }

    #[test]
    fn test_profiling_report_display() {
        let entries = vec![TimingEntry {
            name: "test_func".to_string(),
            duration: Duration::from_millis(42),
            category: Category::Trust,
        }];

        let report = ProfilingReport::from_entries(&entries);
        let display = format!("{report}");
        assert!(display.contains("test_func"));
        assert!(display.contains("42.0"));
    }

    // -- Integration tests for profiling output format (#906) --

    #[test]
    fn test_top_10_summary_format_has_header_and_columns() {
        let entries = vec![
            TimingEntry {
                name: "vcgen::generate_vcs".to_string(),
                duration: Duration::from_millis(500),
                category: Category::Trust,
            },
            TimingEntry {
                name: "router::verify_all".to_string(),
                duration: Duration::from_millis(300),
                category: Category::Trust,
            },
            TimingEntry {
                name: "strengthen::run".to_string(),
                duration: Duration::from_millis(150),
                category: Category::Trust,
            },
            TimingEntry {
                name: "convergence::observe".to_string(),
                duration: Duration::from_millis(30),
                category: Category::Trust,
            },
            TimingEntry {
                name: "debug::analyze".to_string(),
                duration: Duration::from_millis(20),
                category: Category::Trust,
            },
        ];

        let report = ProfilingReport::from_entries(&entries);
        let summary = report.top_10_summary();

        // Header
        assert!(summary.contains("tRust Compilation Hot Paths (Top 10)"));
        assert!(summary.contains("Total profiled time:"));
        assert!(summary.contains("recordings"));

        // Column headers
        assert!(summary.contains("Rank"));
        assert!(summary.contains("Function"));
        assert!(summary.contains("Total(ms)"));
        assert!(summary.contains("% Time"));
        assert!(summary.contains("Calls"));
        assert!(summary.contains("Avg(ms)"));
        assert!(summary.contains("Category"));

        // All entries present
        assert!(summary.contains("vcgen::generate_vcs"));
        assert!(summary.contains("router::verify_all"));
        assert!(summary.contains("strengthen::run"));
        assert!(summary.contains("convergence::observe"));
        assert!(summary.contains("debug::analyze"));

        // Category labels
        assert!(summary.contains("trust"));

        // Rank numbers (1-5)
        assert!(summary.contains("1   "));
        assert!(summary.contains("5   "));
    }

    #[test]
    fn test_top_10_summary_respects_10_limit() {
        let entries: Vec<TimingEntry> = (0..15)
            .map(|i| TimingEntry {
                name: format!("func_{i}"),
                duration: Duration::from_millis((15 - i) * 10),
                category: Category::Trust,
            })
            .collect();

        let report = ProfilingReport::from_entries(&entries);
        let summary = report.top_10_summary();

        // First 10 should be present
        for i in 0..10 {
            assert!(summary.contains(&format!("func_{i}")));
        }
        // 11th-15th should NOT be present
        for i in 10..15 {
            assert!(!summary.contains(&format!("func_{i}")));
        }
    }

    #[test]
    fn test_scope_convenience_constructors() {
        let profiler = Mutex::new(Profiler::new());

        {
            let _s = ProfileScope::with_profiler("vcgen::generate_vcs", Category::Trust, &profiler);
            std::thread::sleep(Duration::from_millis(1));
        }
        {
            let _s = ProfileScope::with_profiler("router::verify_all", Category::Trust, &profiler);
            std::thread::sleep(Duration::from_millis(1));
        }
        {
            let _s = ProfileScope::with_profiler("strengthen::run", Category::Trust, &profiler);
            std::thread::sleep(Duration::from_millis(1));
        }
        {
            let _s =
                ProfileScope::with_profiler("convergence::observe", Category::Trust, &profiler);
            std::thread::sleep(Duration::from_millis(1));
        }

        let report = profiler.lock().expect("lock").report();
        assert_eq!(report.entries.len(), 4);
        assert_eq!(report.total_recordings, 4);

        // All pipeline stage names recorded
        let names: Vec<&str> = report.entries.iter().map(|e| e.name.as_str()).collect();
        assert!(names.contains(&"vcgen::generate_vcs"));
        assert!(names.contains(&"router::verify_all"));
        assert!(names.contains(&"strengthen::run"));
        assert!(names.contains(&"convergence::observe"));
    }

    #[test]
    fn test_profiling_report_percentage_sums_to_100() {
        let entries = vec![
            TimingEntry {
                name: "a".to_string(),
                duration: Duration::from_millis(250),
                category: Category::Trust,
            },
            TimingEntry {
                name: "b".to_string(),
                duration: Duration::from_millis(250),
                category: Category::Trust,
            },
            TimingEntry {
                name: "c".to_string(),
                duration: Duration::from_millis(500),
                category: Category::Trust,
            },
        ];

        let report = ProfilingReport::from_entries(&entries);
        let total_pct: f64 = report.entries.iter().map(|e| e.pct_of_total).sum();
        assert!((total_pct - 100.0).abs() < 0.01);
    }

    #[test]
    fn test_profiling_report_sorted_descending_by_duration() {
        let entries = vec![
            TimingEntry {
                name: "fast".to_string(),
                duration: Duration::from_millis(10),
                category: Category::Trust,
            },
            TimingEntry {
                name: "medium".to_string(),
                duration: Duration::from_millis(50),
                category: Category::Trust,
            },
            TimingEntry {
                name: "slow".to_string(),
                duration: Duration::from_millis(200),
                category: Category::Trust,
            },
        ];

        let report = ProfilingReport::from_entries(&entries);
        assert_eq!(report.entries[0].name, "slow");
        assert_eq!(report.entries[1].name, "medium");
        assert_eq!(report.entries[2].name, "fast");
    }

    #[test]
    fn test_print_profile_report_does_not_panic_when_disabled() {
        // When TRUST_PROFILE is not "1", print_profile_report should be a silent no-op
        print_profile_report();
    }

    #[test]
    fn test_mixed_categories_in_report() {
        let entries = vec![
            TimingEntry {
                name: "vcgen::generate".to_string(),
                duration: Duration::from_millis(100),
                category: Category::Trust,
            },
            TimingEntry {
                name: "rustc::codegen".to_string(),
                duration: Duration::from_millis(200),
                category: Category::Upstream,
            },
            TimingEntry {
                name: "llvm::optimize".to_string(),
                duration: Duration::from_millis(300),
                category: Category::Llvm,
            },
        ];

        let report = ProfilingReport::from_entries(&entries);
        let summary = report.top_10_summary();

        assert!(summary.contains("trust"));
        assert!(summary.contains("upstream"));
        assert!(summary.contains("llvm"));
    }
}
