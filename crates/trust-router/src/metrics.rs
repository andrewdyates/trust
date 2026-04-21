// trust-router/metrics.rs: Router metrics collection and reporting
//
// tRust: Tracks dispatch counts, per-solver statistics, cache hit rates,
// and latency distributions. Provides terminal and JSON report formats.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;
use std::fmt;
use std::time::Duration;

/// tRust: Trait for extensible metric collection.
///
/// Implement this trait to plug custom metric backends (e.g., Prometheus,
/// StatsD) into the router without modifying dispatch logic.
pub trait MetricsCollector: Send + Sync {
    /// Record that a VC was dispatched to a solver.
    fn record_dispatch(&self, solver: &str, duration: Duration, success: bool);

    /// Record a cache hit (VC result was served from cache).
    fn record_cache_hit(&self, solver: &str);

    /// Record a cache miss (VC was dispatched to a solver).
    fn record_cache_miss(&self, solver: &str);

    /// Get a snapshot of current metrics as a displayable string.
    fn summary(&self) -> String;
}

/// tRust: Latency histogram with configurable buckets.
///
/// Bucket-based (not exact) for memory efficiency. Each bucket counts
/// the number of observations that fall into its range.
#[derive(Debug, Clone)]
pub struct LatencyHistogram {
    /// Upper bounds of each bucket in milliseconds.
    bucket_bounds_ms: Vec<f64>,
    /// Count of observations in each bucket (len = bucket_bounds + 1 for overflow).
    counts: Vec<u64>,
    /// Total number of observations.
    total_count: u64,
    /// Sum of all observed latencies in ms (for computing mean).
    total_sum_ms: f64,
    /// Minimum observed latency in ms.
    min_ms: f64,
    /// Maximum observed latency in ms.
    max_ms: f64,
}

impl LatencyHistogram {
    /// Create a histogram with default buckets: 1, 5, 10, 25, 50, 100, 250, 500, 1000, 5000 ms.
    #[must_use]
    pub fn new() -> Self {
        Self::with_buckets(vec![1.0, 5.0, 10.0, 25.0, 50.0, 100.0, 250.0, 500.0, 1000.0, 5000.0])
    }

    /// Create a histogram with custom bucket upper bounds (in milliseconds).
    ///
    /// Bounds must be sorted ascending. An overflow bucket is added automatically.
    #[must_use]
    pub fn with_buckets(mut bounds: Vec<f64>) -> Self {
        bounds.sort_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));
        let bucket_count = bounds.len() + 1; // +1 for overflow
        Self {
            bucket_bounds_ms: bounds,
            counts: vec![0; bucket_count],
            total_count: 0,
            total_sum_ms: 0.0,
            min_ms: f64::INFINITY,
            max_ms: f64::NEG_INFINITY,
        }
    }

    /// Record a latency observation.
    pub fn observe(&mut self, duration: Duration) {
        let ms = duration.as_secs_f64() * 1000.0;
        self.observe_ms(ms);
    }

    /// Record a latency observation in milliseconds.
    pub fn observe_ms(&mut self, ms: f64) {
        self.total_count += 1;
        self.total_sum_ms += ms;

        if ms < self.min_ms {
            self.min_ms = ms;
        }
        if ms > self.max_ms {
            self.max_ms = ms;
        }

        // Find the first bucket whose upper bound >= ms
        let mut placed = false;
        for (i, &bound) in self.bucket_bounds_ms.iter().enumerate() {
            if ms <= bound {
                self.counts[i] += 1;
                placed = true;
                break;
            }
        }
        if !placed {
            // Overflow bucket
            *self.counts.last_mut().expect("counts always has overflow bucket") += 1;
        }
    }

    /// Total number of observations.
    #[must_use]
    pub fn count(&self) -> u64 {
        self.total_count
    }

    /// Mean latency in milliseconds. Returns 0.0 if no observations.
    #[must_use]
    pub fn mean_ms(&self) -> f64 {
        if self.total_count == 0 {
            0.0
        } else {
            self.total_sum_ms / self.total_count as f64
        }
    }

    /// Minimum observed latency in ms. Returns 0.0 if no observations.
    #[must_use]
    pub fn min_ms(&self) -> f64 {
        if self.total_count == 0 {
            0.0
        } else {
            self.min_ms
        }
    }

    /// Maximum observed latency in ms. Returns 0.0 if no observations.
    #[must_use]
    pub fn max_ms(&self) -> f64 {
        if self.total_count == 0 {
            0.0
        } else {
            self.max_ms
        }
    }

    /// Get bucket counts as (upper_bound_ms, count) pairs. The last entry
    /// has `f64::INFINITY` as its bound (overflow bucket).
    #[must_use]
    pub fn buckets(&self) -> Vec<(f64, u64)> {
        let mut result: Vec<(f64, u64)> = self
            .bucket_bounds_ms
            .iter()
            .zip(self.counts.iter())
            .map(|(&bound, &count)| (bound, count))
            .collect();
        // Overflow bucket
        result.push((f64::INFINITY, self.counts[self.bucket_bounds_ms.len()]));
        result
    }
}

impl Default for LatencyHistogram {
    fn default() -> Self {
        Self::new()
    }
}

/// tRust: Per-solver metrics.
#[derive(Debug, Clone)]
pub struct SolverMetrics {
    /// Number of VCs dispatched to this solver.
    pub dispatched: u64,
    /// Number of successful verifications (Proved or Failed with result).
    pub successes: u64,
    /// Number of errors or timeouts.
    pub errors: u64,
    /// Cache hits for this solver.
    pub cache_hits: u64,
    /// Cache misses for this solver.
    pub cache_misses: u64,
    /// Latency distribution.
    pub latency: LatencyHistogram,
}

impl SolverMetrics {
    fn new() -> Self {
        Self {
            dispatched: 0,
            successes: 0,
            errors: 0,
            cache_hits: 0,
            cache_misses: 0,
            latency: LatencyHistogram::new(),
        }
    }

    /// Success rate as a fraction [0.0, 1.0].
    #[must_use]
    pub fn success_rate(&self) -> f64 {
        if self.dispatched == 0 {
            0.0
        } else {
            self.successes as f64 / self.dispatched as f64
        }
    }

    /// Cache hit rate as a fraction [0.0, 1.0].
    #[must_use]
    pub fn cache_hit_rate(&self) -> f64 {
        let total = self.cache_hits + self.cache_misses;
        if total == 0 {
            0.0
        } else {
            self.cache_hits as f64 / total as f64
        }
    }
}

/// tRust: Aggregated router metrics across all solvers.
pub struct RouterMetrics {
    /// Per-solver metrics.
    solvers: FxHashMap<String, SolverMetrics>,
    /// Total VCs dispatched.
    total_dispatched: u64,
    /// Total cache hits across all solvers.
    total_cache_hits: u64,
    /// Total cache misses across all solvers.
    total_cache_misses: u64,
}

impl RouterMetrics {
    /// Create empty metrics.
    #[must_use]
    pub fn new() -> Self {
        Self {
            solvers: FxHashMap::default(),
            total_dispatched: 0,
            total_cache_hits: 0,
            total_cache_misses: 0,
        }
    }

    /// Record a dispatch to a solver.
    pub fn record_dispatch(&mut self, solver: &str, duration: Duration, success: bool) {
        self.total_dispatched += 1;
        let entry = self.solvers.entry(solver.to_string()).or_insert_with(SolverMetrics::new);
        entry.dispatched += 1;
        entry.latency.observe(duration);
        if success {
            entry.successes += 1;
        } else {
            entry.errors += 1;
        }
    }

    /// Record a cache hit for a solver.
    pub fn record_cache_hit(&mut self, solver: &str) {
        self.total_cache_hits += 1;
        let entry = self.solvers.entry(solver.to_string()).or_insert_with(SolverMetrics::new);
        entry.cache_hits += 1;
    }

    /// Record a cache miss for a solver.
    pub fn record_cache_miss(&mut self, solver: &str) {
        self.total_cache_misses += 1;
        let entry = self.solvers.entry(solver.to_string()).or_insert_with(SolverMetrics::new);
        entry.cache_misses += 1;
    }

    /// Total VCs dispatched across all solvers.
    #[must_use]
    pub fn total_dispatched(&self) -> u64 {
        self.total_dispatched
    }

    /// Overall cache hit rate.
    #[must_use]
    pub fn cache_hit_rate(&self) -> f64 {
        let total = self.total_cache_hits + self.total_cache_misses;
        if total == 0 {
            0.0
        } else {
            self.total_cache_hits as f64 / total as f64
        }
    }

    /// Get metrics for a specific solver.
    #[must_use]
    pub fn solver_metrics(&self, solver: &str) -> Option<&SolverMetrics> {
        self.solvers.get(solver)
    }

    /// Per-solver dispatch counts as (name, count) pairs, sorted by count descending.
    #[must_use]
    pub fn per_solver_counts(&self) -> Vec<(String, u64)> {
        let mut counts: Vec<(String, u64)> = self
            .solvers
            .iter()
            .map(|(name, m)| (name.clone(), m.dispatched))
            .collect();
        counts.sort_by(|a, b| b.1.cmp(&a.1));
        counts
    }

    /// All tracked solver names.
    #[must_use]
    pub fn solver_names(&self) -> Vec<String> {
        self.solvers.keys().cloned().collect()
    }

    /// Generate a terminal-formatted summary report.
    #[must_use]
    pub fn terminal_report(&self) -> TerminalMetricsReport<'_> {
        TerminalMetricsReport { metrics: self }
    }

    /// Generate a JSON-formatted report.
    #[must_use]
    pub fn json_report(&self) -> JsonMetricsReport<'_> {
        JsonMetricsReport { metrics: self }
    }
}

impl Default for RouterMetrics {
    fn default() -> Self {
        Self::new()
    }
}

/// tRust: Terminal-formatted metrics summary for CLI output.
pub struct TerminalMetricsReport<'a> {
    metrics: &'a RouterMetrics,
}

impl<'a> fmt::Display for TerminalMetricsReport<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let m = self.metrics;

        writeln!(f, "=== Router Metrics ===")?;
        writeln!(f, "Total dispatched: {}", m.total_dispatched)?;
        writeln!(f, "Cache hit rate:   {:.1}%", m.cache_hit_rate() * 100.0)?;
        writeln!(f)?;

        let mut solvers: Vec<(&String, &SolverMetrics)> = m.solvers.iter().collect();
        solvers.sort_by(|a, b| b.1.dispatched.cmp(&a.1.dispatched));

        for (name, sm) in solvers {
            writeln!(f, "--- {} ---", name)?;
            writeln!(f, "  Dispatched:  {}", sm.dispatched)?;
            writeln!(f, "  Successes:   {}", sm.successes)?;
            writeln!(f, "  Errors:      {}", sm.errors)?;
            writeln!(f, "  Success rate: {:.1}%", sm.success_rate() * 100.0)?;
            writeln!(f, "  Cache hits:  {} / misses: {}", sm.cache_hits, sm.cache_misses)?;

            if sm.latency.count() > 0 {
                writeln!(
                    f,
                    "  Latency: mean={:.1}ms min={:.1}ms max={:.1}ms",
                    sm.latency.mean_ms(),
                    sm.latency.min_ms(),
                    sm.latency.max_ms(),
                )?;
            }
        }

        Ok(())
    }
}

/// tRust: JSON-formatted metrics report for dashboards and structured output.
pub struct JsonMetricsReport<'a> {
    metrics: &'a RouterMetrics,
}

impl<'a> fmt::Display for JsonMetricsReport<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let m = self.metrics;

        // Hand-rolled JSON to avoid serde dependency
        write!(f, "{{")?;
        write!(f, "\"total_dispatched\":{}", m.total_dispatched)?;
        write!(f, ",\"total_cache_hits\":{}", m.total_cache_hits)?;
        write!(f, ",\"total_cache_misses\":{}", m.total_cache_misses)?;
        write!(f, ",\"cache_hit_rate\":{:.4}", m.cache_hit_rate())?;
        write!(f, ",\"solvers\":{{")?;

        let mut solvers: Vec<(&String, &SolverMetrics)> = m.solvers.iter().collect();
        solvers.sort_by_key(|(name, _)| (*name).clone());

        for (i, (name, sm)) in solvers.iter().enumerate() {
            if i > 0 {
                write!(f, ",")?;
            }
            write!(f, "\"{}\":{{", name)?;
            write!(f, "\"dispatched\":{}", sm.dispatched)?;
            write!(f, ",\"successes\":{}", sm.successes)?;
            write!(f, ",\"errors\":{}", sm.errors)?;
            write!(f, ",\"success_rate\":{:.4}", sm.success_rate())?;
            write!(f, ",\"cache_hits\":{}", sm.cache_hits)?;
            write!(f, ",\"cache_misses\":{}", sm.cache_misses)?;
            write!(f, ",\"cache_hit_rate\":{:.4}", sm.cache_hit_rate())?;

            if sm.latency.count() > 0 {
                write!(f, ",\"latency\":{{\"count\":{}", sm.latency.count())?;
                write!(f, ",\"mean_ms\":{:.2}", sm.latency.mean_ms())?;
                write!(f, ",\"min_ms\":{:.2}", sm.latency.min_ms())?;
                write!(f, ",\"max_ms\":{:.2}", sm.latency.max_ms())?;

                // Bucket distribution
                write!(f, ",\"buckets\":[")?;
                for (j, (bound, count)) in sm.latency.buckets().iter().enumerate() {
                    if j > 0 {
                        write!(f, ",")?;
                    }
                    if bound.is_infinite() {
                        write!(f, "{{\"le\":\"+Inf\",\"count\":{}}}", count)?;
                    } else {
                        write!(f, "{{\"le\":{},\"count\":{}}}", bound, count)?;
                    }
                }
                write!(f, "]}}")?;
            }

            write!(f, "}}")?;
        }

        write!(f, "}}}}")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_latency_histogram_empty() {
        let hist = LatencyHistogram::new();
        assert_eq!(hist.count(), 0);
        assert_eq!(hist.mean_ms(), 0.0);
        assert_eq!(hist.min_ms(), 0.0);
        assert_eq!(hist.max_ms(), 0.0);
    }

    #[test]
    fn test_latency_histogram_single_observation() {
        let mut hist = LatencyHistogram::new();
        hist.observe(Duration::from_millis(42));

        assert_eq!(hist.count(), 1);
        assert!((hist.mean_ms() - 42.0).abs() < 0.1);
        assert!((hist.min_ms() - 42.0).abs() < 0.1);
        assert!((hist.max_ms() - 42.0).abs() < 0.1);
    }

    #[test]
    fn test_latency_histogram_multiple_observations() {
        let mut hist = LatencyHistogram::new();
        hist.observe(Duration::from_millis(10));
        hist.observe(Duration::from_millis(50));
        hist.observe(Duration::from_millis(200));

        assert_eq!(hist.count(), 3);
        // Mean should be ~86.67ms
        let mean = hist.mean_ms();
        assert!((mean - 86.67).abs() < 1.0);
        assert!((hist.min_ms() - 10.0).abs() < 0.1);
        assert!((hist.max_ms() - 200.0).abs() < 0.1);
    }

    #[test]
    fn test_latency_histogram_bucket_distribution() {
        let mut hist = LatencyHistogram::with_buckets(vec![10.0, 100.0, 1000.0]);

        hist.observe_ms(5.0); // bucket [0, 10]
        hist.observe_ms(50.0); // bucket (10, 100]
        hist.observe_ms(500.0); // bucket (100, 1000]
        hist.observe_ms(5000.0); // overflow bucket

        let buckets = hist.buckets();
        assert_eq!(buckets.len(), 4); // 3 bounds + 1 overflow
        assert_eq!(buckets[0], (10.0, 1));
        assert_eq!(buckets[1], (100.0, 1));
        assert_eq!(buckets[2], (1000.0, 1));
        assert_eq!(buckets[3].1, 1); // overflow
        assert!(buckets[3].0.is_infinite());
    }

    #[test]
    fn test_latency_histogram_observe_ms() {
        let mut hist = LatencyHistogram::new();
        hist.observe_ms(42.0);
        assert_eq!(hist.count(), 1);
        assert!((hist.mean_ms() - 42.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_solver_metrics_success_rate() {
        let mut sm = SolverMetrics::new();
        assert_eq!(sm.success_rate(), 0.0);

        sm.dispatched = 10;
        sm.successes = 7;
        sm.errors = 3;
        assert!((sm.success_rate() - 0.7).abs() < f64::EPSILON);
    }

    #[test]
    fn test_solver_metrics_cache_hit_rate() {
        let mut sm = SolverMetrics::new();
        assert_eq!(sm.cache_hit_rate(), 0.0);

        sm.cache_hits = 3;
        sm.cache_misses = 7;
        assert!((sm.cache_hit_rate() - 0.3).abs() < f64::EPSILON);
    }

    #[test]
    fn test_router_metrics_dispatch() {
        let mut metrics = RouterMetrics::new();
        metrics.record_dispatch("z4", Duration::from_millis(10), true);
        metrics.record_dispatch("z4", Duration::from_millis(20), false);
        metrics.record_dispatch("zani", Duration::from_millis(50), true);

        assert_eq!(metrics.total_dispatched(), 3);

        let z4 = metrics.solver_metrics("z4").unwrap();
        assert_eq!(z4.dispatched, 2);
        assert_eq!(z4.successes, 1);
        assert_eq!(z4.errors, 1);
        assert_eq!(z4.latency.count(), 2);

        let zani = metrics.solver_metrics("zani").unwrap();
        assert_eq!(zani.dispatched, 1);
        assert_eq!(zani.successes, 1);
    }

    #[test]
    fn test_router_metrics_cache() {
        let mut metrics = RouterMetrics::new();
        metrics.record_cache_hit("z4");
        metrics.record_cache_hit("z4");
        metrics.record_cache_miss("z4");
        metrics.record_cache_miss("zani");

        assert!((metrics.cache_hit_rate() - 0.5).abs() < f64::EPSILON);

        let z4 = metrics.solver_metrics("z4").unwrap();
        assert!((z4.cache_hit_rate() - 2.0 / 3.0).abs() < 0.01);
    }

    #[test]
    fn test_router_metrics_per_solver_counts() {
        let mut metrics = RouterMetrics::new();
        metrics.record_dispatch("z4", Duration::from_millis(10), true);
        metrics.record_dispatch("z4", Duration::from_millis(10), true);
        metrics.record_dispatch("zani", Duration::from_millis(10), true);

        let counts = metrics.per_solver_counts();
        assert_eq!(counts[0].0, "z4");
        assert_eq!(counts[0].1, 2);
        assert_eq!(counts[1].0, "zani");
        assert_eq!(counts[1].1, 1);
    }

    #[test]
    fn test_router_metrics_solver_names() {
        let mut metrics = RouterMetrics::new();
        metrics.record_dispatch("z4", Duration::from_millis(10), true);
        metrics.record_dispatch("zani", Duration::from_millis(10), true);

        let mut names = metrics.solver_names();
        names.sort();
        assert_eq!(names, vec!["z4", "zani"]);
    }

    #[test]
    fn test_terminal_report_format() {
        let mut metrics = RouterMetrics::new();
        metrics.record_dispatch("z4", Duration::from_millis(42), true);
        metrics.record_dispatch("z4", Duration::from_millis(100), false);
        metrics.record_cache_hit("z4");
        metrics.record_cache_miss("z4");

        let report = format!("{}", metrics.terminal_report());
        assert!(report.contains("Router Metrics"));
        assert!(report.contains("Total dispatched: 2"));
        assert!(report.contains("z4"));
        assert!(report.contains("Dispatched:  2"));
        assert!(report.contains("Successes:   1"));
        assert!(report.contains("Errors:      1"));
    }

    #[test]
    fn test_json_report_format() {
        let mut metrics = RouterMetrics::new();
        metrics.record_dispatch("z4", Duration::from_millis(10), true);
        metrics.record_cache_hit("z4");

        let report = format!("{}", metrics.json_report());
        assert!(report.contains("\"total_dispatched\":1"));
        assert!(report.contains("\"total_cache_hits\":1"));
        assert!(report.contains("\"z4\":{"));
        assert!(report.contains("\"dispatched\":1"));
        assert!(report.contains("\"successes\":1"));
        assert!(report.contains("\"latency\":{"));
    }

    #[test]
    fn test_json_report_multiple_solvers() {
        let mut metrics = RouterMetrics::new();
        metrics.record_dispatch("z4", Duration::from_millis(10), true);
        metrics.record_dispatch("zani", Duration::from_millis(20), true);

        let report = format!("{}", metrics.json_report());
        assert!(report.contains("\"z4\":{"));
        assert!(report.contains("\"zani\":{"));
        // Should be valid JSON-ish (contains opening and closing braces)
        assert!(report.starts_with('{'));
        assert!(report.ends_with('}'));
    }

    #[test]
    fn test_router_metrics_empty() {
        let metrics = RouterMetrics::new();
        assert_eq!(metrics.total_dispatched(), 0);
        assert_eq!(metrics.cache_hit_rate(), 0.0);
        assert!(metrics.solver_names().is_empty());
        assert!(metrics.per_solver_counts().is_empty());
    }

    #[test]
    fn test_terminal_report_empty_metrics() {
        let metrics = RouterMetrics::new();
        let report = format!("{}", metrics.terminal_report());
        assert!(report.contains("Total dispatched: 0"));
    }

    #[test]
    fn test_json_report_empty_metrics() {
        let metrics = RouterMetrics::new();
        let report = format!("{}", metrics.json_report());
        assert!(report.contains("\"total_dispatched\":0"));
        assert!(report.contains("\"solvers\":{}"));
    }

    #[test]
    fn test_latency_histogram_custom_buckets() {
        let hist = LatencyHistogram::with_buckets(vec![100.0, 200.0]);
        let buckets = hist.buckets();
        assert_eq!(buckets.len(), 3); // 2 bounds + overflow
        assert_eq!(buckets[0].0, 100.0);
        assert_eq!(buckets[1].0, 200.0);
        assert!(buckets[2].0.is_infinite());
    }

    #[test]
    fn test_solver_metrics_new() {
        let sm = SolverMetrics::new();
        assert_eq!(sm.dispatched, 0);
        assert_eq!(sm.successes, 0);
        assert_eq!(sm.errors, 0);
        assert_eq!(sm.cache_hits, 0);
        assert_eq!(sm.cache_misses, 0);
        assert_eq!(sm.latency.count(), 0);
    }
}
