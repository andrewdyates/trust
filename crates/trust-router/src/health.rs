// trust-router/health.rs: Solver health monitoring and circuit breaking
//
// tRust: Tracks solver availability, response times, error rates, and timeouts.
// Provides circuit-breaking to avoid sending work to unhealthy solvers with
// exponential backoff for recovery probing.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::time::{Duration, Instant};
use trust_types::fx::FxHashMap;

/// tRust: Health status of a solver backend.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum HealthStatus {
    /// Solver is responding normally with acceptable error rates.
    Healthy,
    /// Solver has elevated error rates (> 50%) but is still partially functional.
    Degraded,
    /// Solver has excessive error rates (> 80%) and should not receive new work.
    Unavailable,
}

/// tRust: Configuration for health monitoring thresholds.
#[derive(Debug, Clone)]
pub struct HealthConfig {
    /// Error rate threshold to enter Degraded state (default: 0.5).
    pub degraded_threshold: f64,
    /// Error rate threshold to enter Unavailable state (default: 0.8).
    pub unavailable_threshold: f64,
    /// Minimum number of results before health assessment applies (default: 5).
    pub min_samples: usize,
    /// Base backoff duration for Unavailable solvers before retry (default: 10s).
    pub backoff_base: Duration,
    /// Maximum backoff duration (default: 5 minutes).
    pub backoff_max: Duration,
    /// Maximum number of latency samples to retain per solver (default: 1000).
    pub max_samples: usize,
}

impl Default for HealthConfig {
    fn default() -> Self {
        Self {
            degraded_threshold: 0.5,
            unavailable_threshold: 0.8,
            min_samples: 5,
            backoff_base: Duration::from_secs(10),
            backoff_max: Duration::from_secs(300),
            max_samples: 1000,
        }
    }
}

/// tRust: Snapshot of a solver's current health state.
#[derive(Debug, Clone)]
pub struct SolverHealth {
    /// Solver name.
    pub name: String,
    /// Current health status.
    pub status: HealthStatus,
    /// Median latency (50th percentile) in milliseconds.
    pub latency_p50: f64,
    /// 99th percentile latency in milliseconds.
    pub latency_p99: f64,
    /// Error rate as a fraction [0.0, 1.0].
    pub error_rate: f64,
    /// When this health snapshot was computed.
    pub last_check: Instant,
    /// Total number of recorded results.
    pub total_results: usize,
    /// Number of consecutive failures (resets on success).
    pub consecutive_failures: usize,
}

/// tRust: Internal tracking state for a single solver.
struct SolverTracker {
    /// Sorted latency samples in milliseconds.
    latencies_ms: Vec<f64>,
    /// Total successes.
    successes: u64,
    /// Total failures.
    failures: u64,
    /// Consecutive failure count (resets on success).
    consecutive_failures: usize,
    /// Number of times this solver has entered Unavailable state.
    unavailable_count: u32,
    /// When the solver last became Unavailable (for backoff calculation).
    unavailable_since: Option<Instant>,
}

impl SolverTracker {
    fn new() -> Self {
        Self {
            latencies_ms: Vec::new(),
            successes: 0,
            failures: 0,
            consecutive_failures: 0,
            unavailable_count: 0,
            unavailable_since: None,
        }
    }

    fn total(&self) -> u64 {
        self.successes + self.failures
    }

    fn error_rate(&self) -> f64 {
        let total = self.total();
        if total == 0 { 0.0 } else { self.failures as f64 / total as f64 }
    }

    /// Compute the percentile from sorted latencies. Returns 0.0 if empty.
    fn percentile(&self, p: f64) -> f64 {
        if self.latencies_ms.is_empty() {
            return 0.0;
        }
        let idx = ((p / 100.0) * (self.latencies_ms.len() as f64 - 1.0)).round() as usize;
        let idx = idx.min(self.latencies_ms.len() - 1);
        self.latencies_ms[idx]
    }

    /// Insert a latency sample, keeping the list sorted and bounded.
    fn add_latency(&mut self, ms: f64, max_samples: usize) {
        // Binary search insert to maintain sorted order.
        let pos = self.latencies_ms.partition_point(|&x| x < ms);
        self.latencies_ms.insert(pos, ms);

        // Evict oldest (smallest) samples if over budget.
        if self.latencies_ms.len() > max_samples {
            self.latencies_ms.remove(0);
        }
    }
}

/// tRust: Health monitor that tracks all registered solver backends.
///
/// Call `record_result` after each solver invocation. Query `get_health`
/// for a snapshot or `circuit_breaker` to decide whether to skip a solver.
pub struct HealthMonitor {
    trackers: FxHashMap<String, SolverTracker>,
    config: HealthConfig,
}

impl HealthMonitor {
    /// Create a health monitor with default configuration.
    #[must_use]
    pub fn new() -> Self {
        Self { trackers: FxHashMap::default(), config: HealthConfig::default() }
    }

    /// Create a health monitor with custom configuration.
    #[must_use]
    pub fn with_config(config: HealthConfig) -> Self {
        Self { trackers: FxHashMap::default(), config }
    }

    /// Record a solver invocation result.
    ///
    /// `solver`: solver name (must match across calls).
    /// `duration`: wall-clock time of the invocation.
    /// `success`: true if the solver returned a useful result (Proved, Failed, or Unknown
    ///            with a reason), false if it crashed, timed out, or returned an error.
    pub fn record_result(&mut self, solver: &str, duration: Duration, success: bool) {
        let tracker = self.trackers.entry(solver.to_string()).or_insert_with(SolverTracker::new);

        let ms = duration.as_secs_f64() * 1000.0;
        tracker.add_latency(ms, self.config.max_samples);

        if success {
            tracker.successes += 1;
            tracker.consecutive_failures = 0;
            // If we were Unavailable and got a success, reset backoff state
            tracker.unavailable_since = None;
        } else {
            tracker.failures += 1;
            tracker.consecutive_failures += 1;
        }
    }

    /// Get a health snapshot for a solver.
    ///
    /// Returns a default Healthy snapshot with zero metrics if the solver
    /// has not been seen.
    #[must_use]
    pub fn get_health(&self, solver: &str) -> SolverHealth {
        let now = Instant::now();

        let Some(tracker) = self.trackers.get(solver) else {
            return SolverHealth {
                name: solver.to_string(),
                status: HealthStatus::Healthy,
                latency_p50: 0.0,
                latency_p99: 0.0,
                error_rate: 0.0,
                last_check: now,
                total_results: 0,
                consecutive_failures: 0,
            };
        };

        let error_rate = tracker.error_rate();
        let status = self.classify_status(tracker);

        SolverHealth {
            name: solver.to_string(),
            status,
            latency_p50: tracker.percentile(50.0),
            latency_p99: tracker.percentile(99.0),
            error_rate,
            last_check: now,
            total_results: tracker.total() as usize,
            consecutive_failures: tracker.consecutive_failures,
        }
    }

    /// Check the circuit breaker for a solver.
    ///
    /// Returns `true` if the solver should be skipped (circuit is open).
    /// Returns `false` if the solver is safe to use.
    ///
    /// For Unavailable solvers, applies exponential backoff: the circuit
    /// re-closes briefly after the backoff period to allow a probe request.
    #[must_use]
    pub fn circuit_breaker(&self, solver: &str) -> bool {
        let Some(tracker) = self.trackers.get(solver) else {
            return false; // Unknown solver — allow
        };

        let status = self.classify_status(tracker);

        match status {
            HealthStatus::Healthy => false,
            HealthStatus::Degraded => false, // Allow but caller may deprioritize
            HealthStatus::Unavailable => {
                // Check if backoff period has elapsed for a probe
                if let Some(since) = tracker.unavailable_since {
                    let backoff = self.compute_backoff(tracker.unavailable_count);
                    since.elapsed() < backoff
                } else {
                    // Just became unavailable — block
                    true
                }
            }
        }
    }

    /// Mark a solver as entering the Unavailable state (for backoff tracking).
    ///
    /// Called internally when status transitions to Unavailable. Callers
    /// can also call this explicitly to force a solver offline.
    pub fn mark_unavailable(&mut self, solver: &str) {
        let tracker = self.trackers.entry(solver.to_string()).or_insert_with(SolverTracker::new);
        tracker.unavailable_count += 1;
        tracker.unavailable_since = Some(Instant::now());
    }

    /// Get all tracked solver names.
    #[must_use]
    pub fn tracked_solvers(&self) -> Vec<String> {
        self.trackers.keys().cloned().collect()
    }

    /// Get health snapshots for all tracked solvers.
    #[must_use]
    pub fn all_health(&self) -> Vec<SolverHealth> {
        self.trackers.keys().map(|name| self.get_health(name)).collect()
    }

    /// Classify the health status of a solver tracker.
    fn classify_status(&self, tracker: &SolverTracker) -> HealthStatus {
        // Not enough data to assess
        if (tracker.total() as usize) < self.config.min_samples {
            return HealthStatus::Healthy;
        }

        let error_rate = tracker.error_rate();

        if error_rate > self.config.unavailable_threshold {
            HealthStatus::Unavailable
        } else if error_rate > self.config.degraded_threshold {
            HealthStatus::Degraded
        } else {
            HealthStatus::Healthy
        }
    }

    /// Compute exponential backoff duration for an Unavailable solver.
    fn compute_backoff(&self, unavailable_count: u32) -> Duration {
        // Exponential backoff: base * 2^(count - 1), capped at max
        let exponent = unavailable_count.saturating_sub(1).min(10);
        let multiplier = 1u64 << exponent;
        let backoff = self.config.backoff_base * multiplier as u32;
        backoff.min(self.config.backoff_max)
    }
}

impl Default for HealthMonitor {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_health_monitor_new_solver_is_healthy() {
        let monitor = HealthMonitor::new();
        let health = monitor.get_health("z4");
        assert_eq!(health.status, HealthStatus::Healthy);
        assert_eq!(health.total_results, 0);
        assert_eq!(health.error_rate, 0.0);
        assert_eq!(health.latency_p50, 0.0);
    }

    #[test]
    fn test_health_monitor_record_success() {
        let mut monitor = HealthMonitor::new();
        monitor.record_result("z4", Duration::from_millis(50), true);
        monitor.record_result("z4", Duration::from_millis(100), true);

        let health = monitor.get_health("z4");
        assert_eq!(health.total_results, 2);
        assert_eq!(health.error_rate, 0.0);
        assert_eq!(health.consecutive_failures, 0);
        assert!(health.latency_p50 > 0.0);
    }

    #[test]
    fn test_health_monitor_record_failure() {
        let mut monitor = HealthMonitor::new();
        monitor.record_result("z4", Duration::from_millis(50), false);

        let health = monitor.get_health("z4");
        assert_eq!(health.total_results, 1);
        assert!((health.error_rate - 1.0).abs() < f64::EPSILON);
        assert_eq!(health.consecutive_failures, 1);
    }

    #[test]
    fn test_health_status_transitions_to_degraded() {
        let config = HealthConfig {
            min_samples: 4,
            degraded_threshold: 0.5,
            unavailable_threshold: 0.8,
            ..Default::default()
        };
        let mut monitor = HealthMonitor::with_config(config);

        // 2 successes, 2 failures = 50% error rate, but need 4 samples min
        monitor.record_result("z4", Duration::from_millis(10), true);
        monitor.record_result("z4", Duration::from_millis(10), false);
        monitor.record_result("z4", Duration::from_millis(10), true);
        monitor.record_result("z4", Duration::from_millis(10), false);

        let health = monitor.get_health("z4");
        assert_eq!(health.total_results, 4);
        // 50% error rate is at boundary. >0.5 triggers degraded, = 0.5 stays healthy.
        assert_eq!(health.status, HealthStatus::Healthy);

        // One more failure tips it over
        monitor.record_result("z4", Duration::from_millis(10), false);
        let health = monitor.get_health("z4");
        // 3 failures / 5 total = 0.6 > 0.5
        assert_eq!(health.status, HealthStatus::Degraded);
    }

    #[test]
    fn test_health_status_transitions_to_unavailable() {
        let config = HealthConfig {
            min_samples: 5,
            degraded_threshold: 0.5,
            unavailable_threshold: 0.8,
            ..Default::default()
        };
        let mut monitor = HealthMonitor::with_config(config);

        // 1 success, 4 failures = 80% error rate
        monitor.record_result("z4", Duration::from_millis(10), true);
        for _ in 0..4 {
            monitor.record_result("z4", Duration::from_millis(10), false);
        }

        let health = monitor.get_health("z4");
        // 4/5 = 0.8, need >0.8 for Unavailable
        assert_eq!(health.status, HealthStatus::Degraded);

        // One more failure: 5/6 = 0.833 > 0.8
        monitor.record_result("z4", Duration::from_millis(10), false);
        let health = monitor.get_health("z4");
        assert_eq!(health.status, HealthStatus::Unavailable);
    }

    #[test]
    fn test_health_recovery_on_success() {
        let config = HealthConfig {
            min_samples: 2,
            degraded_threshold: 0.5,
            unavailable_threshold: 0.8,
            ..Default::default()
        };
        let mut monitor = HealthMonitor::with_config(config);

        // Start degraded: 2 failures out of 3
        monitor.record_result("z4", Duration::from_millis(10), true);
        monitor.record_result("z4", Duration::from_millis(10), false);
        monitor.record_result("z4", Duration::from_millis(10), false);
        assert_eq!(monitor.get_health("z4").status, HealthStatus::Degraded);

        // Add successes to recover
        for _ in 0..5 {
            monitor.record_result("z4", Duration::from_millis(10), true);
        }

        let health = monitor.get_health("z4");
        // 6 successes / 8 total = 25% error rate
        assert_eq!(health.status, HealthStatus::Healthy);
        assert_eq!(health.consecutive_failures, 0);
    }

    #[test]
    fn test_circuit_breaker_healthy_allows() {
        let monitor = HealthMonitor::new();
        assert!(!monitor.circuit_breaker("z4"));
    }

    #[test]
    fn test_circuit_breaker_degraded_allows() {
        let config = HealthConfig {
            min_samples: 2,
            degraded_threshold: 0.3,
            unavailable_threshold: 0.8,
            ..Default::default()
        };
        let mut monitor = HealthMonitor::with_config(config);

        // 1 success, 1 failure = 50% > 0.3 degraded threshold
        monitor.record_result("z4", Duration::from_millis(10), true);
        monitor.record_result("z4", Duration::from_millis(10), false);

        assert_eq!(monitor.get_health("z4").status, HealthStatus::Degraded);
        // Circuit breaker allows Degraded solvers
        assert!(!monitor.circuit_breaker("z4"));
    }

    #[test]
    fn test_circuit_breaker_unavailable_blocks() {
        let config = HealthConfig {
            min_samples: 2,
            degraded_threshold: 0.5,
            unavailable_threshold: 0.8,
            backoff_base: Duration::from_secs(60),
            ..Default::default()
        };
        let mut monitor = HealthMonitor::with_config(config);

        // All failures -> Unavailable
        for _ in 0..5 {
            monitor.record_result("z4", Duration::from_millis(10), false);
        }

        // Mark unavailable to set backoff timer
        monitor.mark_unavailable("z4");

        assert_eq!(monitor.get_health("z4").status, HealthStatus::Unavailable);
        // Should be blocked (backoff hasn't elapsed)
        assert!(monitor.circuit_breaker("z4"));
    }

    #[test]
    fn test_circuit_breaker_unknown_solver_allows() {
        let monitor = HealthMonitor::new();
        assert!(!monitor.circuit_breaker("never_seen"));
    }

    #[test]
    fn test_latency_percentiles() {
        let mut monitor = HealthMonitor::new();

        // Add 100 samples: 1ms, 2ms, ..., 100ms
        for i in 1..=100 {
            monitor.record_result("z4", Duration::from_millis(i), true);
        }

        let health = monitor.get_health("z4");
        // p50 should be around 50ms
        assert!((health.latency_p50 - 50.0).abs() < 2.0);
        // p99 should be around 99ms
        assert!((health.latency_p99 - 99.0).abs() < 2.0);
    }

    #[test]
    fn test_consecutive_failures_reset_on_success() {
        let mut monitor = HealthMonitor::new();

        monitor.record_result("z4", Duration::from_millis(10), false);
        monitor.record_result("z4", Duration::from_millis(10), false);
        monitor.record_result("z4", Duration::from_millis(10), false);
        assert_eq!(monitor.get_health("z4").consecutive_failures, 3);

        monitor.record_result("z4", Duration::from_millis(10), true);
        assert_eq!(monitor.get_health("z4").consecutive_failures, 0);

        monitor.record_result("z4", Duration::from_millis(10), false);
        assert_eq!(monitor.get_health("z4").consecutive_failures, 1);
    }

    #[test]
    fn test_min_samples_gate() {
        let config = HealthConfig {
            min_samples: 10,
            degraded_threshold: 0.5,
            unavailable_threshold: 0.8,
            ..Default::default()
        };
        let mut monitor = HealthMonitor::with_config(config);

        // All failures but below min_samples — should still be Healthy
        for _ in 0..9 {
            monitor.record_result("z4", Duration::from_millis(10), false);
        }

        assert_eq!(monitor.get_health("z4").status, HealthStatus::Healthy);

        // One more failure hits min_samples, now error rate kicks in
        monitor.record_result("z4", Duration::from_millis(10), false);
        assert_eq!(monitor.get_health("z4").status, HealthStatus::Unavailable);
    }

    #[test]
    fn test_tracked_solvers() {
        let mut monitor = HealthMonitor::new();
        monitor.record_result("z4", Duration::from_millis(10), true);
        monitor.record_result("zani", Duration::from_millis(20), true);
        monitor.record_result("sunder", Duration::from_millis(30), false);

        let mut solvers = monitor.tracked_solvers();
        solvers.sort();
        assert_eq!(solvers, vec!["sunder", "z4", "zani"]);
    }

    #[test]
    fn test_all_health() {
        let mut monitor = HealthMonitor::new();
        monitor.record_result("z4", Duration::from_millis(10), true);
        monitor.record_result("zani", Duration::from_millis(20), true);

        let all = monitor.all_health();
        assert_eq!(all.len(), 2);
        assert!(all.iter().all(|h| h.status == HealthStatus::Healthy));
    }

    #[test]
    fn test_exponential_backoff_increases() {
        let config = HealthConfig {
            backoff_base: Duration::from_secs(10),
            backoff_max: Duration::from_secs(300),
            ..Default::default()
        };
        let monitor = HealthMonitor::with_config(config);

        // First unavailable: base * 2^0 = 10s
        let b1 = monitor.compute_backoff(1);
        assert_eq!(b1, Duration::from_secs(10));

        // Second: base * 2^1 = 20s
        let b2 = monitor.compute_backoff(2);
        assert_eq!(b2, Duration::from_secs(20));

        // Third: base * 2^2 = 40s
        let b3 = monitor.compute_backoff(3);
        assert_eq!(b3, Duration::from_secs(40));
    }

    #[test]
    fn test_exponential_backoff_capped() {
        let config = HealthConfig {
            backoff_base: Duration::from_secs(10),
            backoff_max: Duration::from_secs(60),
            ..Default::default()
        };
        let monitor = HealthMonitor::with_config(config);

        // Large count should be capped
        let backoff = monitor.compute_backoff(100);
        assert!(backoff <= Duration::from_secs(60));
    }

    #[test]
    fn test_mark_unavailable() {
        let mut monitor = HealthMonitor::new();
        monitor.mark_unavailable("z4");
        monitor.mark_unavailable("z4");

        // Should have incremented unavailable_count
        let tracker = monitor.trackers.get("z4").unwrap();
        assert_eq!(tracker.unavailable_count, 2);
        assert!(tracker.unavailable_since.is_some());
    }

    #[test]
    fn test_multiple_solvers_independent() {
        let mut monitor = HealthMonitor::new();

        // z4 is healthy, zani is failing
        for _ in 0..10 {
            monitor.record_result("z4", Duration::from_millis(10), true);
            monitor.record_result("zani", Duration::from_millis(10), false);
        }

        let z4_health = monitor.get_health("z4");
        let zani_health = monitor.get_health("zani");

        assert_eq!(z4_health.status, HealthStatus::Healthy);
        assert_eq!(zani_health.status, HealthStatus::Unavailable);
    }

    #[test]
    fn test_health_config_defaults() {
        let config = HealthConfig::default();
        assert!((config.degraded_threshold - 0.5).abs() < f64::EPSILON);
        assert!((config.unavailable_threshold - 0.8).abs() < f64::EPSILON);
        assert_eq!(config.min_samples, 5);
        assert_eq!(config.backoff_base, Duration::from_secs(10));
        assert_eq!(config.backoff_max, Duration::from_secs(300));
        assert_eq!(config.max_samples, 1000);
    }

    #[test]
    fn test_health_status_debug() {
        // Ensure all variants have Debug
        assert_eq!(format!("{:?}", HealthStatus::Healthy), "Healthy");
        assert_eq!(format!("{:?}", HealthStatus::Degraded), "Degraded");
        assert_eq!(format!("{:?}", HealthStatus::Unavailable), "Unavailable");
    }

    #[test]
    fn test_solver_health_snapshot_fields() {
        let mut monitor = HealthMonitor::new();
        monitor.record_result("z4", Duration::from_millis(42), true);
        monitor.record_result("z4", Duration::from_millis(100), false);

        let health = monitor.get_health("z4");
        assert_eq!(health.name, "z4");
        assert_eq!(health.total_results, 2);
        assert!((health.error_rate - 0.5).abs() < f64::EPSILON);
        assert!(health.latency_p50 > 0.0);
        assert!(health.latency_p99 > 0.0);
    }
}
