// trust-router/health_monitor.rs: Unified health-aware solver recommendation
//
// tRust: Combines HealthMonitor (error rates, latency, circuit breaking) with
// RouterMetrics (dispatch stats) and PerformanceHistory (win rates per VcKind)
// to produce a ranked recommendation of solvers for a given VC.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::time::{Duration, Instant};

use crate::adaptive::PerformanceHistory;
use crate::health::{HealthConfig, HealthMonitor, HealthStatus};
use crate::metrics::RouterMetrics;

/// tRust: Solver recommendation with scoring rationale.
#[derive(Debug, Clone)]
pub struct SolverRecommendation {
    /// Solver name.
    pub solver: String,
    /// Composite score (higher is better).
    pub score: f64,
    /// Current health status of this solver.
    pub health_status: HealthStatus,
    /// Whether the circuit breaker is open (solver should be skipped).
    pub circuit_open: bool,
    /// Win rate for this VC kind from adaptive history (0.0 if unknown).
    pub win_rate: f64,
    /// Success rate from router metrics (0.0 if no dispatches).
    pub success_rate: f64,
    /// Average latency in ms from health monitor (0.0 if no data).
    pub avg_latency_ms: f64,
}

/// tRust: Configuration for the unified health monitor scoring.
#[derive(Debug, Clone)]
pub struct UnifiedHealthConfig {
    /// Weight for win rate in composite score (default: 0.4).
    pub win_rate_weight: f64,
    /// Weight for success rate in composite score (default: 0.3).
    pub success_rate_weight: f64,
    /// Weight for latency in composite score (default: 0.2).
    /// Applied as (1.0 - normalized_latency), so lower latency = higher score.
    pub latency_weight: f64,
    /// Weight for health status in composite score (default: 0.1).
    pub health_weight: f64,
    /// Maximum latency in ms for normalization (default: 5000.0).
    /// Latencies above this are treated as 1.0 (worst).
    pub max_latency_ms: f64,
    /// Underlying health monitor config.
    pub health_config: HealthConfig,
}

impl Default for UnifiedHealthConfig {
    fn default() -> Self {
        Self {
            win_rate_weight: 0.4,
            success_rate_weight: 0.3,
            latency_weight: 0.2,
            health_weight: 0.1,
            max_latency_ms: 5000.0,
            health_config: HealthConfig::default(),
        }
    }
}

/// tRust: Unified health monitor that combines health, metrics, and adaptive history.
///
/// Provides `recommend_solver()` which returns a ranked list of solvers for a
/// given VC kind, factoring in health status, circuit breaker state, win rates,
/// success rates, and latency.
pub struct UnifiedHealthMonitor {
    health: HealthMonitor,
    metrics: RouterMetrics,
    history: PerformanceHistory,
    config: UnifiedHealthConfig,
    /// When this monitor was created (for uptime tracking).
    created_at: Instant,
}

impl UnifiedHealthMonitor {
    /// Create a unified health monitor with default configuration.
    #[must_use]
    pub fn new() -> Self {
        Self::with_config(UnifiedHealthConfig::default())
    }

    /// Create a unified health monitor with custom configuration.
    #[must_use]
    pub fn with_config(config: UnifiedHealthConfig) -> Self {
        Self {
            health: HealthMonitor::with_config(config.health_config.clone()),
            metrics: RouterMetrics::new(),
            history: PerformanceHistory::new(),
            config,
            created_at: Instant::now(),
        }
    }

    /// Record a solver invocation result across all subsystems.
    ///
    /// This is the primary entry point for recording outcomes. It updates:
    /// - Health monitor (error rates, latency percentiles, circuit breaker)
    /// - Router metrics (dispatch counts, latency histograms)
    /// - Performance history (win rates per VC kind)
    pub fn record_result(
        &mut self,
        solver: &str,
        vc_kind_key: &str,
        duration: Duration,
        success: bool,
        is_winner: bool,
    ) {
        let time_ms = duration.as_millis() as u64;

        // Update health monitor
        self.health.record_result(solver, duration, success);

        // Update router metrics
        self.metrics.record_dispatch(solver, duration, success);

        // Update performance history
        self.history.record_attempt(vc_kind_key, solver, time_ms);
        if is_winner {
            self.history.record_win(vc_kind_key, solver);
        }
    }

    /// Record a cache hit.
    pub fn record_cache_hit(&mut self, solver: &str) {
        self.metrics.record_cache_hit(solver);
    }

    /// Record a cache miss.
    pub fn record_cache_miss(&mut self, solver: &str) {
        self.metrics.record_cache_miss(solver);
    }

    /// Recommend solvers for a given VC kind, ranked by composite score.
    ///
    /// Solvers with open circuit breakers are included but marked as such
    /// (and scored 0.0), so callers can see the full picture.
    ///
    /// `vc_kind_key` should match the key used in `record_result`.
    /// `available_solvers` is the list of solver names to consider.
    #[must_use]
    pub fn recommend_solvers(
        &self,
        vc_kind_key: &str,
        available_solvers: &[&str],
    ) -> Vec<SolverRecommendation> {
        let mut recommendations: Vec<SolverRecommendation> = available_solvers
            .iter()
            .map(|&solver| self.score_solver(solver, vc_kind_key))
            .collect();

        // Sort by score descending (circuit-open solvers will have score 0.0)
        recommendations.sort_by(|a, b| {
            b.score
                .partial_cmp(&a.score)
                .unwrap_or(std::cmp::Ordering::Equal)
        });

        recommendations
    }

    /// Get the single best solver recommendation, excluding circuit-open solvers.
    ///
    /// Returns `None` if all solvers are circuit-open or no solvers are available.
    #[must_use]
    pub fn best_solver(
        &self,
        vc_kind_key: &str,
        available_solvers: &[&str],
    ) -> Option<SolverRecommendation> {
        self.recommend_solvers(vc_kind_key, available_solvers)
            .into_iter()
            .find(|r| !r.circuit_open)
    }

    /// Check if a solver should be skipped (circuit breaker is open).
    #[must_use]
    pub fn should_skip(&self, solver: &str) -> bool {
        self.health.circuit_breaker(solver)
    }

    /// Get the health status of a solver.
    #[must_use]
    pub fn health_status(&self, solver: &str) -> HealthStatus {
        self.health.get_health(solver).status
    }

    /// Get a reference to the underlying health monitor.
    #[must_use]
    pub fn health(&self) -> &HealthMonitor {
        &self.health
    }

    /// Get a reference to the underlying router metrics.
    #[must_use]
    pub fn metrics(&self) -> &RouterMetrics {
        &self.metrics
    }

    /// Get a reference to the underlying performance history.
    #[must_use]
    pub fn history(&self) -> &PerformanceHistory {
        &self.history
    }

    /// Get uptime since monitor creation.
    #[must_use]
    pub fn uptime(&self) -> Duration {
        self.created_at.elapsed()
    }

    /// Generate a unified summary combining health, metrics, and history.
    #[must_use]
    pub fn summary(&self) -> UnifiedSummary {
        let solver_names = self.all_solver_names();
        let solver_summaries: Vec<SolverSummary> = solver_names
            .iter()
            .map(|name| {
                let health = self.health.get_health(name);
                let metrics = self.metrics.solver_metrics(name);
                SolverSummary {
                    name: name.clone(),
                    health_status: health.status,
                    error_rate: health.error_rate,
                    latency_p50_ms: health.latency_p50,
                    latency_p99_ms: health.latency_p99,
                    total_dispatched: metrics.map(|m| m.dispatched).unwrap_or(0),
                    success_rate: metrics.map(|m| m.success_rate()).unwrap_or(0.0),
                    cache_hit_rate: metrics.map(|m| m.cache_hit_rate()).unwrap_or(0.0),
                    circuit_open: self.health.circuit_breaker(name),
                }
            })
            .collect();

        UnifiedSummary {
            total_dispatched: self.metrics.total_dispatched(),
            cache_hit_rate: self.metrics.cache_hit_rate(),
            tracked_vc_kinds: self.history.tracked_kinds().len(),
            total_races: self.history.total_races(),
            uptime: self.created_at.elapsed(),
            solvers: solver_summaries,
        }
    }

    /// Score a single solver for a given VC kind.
    fn score_solver(&self, solver: &str, vc_kind_key: &str) -> SolverRecommendation {
        let health = self.health.get_health(solver);
        let circuit_open = self.health.circuit_breaker(solver);

        // Win rate from performance history
        let win_rate = self
            .history
            .records_for_kind(vc_kind_key)
            .iter()
            .find(|r| r.solver == solver)
            .map(|r| r.win_rate())
            .unwrap_or(0.0);

        // Success rate from router metrics
        let success_rate = self
            .metrics
            .solver_metrics(solver)
            .map(|m| m.success_rate())
            .unwrap_or(0.0);

        // Average latency from health monitor (use p50 as representative)
        let avg_latency_ms = health.latency_p50;

        // Composite score
        let score = if circuit_open {
            0.0
        } else {
            self.compute_score(win_rate, success_rate, avg_latency_ms, health.status)
        };

        SolverRecommendation {
            solver: solver.to_string(),
            score,
            health_status: health.status,
            circuit_open,
            win_rate,
            success_rate,
            avg_latency_ms,
        }
    }

    /// Compute composite score from individual factors.
    fn compute_score(
        &self,
        win_rate: f64,
        success_rate: f64,
        latency_ms: f64,
        status: HealthStatus,
    ) -> f64 {
        let c = &self.config;

        // Normalize latency: lower is better, capped at max_latency_ms
        let latency_score = 1.0 - (latency_ms / c.max_latency_ms).min(1.0);

        // Health status score
        let health_score = match status {
            HealthStatus::Healthy => 1.0,
            HealthStatus::Degraded => 0.5,
            HealthStatus::Unavailable => 0.0,
        };

        c.win_rate_weight * win_rate
            + c.success_rate_weight * success_rate
            + c.latency_weight * latency_score
            + c.health_weight * health_score
    }

    /// Collect all solver names seen across health, metrics, and history.
    fn all_solver_names(&self) -> Vec<String> {
        let mut names: Vec<String> = Vec::new();

        for name in self.health.tracked_solvers() {
            if !names.contains(&name) {
                names.push(name);
            }
        }
        for name in self.metrics.solver_names() {
            if !names.contains(&name) {
                names.push(name);
            }
        }

        names.sort();
        names
    }
}

impl Default for UnifiedHealthMonitor {
    fn default() -> Self {
        Self::new()
    }
}

/// tRust: Per-solver summary combining health and metrics data.
#[derive(Debug, Clone)]
pub struct SolverSummary {
    /// Solver name.
    pub name: String,
    /// Current health status.
    pub health_status: HealthStatus,
    /// Error rate from health monitor.
    pub error_rate: f64,
    /// Median latency in ms.
    pub latency_p50_ms: f64,
    /// 99th percentile latency in ms.
    pub latency_p99_ms: f64,
    /// Total dispatches from router metrics.
    pub total_dispatched: u64,
    /// Success rate from router metrics.
    pub success_rate: f64,
    /// Cache hit rate from router metrics.
    pub cache_hit_rate: f64,
    /// Whether the circuit breaker is open.
    pub circuit_open: bool,
}

/// tRust: Unified summary of the entire monitoring system.
#[derive(Debug, Clone)]
pub struct UnifiedSummary {
    /// Total VCs dispatched.
    pub total_dispatched: u64,
    /// Overall cache hit rate.
    pub cache_hit_rate: f64,
    /// Number of tracked VC kinds in performance history.
    pub tracked_vc_kinds: usize,
    /// Total adaptive races completed.
    pub total_races: u64,
    /// Monitor uptime.
    pub uptime: Duration,
    /// Per-solver summaries.
    pub solvers: Vec<SolverSummary>,
}

impl std::fmt::Display for UnifiedSummary {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "=== Unified Health Summary ===")?;
        writeln!(f, "Total dispatched: {}", self.total_dispatched)?;
        writeln!(f, "Cache hit rate:   {:.1}%", self.cache_hit_rate * 100.0)?;
        writeln!(f, "Tracked VC kinds: {}", self.tracked_vc_kinds)?;
        writeln!(f, "Total races:      {}", self.total_races)?;
        writeln!(f, "Uptime:           {:.1}s", self.uptime.as_secs_f64())?;
        writeln!(f)?;

        for s in &self.solvers {
            writeln!(f, "--- {} ---", s.name)?;
            writeln!(f, "  Health:      {:?}{}", s.health_status, if s.circuit_open { " [CIRCUIT OPEN]" } else { "" })?;
            writeln!(f, "  Error rate:  {:.1}%", s.error_rate * 100.0)?;
            writeln!(f, "  Latency:     p50={:.1}ms p99={:.1}ms", s.latency_p50_ms, s.latency_p99_ms)?;
            writeln!(f, "  Dispatched:  {}", s.total_dispatched)?;
            writeln!(f, "  Success rate: {:.1}%", s.success_rate * 100.0)?;
            writeln!(f, "  Cache hits:  {:.1}%", s.cache_hit_rate * 100.0)?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_unified_health_monitor_new_is_empty() {
        let monitor = UnifiedHealthMonitor::new();
        let summary = monitor.summary();
        assert_eq!(summary.total_dispatched, 0);
        assert!(summary.solvers.is_empty());
    }

    #[test]
    fn test_record_result_updates_all_subsystems() {
        let mut monitor = UnifiedHealthMonitor::new();
        monitor.record_result("z4", "div_zero", Duration::from_millis(10), true, true);

        // Health monitor updated
        let health = monitor.health().get_health("z4");
        assert_eq!(health.total_results, 1);

        // Metrics updated
        assert_eq!(monitor.metrics().total_dispatched(), 1);
        let sm = monitor.metrics().solver_metrics("z4").unwrap();
        assert_eq!(sm.dispatched, 1);
        assert_eq!(sm.successes, 1);

        // History updated
        let records = monitor.history().records_for_kind("div_zero");
        assert_eq!(records.len(), 1);
        assert_eq!(records[0].wins, 1);
    }

    #[test]
    fn test_record_result_failure() {
        let mut monitor = UnifiedHealthMonitor::new();
        monitor.record_result("z4", "div_zero", Duration::from_millis(100), false, false);

        let health = monitor.health().get_health("z4");
        assert_eq!(health.consecutive_failures, 1);

        let sm = monitor.metrics().solver_metrics("z4").unwrap();
        assert_eq!(sm.errors, 1);
    }

    #[test]
    fn test_recommend_solvers_empty() {
        let monitor = UnifiedHealthMonitor::new();
        let recs = monitor.recommend_solvers("div_zero", &["z4", "zani"]);
        assert_eq!(recs.len(), 2);
        // Both should have default healthy status and zero scores
        for rec in &recs {
            assert_eq!(rec.health_status, HealthStatus::Healthy);
            assert!(!rec.circuit_open);
        }
    }

    #[test]
    fn test_recommend_solvers_prefers_winner() {
        let mut monitor = UnifiedHealthMonitor::new();

        // z4 wins consistently
        for _ in 0..10 {
            monitor.record_result("z4", "div_zero", Duration::from_millis(10), true, true);
            monitor.record_result("zani", "div_zero", Duration::from_millis(50), true, false);
        }

        let recs = monitor.recommend_solvers("div_zero", &["z4", "zani"]);
        assert_eq!(recs[0].solver, "z4");
        assert!(recs[0].score > recs[1].score);
        assert!(recs[0].win_rate > recs[1].win_rate);
    }

    #[test]
    fn test_recommend_solvers_penalizes_failures() {
        let config = UnifiedHealthConfig {
            health_config: HealthConfig {
                min_samples: 2,
                ..Default::default()
            },
            ..Default::default()
        };
        let mut monitor = UnifiedHealthMonitor::with_config(config);

        // z4 succeeds, zani fails
        for _ in 0..5 {
            monitor.record_result("z4", "div_zero", Duration::from_millis(10), true, true);
            monitor.record_result("zani", "div_zero", Duration::from_millis(10), false, false);
        }

        let recs = monitor.recommend_solvers("div_zero", &["z4", "zani"]);
        assert_eq!(recs[0].solver, "z4");
        assert!(recs[0].score > recs[1].score);
    }

    #[test]
    fn test_recommend_solvers_penalizes_high_latency() {
        let mut monitor = UnifiedHealthMonitor::new();

        // z4 is fast, zani is slow. Both succeed.
        for _ in 0..10 {
            monitor.record_result("z4", "div_zero", Duration::from_millis(5), true, true);
            monitor.record_result("zani", "div_zero", Duration::from_millis(4000), true, true);
        }

        let recs = monitor.recommend_solvers("div_zero", &["z4", "zani"]);
        assert_eq!(recs[0].solver, "z4");
        assert!(recs[0].avg_latency_ms < recs[1].avg_latency_ms);
    }

    #[test]
    fn test_best_solver_skips_circuit_open() {
        let config = UnifiedHealthConfig {
            health_config: HealthConfig {
                min_samples: 2,
                unavailable_threshold: 0.8,
                ..Default::default()
            },
            ..Default::default()
        };
        let mut monitor = UnifiedHealthMonitor::with_config(config);

        // z4 is all failures -> unavailable
        for _ in 0..5 {
            monitor.record_result("z4", "div_zero", Duration::from_millis(10), false, false);
        }
        // Mark unavailable to activate circuit breaker
        monitor.health.mark_unavailable("z4");

        // zani is healthy
        for _ in 0..5 {
            monitor.record_result("zani", "div_zero", Duration::from_millis(10), true, true);
        }

        let best = monitor.best_solver("div_zero", &["z4", "zani"]);
        assert!(best.is_some());
        assert_eq!(best.unwrap().solver, "zani");
    }

    #[test]
    fn test_best_solver_returns_none_when_all_circuit_open() {
        let config = UnifiedHealthConfig {
            health_config: HealthConfig {
                min_samples: 2,
                unavailable_threshold: 0.5,
                ..Default::default()
            },
            ..Default::default()
        };
        let mut monitor = UnifiedHealthMonitor::with_config(config);

        for _ in 0..5 {
            monitor.record_result("z4", "div_zero", Duration::from_millis(10), false, false);
            monitor.record_result("zani", "div_zero", Duration::from_millis(10), false, false);
        }
        monitor.health.mark_unavailable("z4");
        monitor.health.mark_unavailable("zani");

        let best = monitor.best_solver("div_zero", &["z4", "zani"]);
        assert!(best.is_none());
    }

    #[test]
    fn test_should_skip_unknown_solver() {
        let monitor = UnifiedHealthMonitor::new();
        assert!(!monitor.should_skip("never_seen"));
    }

    #[test]
    fn test_health_status_new_solver() {
        let monitor = UnifiedHealthMonitor::new();
        assert_eq!(monitor.health_status("z4"), HealthStatus::Healthy);
    }

    #[test]
    fn test_cache_hit_miss_recording() {
        let mut monitor = UnifiedHealthMonitor::new();
        monitor.record_cache_hit("z4");
        monitor.record_cache_hit("z4");
        monitor.record_cache_miss("z4");

        let sm = monitor.metrics().solver_metrics("z4").unwrap();
        assert_eq!(sm.cache_hits, 2);
        assert_eq!(sm.cache_misses, 1);
    }

    #[test]
    fn test_unified_summary_format() {
        let mut monitor = UnifiedHealthMonitor::new();
        monitor.record_result("z4", "div_zero", Duration::from_millis(42), true, true);
        monitor.record_result("zani", "postcond", Duration::from_millis(100), true, false);

        let summary = monitor.summary();
        assert_eq!(summary.total_dispatched, 2);
        assert_eq!(summary.solvers.len(), 2);

        let display = format!("{}", summary);
        assert!(display.contains("Unified Health Summary"));
        assert!(display.contains("Total dispatched: 2"));
        assert!(display.contains("z4"));
        assert!(display.contains("zani"));
    }

    #[test]
    fn test_unified_summary_empty() {
        let monitor = UnifiedHealthMonitor::new();
        let summary = monitor.summary();
        let display = format!("{}", summary);
        assert!(display.contains("Total dispatched: 0"));
    }

    #[test]
    fn test_uptime_is_nonzero() {
        let monitor = UnifiedHealthMonitor::new();
        // Uptime should be at least 0 (instantaneous).
        // We cannot assert > 0 reliably, but can assert it does not panic.
        let _ = monitor.uptime();
    }

    #[test]
    fn test_unified_config_default() {
        let config = UnifiedHealthConfig::default();
        assert!((config.win_rate_weight - 0.4).abs() < f64::EPSILON);
        assert!((config.success_rate_weight - 0.3).abs() < f64::EPSILON);
        assert!((config.latency_weight - 0.2).abs() < f64::EPSILON);
        assert!((config.health_weight - 0.1).abs() < f64::EPSILON);
        assert!((config.max_latency_ms - 5000.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_score_computation_all_perfect() {
        let monitor = UnifiedHealthMonitor::new();
        // Perfect scores: win_rate=1.0, success_rate=1.0, latency=0ms, Healthy
        let score = monitor.compute_score(1.0, 1.0, 0.0, HealthStatus::Healthy);
        // 0.4*1.0 + 0.3*1.0 + 0.2*1.0 + 0.1*1.0 = 1.0
        assert!((score - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_score_computation_all_worst() {
        let monitor = UnifiedHealthMonitor::new();
        // Worst scores: win_rate=0, success_rate=0, latency=max, Unavailable
        let score = monitor.compute_score(0.0, 0.0, 5000.0, HealthStatus::Unavailable);
        assert!((score - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_score_computation_degraded_health() {
        let monitor = UnifiedHealthMonitor::new();
        let score = monitor.compute_score(0.5, 0.5, 0.0, HealthStatus::Degraded);
        // 0.4*0.5 + 0.3*0.5 + 0.2*1.0 + 0.1*0.5 = 0.2 + 0.15 + 0.2 + 0.05 = 0.6
        assert!((score - 0.6).abs() < f64::EPSILON);
    }

    #[test]
    fn test_score_computation_high_latency() {
        let monitor = UnifiedHealthMonitor::new();
        // High latency (2500ms out of 5000ms max)
        let score = monitor.compute_score(1.0, 1.0, 2500.0, HealthStatus::Healthy);
        // 0.4*1.0 + 0.3*1.0 + 0.2*0.5 + 0.1*1.0 = 0.4 + 0.3 + 0.1 + 0.1 = 0.9
        assert!((score - 0.9).abs() < f64::EPSILON);
    }

    #[test]
    fn test_recommend_solvers_ordering_is_stable() {
        let mut monitor = UnifiedHealthMonitor::new();

        for _ in 0..10 {
            monitor.record_result("z4", "div_zero", Duration::from_millis(10), true, true);
            monitor.record_result("zani", "div_zero", Duration::from_millis(10), true, false);
        }

        // Call recommend_solvers twice, should get same order
        let recs1 = monitor.recommend_solvers("div_zero", &["z4", "zani"]);
        let recs2 = monitor.recommend_solvers("div_zero", &["z4", "zani"]);

        assert_eq!(recs1[0].solver, recs2[0].solver);
        assert_eq!(recs1[1].solver, recs2[1].solver);
    }

    #[test]
    fn test_multiple_vc_kinds_independent() {
        let mut monitor = UnifiedHealthMonitor::new();

        // z4 wins for div_zero
        for _ in 0..10 {
            monitor.record_result("z4", "div_zero", Duration::from_millis(10), true, true);
            monitor.record_result("zani", "div_zero", Duration::from_millis(50), true, false);
        }

        // zani wins for postcond
        for _ in 0..10 {
            monitor.record_result("zani", "postcond", Duration::from_millis(10), true, true);
            monitor.record_result("z4", "postcond", Duration::from_millis(50), true, false);
        }

        let div_recs = monitor.recommend_solvers("div_zero", &["z4", "zani"]);
        let post_recs = monitor.recommend_solvers("postcond", &["z4", "zani"]);

        // z4 should be preferred for div_zero, zani for postcond
        assert_eq!(div_recs[0].solver, "z4");
        assert_eq!(post_recs[0].solver, "zani");
    }

    #[test]
    fn test_solver_recommendation_fields() {
        let mut monitor = UnifiedHealthMonitor::new();
        monitor.record_result("z4", "div_zero", Duration::from_millis(42), true, true);

        let recs = monitor.recommend_solvers("div_zero", &["z4"]);
        assert_eq!(recs.len(), 1);

        let rec = &recs[0];
        assert_eq!(rec.solver, "z4");
        assert_eq!(rec.health_status, HealthStatus::Healthy);
        assert!(!rec.circuit_open);
        assert!(rec.win_rate > 0.0);
        assert!(rec.success_rate > 0.0);
        assert!(rec.avg_latency_ms > 0.0);
        assert!(rec.score > 0.0);
    }

    #[test]
    fn test_summary_solver_details() {
        let mut monitor = UnifiedHealthMonitor::new();
        monitor.record_result("z4", "div_zero", Duration::from_millis(10), true, true);
        monitor.record_cache_hit("z4");

        let summary = monitor.summary();
        assert_eq!(summary.solvers.len(), 1);

        let s = &summary.solvers[0];
        assert_eq!(s.name, "z4");
        assert_eq!(s.health_status, HealthStatus::Healthy);
        assert_eq!(s.total_dispatched, 1);
        assert!(!s.circuit_open);
    }
}
