// trust-router/routing_metrics.rs: Per-route quality evaluation and audit trail
//
// tRust: Tracks individual routing decisions with their outcomes, enabling
// post-hoc analysis of routing quality. Each decision records which solver
// was chosen, why, and what happened. Provides route quality scoring and
// JSON export for integration with trust-report.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;
use std::fmt;
use std::time::Duration;
use std::fmt::Write;

/// tRust: Why a particular solver was chosen for a VC.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum RoutingReason {
    /// Solver was chosen by the static backend plan (role-based ranking).
    BackendPlan,
    /// Solver was chosen adaptively based on historical win rates.
    AdaptiveWinRate,
    /// Solver was chosen because it was the only healthy option.
    OnlyHealthy,
    /// Solver was chosen as a fallback after the primary solver failed.
    Fallback,
    /// Solver was chosen by portfolio race (first to complete).
    PortfolioRace,
    /// Solver was chosen by CEGAR-specific dispatch.
    CegarDispatch,
    /// Solver was used due to cache hit.
    CacheHit,
}

impl fmt::Display for RoutingReason {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::BackendPlan => write!(f, "backend_plan"),
            Self::AdaptiveWinRate => write!(f, "adaptive_win_rate"),
            Self::OnlyHealthy => write!(f, "only_healthy"),
            Self::Fallback => write!(f, "fallback"),
            Self::PortfolioRace => write!(f, "portfolio_race"),
            Self::CegarDispatch => write!(f, "cegar_dispatch"),
            Self::CacheHit => write!(f, "cache_hit"),
        }
    }
}

/// tRust: Outcome of a routing decision.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum RoutingOutcome {
    /// Solver proved the VC.
    Proved,
    /// Solver found a counterexample.
    Failed,
    /// Solver returned unknown.
    Unknown,
    /// Solver timed out.
    Timeout,
    /// Solver encountered an error.
    Error,
}

impl fmt::Display for RoutingOutcome {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Proved => write!(f, "proved"),
            Self::Failed => write!(f, "failed"),
            Self::Unknown => write!(f, "unknown"),
            Self::Timeout => write!(f, "timeout"),
            Self::Error => write!(f, "error"),
        }
    }
}

/// tRust: A single routing decision record.
#[derive(Debug, Clone)]
pub struct RoutingDecision {
    /// VC kind key (same as used in adaptive history).
    pub vc_kind_key: String,
    /// Function name from the VC.
    pub function: String,
    /// Solver that was selected.
    pub solver: String,
    /// Why this solver was selected.
    pub reason: RoutingReason,
    /// What happened.
    pub outcome: RoutingOutcome,
    /// Wall-clock time of the solver invocation.
    pub duration: Duration,
    /// Sequence number (monotonically increasing).
    pub sequence: u64,
}

/// tRust: Aggregate quality metrics for a specific route (vc_kind -> solver pair).
#[derive(Debug, Clone)]
pub struct RouteQuality {
    /// VC kind key.
    pub vc_kind_key: String,
    /// Solver name.
    pub solver: String,
    /// Total routing decisions for this route.
    pub total: u64,
    /// Number of proved outcomes.
    pub proved: u64,
    /// Number of failed outcomes (counterexample found).
    pub failed: u64,
    /// Number of unknown outcomes.
    pub unknown: u64,
    /// Number of timeout outcomes.
    pub timeouts: u64,
    /// Number of error outcomes.
    pub errors: u64,
    /// Mean latency in ms.
    pub mean_latency_ms: f64,
    /// Min latency in ms.
    pub min_latency_ms: f64,
    /// Max latency in ms.
    pub max_latency_ms: f64,
}

impl RouteQuality {
    /// Definitive rate: fraction of decisions that produced Proved or Failed.
    #[must_use]
    pub fn definitive_rate(&self) -> f64 {
        if self.total == 0 {
            0.0
        } else {
            (self.proved + self.failed) as f64 / self.total as f64
        }
    }

    /// Error rate: fraction of decisions that produced Timeout or Error.
    #[must_use]
    pub fn error_rate(&self) -> f64 {
        if self.total == 0 {
            0.0
        } else {
            (self.timeouts + self.errors) as f64 / self.total as f64
        }
    }
}

/// tRust: Collects routing decisions and computes route quality metrics.
///
/// Each routing decision is recorded with its reason and outcome.
/// Quality metrics are computed on-demand from the recorded decisions.
pub struct RoutingMetricsCollector {
    /// All recorded decisions in chronological order.
    decisions: Vec<RoutingDecision>,
    /// Next sequence number.
    next_sequence: u64,
    /// Maximum number of decisions to retain (oldest are evicted). 0 = unlimited.
    max_decisions: usize,
}

impl RoutingMetricsCollector {
    /// Create a new collector with unlimited history.
    #[must_use]
    pub fn new() -> Self {
        Self {
            decisions: Vec::new(),
            next_sequence: 0,
            max_decisions: 0,
        }
    }

    /// Create a new collector with a maximum history size.
    #[must_use]
    pub fn with_capacity(max_decisions: usize) -> Self {
        Self {
            decisions: Vec::with_capacity(max_decisions.min(1024)),
            next_sequence: 0,
            max_decisions,
        }
    }

    /// Record a routing decision.
    pub fn record(
        &mut self,
        vc_kind_key: &str,
        function: &str,
        solver: &str,
        reason: RoutingReason,
        outcome: RoutingOutcome,
        duration: Duration,
    ) {
        let decision = RoutingDecision {
            vc_kind_key: vc_kind_key.to_string(),
            function: function.to_string(),
            solver: solver.to_string(),
            reason,
            outcome,
            duration,
            sequence: self.next_sequence,
        };
        self.next_sequence += 1;

        self.decisions.push(decision);

        // Evict oldest if over budget
        if self.max_decisions > 0 && self.decisions.len() > self.max_decisions {
            self.decisions.remove(0);
        }
    }

    /// Total number of recorded decisions.
    #[must_use]
    pub fn total_decisions(&self) -> u64 {
        self.decisions.len() as u64
    }

    /// Get route quality for a specific (vc_kind, solver) pair.
    #[must_use]
    pub fn route_quality(&self, vc_kind_key: &str, solver: &str) -> RouteQuality {
        let matching: Vec<&RoutingDecision> = self
            .decisions
            .iter()
            .filter(|d| d.vc_kind_key == vc_kind_key && d.solver == solver)
            .collect();

        let total = matching.len() as u64;

        let mut proved = 0u64;
        let mut failed = 0u64;
        let mut unknown = 0u64;
        let mut timeouts = 0u64;
        let mut errors = 0u64;
        let mut sum_ms = 0.0f64;
        let mut min_ms = f64::INFINITY;
        let mut max_ms = f64::NEG_INFINITY;

        for d in &matching {
            match d.outcome {
                RoutingOutcome::Proved => proved += 1,
                RoutingOutcome::Failed => failed += 1,
                RoutingOutcome::Unknown => unknown += 1,
                RoutingOutcome::Timeout => timeouts += 1,
                RoutingOutcome::Error => errors += 1,
            }

            let ms = d.duration.as_secs_f64() * 1000.0;
            sum_ms += ms;
            if ms < min_ms {
                min_ms = ms;
            }
            if ms > max_ms {
                max_ms = ms;
            }
        }

        RouteQuality {
            vc_kind_key: vc_kind_key.to_string(),
            solver: solver.to_string(),
            total,
            proved,
            failed,
            unknown,
            timeouts,
            errors,
            mean_latency_ms: if total == 0 { 0.0 } else { sum_ms / total as f64 },
            min_latency_ms: if total == 0 { 0.0 } else { min_ms },
            max_latency_ms: if total == 0 { 0.0 } else { max_ms },
        }
    }

    /// Get quality metrics for all observed routes.
    #[must_use]
    pub fn all_route_qualities(&self) -> Vec<RouteQuality> {
        let mut seen: Vec<(String, String)> = Vec::new();

        for d in &self.decisions {
            let key = (d.vc_kind_key.clone(), d.solver.clone());
            if !seen.contains(&key) {
                seen.push(key);
            }
        }

        seen.sort();

        seen.iter()
            .map(|(kind, solver)| self.route_quality(kind, solver))
            .collect()
    }

    /// Get routing reason distribution as (reason, count) pairs.
    #[must_use]
    pub fn reason_distribution(&self) -> Vec<(RoutingReason, u64)> {
        let mut counts: FxHashMap<RoutingReason, u64> = FxHashMap::default();
        for d in &self.decisions {
            *counts.entry(d.reason.clone()).or_insert(0) += 1;
        }

        let mut result: Vec<(RoutingReason, u64)> = counts.into_iter().collect();
        result.sort_by(|a, b| b.1.cmp(&a.1));
        result
    }

    /// Get outcome distribution as (outcome, count) pairs.
    #[must_use]
    pub fn outcome_distribution(&self) -> Vec<(RoutingOutcome, u64)> {
        let mut counts: FxHashMap<RoutingOutcome, u64> = FxHashMap::default();
        for d in &self.decisions {
            *counts.entry(d.outcome).or_insert(0) += 1;
        }

        let mut result: Vec<(RoutingOutcome, u64)> = counts.into_iter().collect();
        result.sort_by(|a, b| b.1.cmp(&a.1));
        result
    }

    /// Overall definitive rate across all decisions.
    #[must_use]
    pub fn overall_definitive_rate(&self) -> f64 {
        if self.decisions.is_empty() {
            return 0.0;
        }

        let definitive = self
            .decisions
            .iter()
            .filter(|d| {
                matches!(
                    d.outcome,
                    RoutingOutcome::Proved | RoutingOutcome::Failed
                )
            })
            .count();

        definitive as f64 / self.decisions.len() as f64
    }

    /// Get the N most recent decisions.
    #[must_use]
    pub fn recent_decisions(&self, n: usize) -> &[RoutingDecision] {
        let start = self.decisions.len().saturating_sub(n);
        &self.decisions[start..]
    }

    /// Export all route quality metrics as a JSON string.
    ///
    /// Hand-rolled JSON to avoid serde dependency on the hot path.
    #[must_use]
    pub fn json_export(&self) -> String {
        let mut out = String::with_capacity(1024);
        out.push('{');

        let _ = write!(out, 
            "\"total_decisions\":{},\"overall_definitive_rate\":{:.4}",
            self.total_decisions(),
            self.overall_definitive_rate()
        );

        // Reason distribution
        out.push_str(",\"reason_distribution\":{");
        let reasons = self.reason_distribution();
        for (i, (reason, count)) in reasons.iter().enumerate() {
            if i > 0 {
                out.push(',');
            }
            let _ = write!(out, "\"{}\":{}", reason, count);
        }
        out.push('}');

        // Outcome distribution
        out.push_str(",\"outcome_distribution\":{");
        let outcomes = self.outcome_distribution();
        for (i, (outcome, count)) in outcomes.iter().enumerate() {
            if i > 0 {
                out.push(',');
            }
            let _ = write!(out, "\"{}\":{}", outcome, count);
        }
        out.push('}');

        // Route qualities
        out.push_str(",\"routes\":[");
        let qualities = self.all_route_qualities();
        for (i, q) in qualities.iter().enumerate() {
            if i > 0 {
                out.push(',');
            }
            let _ = write!(out, 
                "{{\"vc_kind\":\"{}\",\"solver\":\"{}\",\"total\":{},\"proved\":{},\"failed\":{},\"unknown\":{},\"timeouts\":{},\"errors\":{},\"definitive_rate\":{:.4},\"error_rate\":{:.4},\"mean_latency_ms\":{:.2},\"min_latency_ms\":{:.2},\"max_latency_ms\":{:.2}}}",
                q.vc_kind_key, q.solver, q.total, q.proved, q.failed, q.unknown,
                q.timeouts, q.errors, q.definitive_rate(), q.error_rate(),
                q.mean_latency_ms, q.min_latency_ms, q.max_latency_ms
            );
        }
        out.push(']');

        out.push('}');
        out
    }

    /// Terminal-formatted summary report.
    #[must_use]
    pub fn terminal_report(&self) -> RoutingMetricsReport<'_> {
        RoutingMetricsReport { collector: self }
    }
}

impl Default for RoutingMetricsCollector {
    fn default() -> Self {
        Self::new()
    }
}

/// tRust: Terminal-formatted routing metrics report.
pub struct RoutingMetricsReport<'a> {
    collector: &'a RoutingMetricsCollector,
}

impl<'a> fmt::Display for RoutingMetricsReport<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let c = self.collector;

        writeln!(f, "=== Routing Metrics ===")?;
        writeln!(f, "Total decisions: {}", c.total_decisions())?;
        writeln!(
            f,
            "Definitive rate: {:.1}%",
            c.overall_definitive_rate() * 100.0
        )?;
        writeln!(f)?;

        // Reason distribution
        writeln!(f, "Routing reasons:")?;
        for (reason, count) in c.reason_distribution() {
            writeln!(f, "  {}: {}", reason, count)?;
        }
        writeln!(f)?;

        // Outcome distribution
        writeln!(f, "Outcomes:")?;
        for (outcome, count) in c.outcome_distribution() {
            writeln!(f, "  {}: {}", outcome, count)?;
        }
        writeln!(f)?;

        // Per-route quality
        writeln!(f, "Per-route quality:")?;
        for q in c.all_route_qualities() {
            writeln!(
                f,
                "  {} -> {}: {}/{} definitive ({:.1}%), mean={:.1}ms",
                q.vc_kind_key,
                q.solver,
                q.proved + q.failed,
                q.total,
                q.definitive_rate() * 100.0,
                q.mean_latency_ms,
            )?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_routing_metrics_collector_empty() {
        let collector = RoutingMetricsCollector::new();
        assert_eq!(collector.total_decisions(), 0);
        assert_eq!(collector.overall_definitive_rate(), 0.0);
        assert!(collector.all_route_qualities().is_empty());
        assert!(collector.reason_distribution().is_empty());
        assert!(collector.outcome_distribution().is_empty());
    }

    #[test]
    fn test_record_and_query() {
        let mut collector = RoutingMetricsCollector::new();
        collector.record(
            "div_zero",
            "test_fn",
            "z4",
            RoutingReason::BackendPlan,
            RoutingOutcome::Proved,
            Duration::from_millis(10),
        );

        assert_eq!(collector.total_decisions(), 1);

        let quality = collector.route_quality("div_zero", "z4");
        assert_eq!(quality.total, 1);
        assert_eq!(quality.proved, 1);
        assert_eq!(quality.failed, 0);
        assert!((quality.definitive_rate() - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_multiple_outcomes() {
        let mut collector = RoutingMetricsCollector::new();

        collector.record("div_zero", "fn1", "z4", RoutingReason::BackendPlan, RoutingOutcome::Proved, Duration::from_millis(10));
        collector.record("div_zero", "fn2", "z4", RoutingReason::BackendPlan, RoutingOutcome::Failed, Duration::from_millis(20));
        collector.record("div_zero", "fn3", "z4", RoutingReason::BackendPlan, RoutingOutcome::Unknown, Duration::from_millis(30));
        collector.record("div_zero", "fn4", "z4", RoutingReason::BackendPlan, RoutingOutcome::Timeout, Duration::from_millis(5000));
        collector.record("div_zero", "fn5", "z4", RoutingReason::BackendPlan, RoutingOutcome::Error, Duration::from_millis(1));

        let quality = collector.route_quality("div_zero", "z4");
        assert_eq!(quality.total, 5);
        assert_eq!(quality.proved, 1);
        assert_eq!(quality.failed, 1);
        assert_eq!(quality.unknown, 1);
        assert_eq!(quality.timeouts, 1);
        assert_eq!(quality.errors, 1);
        assert!((quality.definitive_rate() - 0.4).abs() < f64::EPSILON);
        assert!((quality.error_rate() - 0.4).abs() < f64::EPSILON);
    }

    #[test]
    fn test_route_quality_latency_stats() {
        let mut collector = RoutingMetricsCollector::new();

        collector.record("div_zero", "fn1", "z4", RoutingReason::BackendPlan, RoutingOutcome::Proved, Duration::from_millis(10));
        collector.record("div_zero", "fn2", "z4", RoutingReason::BackendPlan, RoutingOutcome::Proved, Duration::from_millis(30));
        collector.record("div_zero", "fn3", "z4", RoutingReason::BackendPlan, RoutingOutcome::Proved, Duration::from_millis(20));

        let quality = collector.route_quality("div_zero", "z4");
        assert!((quality.mean_latency_ms - 20.0).abs() < 0.1);
        assert!((quality.min_latency_ms - 10.0).abs() < 0.1);
        assert!((quality.max_latency_ms - 30.0).abs() < 0.1);
    }

    #[test]
    fn test_route_quality_empty_route() {
        let collector = RoutingMetricsCollector::new();
        let quality = collector.route_quality("div_zero", "z4");
        assert_eq!(quality.total, 0);
        assert_eq!(quality.definitive_rate(), 0.0);
        assert_eq!(quality.error_rate(), 0.0);
        assert_eq!(quality.mean_latency_ms, 0.0);
    }

    #[test]
    fn test_all_route_qualities() {
        let mut collector = RoutingMetricsCollector::new();

        collector.record("div_zero", "fn1", "z4", RoutingReason::BackendPlan, RoutingOutcome::Proved, Duration::from_millis(10));
        collector.record("div_zero", "fn2", "zani", RoutingReason::AdaptiveWinRate, RoutingOutcome::Proved, Duration::from_millis(20));
        collector.record("postcond", "fn3", "z4", RoutingReason::BackendPlan, RoutingOutcome::Failed, Duration::from_millis(15));

        let qualities = collector.all_route_qualities();
        assert_eq!(qualities.len(), 3); // 3 distinct (kind, solver) pairs
    }

    #[test]
    fn test_reason_distribution() {
        let mut collector = RoutingMetricsCollector::new();

        collector.record("div_zero", "fn1", "z4", RoutingReason::BackendPlan, RoutingOutcome::Proved, Duration::from_millis(10));
        collector.record("div_zero", "fn2", "z4", RoutingReason::BackendPlan, RoutingOutcome::Proved, Duration::from_millis(10));
        collector.record("div_zero", "fn3", "z4", RoutingReason::AdaptiveWinRate, RoutingOutcome::Proved, Duration::from_millis(10));

        let reasons = collector.reason_distribution();
        assert_eq!(reasons.len(), 2);
        // BackendPlan should be first (count=2)
        assert_eq!(reasons[0].0, RoutingReason::BackendPlan);
        assert_eq!(reasons[0].1, 2);
        assert_eq!(reasons[1].0, RoutingReason::AdaptiveWinRate);
        assert_eq!(reasons[1].1, 1);
    }

    #[test]
    fn test_outcome_distribution() {
        let mut collector = RoutingMetricsCollector::new();

        collector.record("div_zero", "fn1", "z4", RoutingReason::BackendPlan, RoutingOutcome::Proved, Duration::from_millis(10));
        collector.record("div_zero", "fn2", "z4", RoutingReason::BackendPlan, RoutingOutcome::Proved, Duration::from_millis(10));
        collector.record("div_zero", "fn3", "z4", RoutingReason::BackendPlan, RoutingOutcome::Timeout, Duration::from_millis(5000));

        let outcomes = collector.outcome_distribution();
        assert_eq!(outcomes.len(), 2);
        assert_eq!(outcomes[0].0, RoutingOutcome::Proved);
        assert_eq!(outcomes[0].1, 2);
    }

    #[test]
    fn test_overall_definitive_rate() {
        let mut collector = RoutingMetricsCollector::new();

        collector.record("div_zero", "fn1", "z4", RoutingReason::BackendPlan, RoutingOutcome::Proved, Duration::from_millis(10));
        collector.record("div_zero", "fn2", "z4", RoutingReason::BackendPlan, RoutingOutcome::Failed, Duration::from_millis(10));
        collector.record("div_zero", "fn3", "z4", RoutingReason::BackendPlan, RoutingOutcome::Unknown, Duration::from_millis(10));
        collector.record("div_zero", "fn4", "z4", RoutingReason::BackendPlan, RoutingOutcome::Timeout, Duration::from_millis(10));

        // 2 definitive (Proved + Failed) out of 4
        assert!((collector.overall_definitive_rate() - 0.5).abs() < f64::EPSILON);
    }

    #[test]
    fn test_recent_decisions() {
        let mut collector = RoutingMetricsCollector::new();

        for i in 0..10 {
            collector.record(
                "div_zero",
                &format!("fn_{i}"),
                "z4",
                RoutingReason::BackendPlan,
                RoutingOutcome::Proved,
                Duration::from_millis(10),
            );
        }

        let recent = collector.recent_decisions(3);
        assert_eq!(recent.len(), 3);
        assert_eq!(recent[0].sequence, 7);
        assert_eq!(recent[1].sequence, 8);
        assert_eq!(recent[2].sequence, 9);
    }

    #[test]
    fn test_recent_decisions_more_than_total() {
        let mut collector = RoutingMetricsCollector::new();
        collector.record("div_zero", "fn1", "z4", RoutingReason::BackendPlan, RoutingOutcome::Proved, Duration::from_millis(10));

        let recent = collector.recent_decisions(100);
        assert_eq!(recent.len(), 1);
    }

    #[test]
    fn test_capacity_eviction() {
        let mut collector = RoutingMetricsCollector::with_capacity(3);

        for i in 0..5 {
            collector.record(
                "div_zero",
                &format!("fn_{i}"),
                "z4",
                RoutingReason::BackendPlan,
                RoutingOutcome::Proved,
                Duration::from_millis(10),
            );
        }

        // Should only have 3 decisions (most recent)
        assert_eq!(collector.decisions.len(), 3);
        assert_eq!(collector.decisions[0].sequence, 2);
        assert_eq!(collector.decisions[2].sequence, 4);
    }

    #[test]
    fn test_json_export_empty() {
        let collector = RoutingMetricsCollector::new();
        let json = collector.json_export();
        assert!(json.contains("\"total_decisions\":0"));
        assert!(json.contains("\"overall_definitive_rate\":0.0000"));
        assert!(json.contains("\"routes\":[]"));
    }

    #[test]
    fn test_json_export_with_data() {
        let mut collector = RoutingMetricsCollector::new();

        collector.record("div_zero", "fn1", "z4", RoutingReason::BackendPlan, RoutingOutcome::Proved, Duration::from_millis(10));
        collector.record("div_zero", "fn2", "z4", RoutingReason::AdaptiveWinRate, RoutingOutcome::Failed, Duration::from_millis(20));

        let json = collector.json_export();
        assert!(json.contains("\"total_decisions\":2"));
        assert!(json.contains("\"overall_definitive_rate\":1.0000"));
        assert!(json.contains("\"vc_kind\":\"div_zero\""));
        assert!(json.contains("\"solver\":\"z4\""));
        assert!(json.contains("\"proved\":1"));
        assert!(json.contains("\"failed\":1"));

        // Reason distribution
        assert!(json.contains("\"reason_distribution\":{"));
        assert!(json.contains("\"backend_plan\":1"));
        assert!(json.contains("\"adaptive_win_rate\":1"));

        // Outcome distribution
        assert!(json.contains("\"outcome_distribution\":{"));

        // Valid JSON structure
        assert!(json.starts_with('{'));
        assert!(json.ends_with('}'));
    }

    #[test]
    fn test_terminal_report_format() {
        let mut collector = RoutingMetricsCollector::new();

        collector.record("div_zero", "fn1", "z4", RoutingReason::BackendPlan, RoutingOutcome::Proved, Duration::from_millis(10));

        let report = format!("{}", collector.terminal_report());
        assert!(report.contains("Routing Metrics"));
        assert!(report.contains("Total decisions: 1"));
        assert!(report.contains("Definitive rate: 100.0%"));
        assert!(report.contains("backend_plan"));
        assert!(report.contains("div_zero"));
    }

    #[test]
    fn test_terminal_report_empty() {
        let collector = RoutingMetricsCollector::new();
        let report = format!("{}", collector.terminal_report());
        assert!(report.contains("Total decisions: 0"));
        assert!(report.contains("Definitive rate: 0.0%"));
    }

    #[test]
    fn test_routing_reason_display() {
        assert_eq!(format!("{}", RoutingReason::BackendPlan), "backend_plan");
        assert_eq!(format!("{}", RoutingReason::AdaptiveWinRate), "adaptive_win_rate");
        assert_eq!(format!("{}", RoutingReason::OnlyHealthy), "only_healthy");
        assert_eq!(format!("{}", RoutingReason::Fallback), "fallback");
        assert_eq!(format!("{}", RoutingReason::PortfolioRace), "portfolio_race");
        assert_eq!(format!("{}", RoutingReason::CegarDispatch), "cegar_dispatch");
        assert_eq!(format!("{}", RoutingReason::CacheHit), "cache_hit");
    }

    #[test]
    fn test_routing_outcome_display() {
        assert_eq!(format!("{}", RoutingOutcome::Proved), "proved");
        assert_eq!(format!("{}", RoutingOutcome::Failed), "failed");
        assert_eq!(format!("{}", RoutingOutcome::Unknown), "unknown");
        assert_eq!(format!("{}", RoutingOutcome::Timeout), "timeout");
        assert_eq!(format!("{}", RoutingOutcome::Error), "error");
    }

    #[test]
    fn test_routing_decision_sequence_monotonic() {
        let mut collector = RoutingMetricsCollector::new();

        for i in 0..5 {
            collector.record(
                "div_zero",
                &format!("fn_{i}"),
                "z4",
                RoutingReason::BackendPlan,
                RoutingOutcome::Proved,
                Duration::from_millis(10),
            );
        }

        for (i, d) in collector.decisions.iter().enumerate() {
            assert_eq!(d.sequence, i as u64);
        }
    }

    #[test]
    fn test_multiple_solvers_same_kind() {
        let mut collector = RoutingMetricsCollector::new();

        collector.record("div_zero", "fn1", "z4", RoutingReason::BackendPlan, RoutingOutcome::Proved, Duration::from_millis(10));
        collector.record("div_zero", "fn2", "zani", RoutingReason::BackendPlan, RoutingOutcome::Unknown, Duration::from_millis(50));
        collector.record("div_zero", "fn3", "z4", RoutingReason::BackendPlan, RoutingOutcome::Proved, Duration::from_millis(15));

        let z4_quality = collector.route_quality("div_zero", "z4");
        assert_eq!(z4_quality.total, 2);
        assert_eq!(z4_quality.proved, 2);
        assert!((z4_quality.definitive_rate() - 1.0).abs() < f64::EPSILON);

        let zani_quality = collector.route_quality("div_zero", "zani");
        assert_eq!(zani_quality.total, 1);
        assert_eq!(zani_quality.unknown, 1);
        assert_eq!(zani_quality.definitive_rate(), 0.0);
    }

    #[test]
    fn test_routing_reason_equality() {
        assert_eq!(RoutingReason::BackendPlan, RoutingReason::BackendPlan);
        assert_ne!(RoutingReason::BackendPlan, RoutingReason::Fallback);
    }

    #[test]
    fn test_routing_outcome_equality() {
        assert_eq!(RoutingOutcome::Proved, RoutingOutcome::Proved);
        assert_ne!(RoutingOutcome::Proved, RoutingOutcome::Failed);
    }
}
