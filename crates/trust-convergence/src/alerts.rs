// trust-convergence/alerts.rs: Alert conditions for the convergence pipeline.
//
// Defines alert rules for stall detection, regression, timeout budget
// exhaustion, and CEGAR refinement limits. Evaluates conditions against
// convergence metrics and emits structured alerts for reporting.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};

use crate::analysis::{ConvergencePattern, detect_pattern};
use crate::metrics::ConvergenceMetrics;

// ---------------------------------------------------------------------------
// Alert types
// ---------------------------------------------------------------------------

/// Severity levels for convergence alerts.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub(crate) enum Severity {
    /// Informational: no action required.
    Info,
    /// Warning: investigate soon.
    Warning,
    /// Critical: immediate attention required.
    Critical,
}

/// Category of alert for filtering and routing.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub(crate) enum AlertCategory {
    /// Proving rate has stalled.
    Stall,
    /// VCs proven decreased between iterations.
    Regression,
    /// Time budget exceeded.
    TimeoutBudget,
    /// CEGAR refinement loop is not converging.
    CegarRefinement,
    /// Cache hit rate dropped significantly.
    CacheDegradation,
    /// Convergence pattern changed unfavorably.
    PatternShift,
}

/// A structured convergence alert.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub(crate) struct ConvergenceAlert {
    /// Alert category.
    pub category: AlertCategory,
    /// Severity level.
    pub severity: Severity,
    /// Human-readable summary.
    pub message: String,
    /// Iteration at which the alert was triggered (latest observed).
    pub iteration: u32,
    /// Optional additional context (metric values, thresholds, etc.).
    pub context: AlertContext,
}

/// Additional context attached to an alert.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[non_exhaustive]
pub(crate) enum AlertContext {
    /// Context for stall alerts.
    Stall {
        consecutive_flat: u32,
        threshold: u32,
    },
    /// Context for regression alerts.
    Regression {
        from_value: u32,
        to_value: u32,
        from_iteration: u32,
        to_iteration: u32,
    },
    /// Context for timeout budget alerts.
    TimeoutBudget {
        total_ms: u64,
        budget_ms: u64,
        overshoot_pct: f64,
    },
    /// Context for CEGAR refinement alerts.
    CegarRefinement {
        refinement_count: u32,
        max_refinements: u32,
    },
    /// Context for cache degradation alerts.
    CacheDegradation {
        previous_rate: f64,
        current_rate: f64,
        drop_pct: f64,
    },
    /// Context for pattern shift alerts.
    PatternShift {
        previous_pattern: String,
        current_pattern: String,
    },
    /// No additional context.
    None,
}

// ---------------------------------------------------------------------------
// Alert configuration
// ---------------------------------------------------------------------------

/// Configurable thresholds for alert evaluation.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct AlertConfig {
    /// Number of consecutive flat iterations to trigger stall alert.
    pub stall_threshold: u32,
    /// Time budget in milliseconds.
    pub time_budget_ms: u64,
    /// Maximum CEGAR refinement iterations before alert.
    pub max_cegar_refinements: u32,
    /// Cache hit rate drop percentage to trigger degradation alert (0.0..=1.0).
    pub cache_drop_threshold: f64,
}

impl Default for AlertConfig {
    fn default() -> Self {
        Self {
            stall_threshold: 3,
            time_budget_ms: 600_000, // 10 minutes
            max_cegar_refinements: 20,
            cache_drop_threshold: 0.2, // 20% drop
        }
    }
}

// ---------------------------------------------------------------------------
// Alert evaluator
// ---------------------------------------------------------------------------

/// Evaluates metrics against alert rules and produces alerts.
#[derive(Debug, Clone)]
pub(crate) struct AlertEvaluator {
    config: AlertConfig,
    /// Previous pattern for shift detection.
    previous_pattern: Option<ConvergencePattern>,
}

impl AlertEvaluator {
    /// Create an evaluator with the given config.
    #[must_use]
    pub fn new(config: AlertConfig) -> Self {
        Self {
            config,
            previous_pattern: None,
        }
    }

    /// Create an evaluator with default config.
    #[must_use]
    pub fn with_defaults() -> Self {
        Self::new(AlertConfig::default())
    }

    /// Evaluate all alert rules against the given metrics.
    ///
    /// Updates internal state for pattern shift detection across calls.
    pub fn evaluate(&mut self, metrics: &ConvergenceMetrics) -> Vec<ConvergenceAlert> {
        let mut alerts = Vec::new();
        let iteration = metrics.iterations.saturating_sub(1);

        self.check_stall(metrics, iteration, &mut alerts);
        self.check_regression(metrics, iteration, &mut alerts);
        self.check_timeout_budget(metrics, iteration, &mut alerts);
        self.check_cache_degradation(metrics, iteration, &mut alerts);
        self.check_pattern_shift(metrics, iteration, &mut alerts);

        // Sort by severity (critical first)
        alerts.sort_by(|a, b| b.severity.cmp(&a.severity));
        alerts
    }

    fn check_stall(
        &self,
        metrics: &ConvergenceMetrics,
        iteration: u32,
        alerts: &mut Vec<ConvergenceAlert>,
    ) {
        let vcs = &metrics.vcs_proven_per_iteration;
        if vcs.len() < 2 {
            return;
        }

        let trailing_flat = count_trailing_flat(vcs);
        if trailing_flat >= self.config.stall_threshold {
            let severity = if trailing_flat >= self.config.stall_threshold * 2 {
                Severity::Critical
            } else {
                Severity::Warning
            };
            alerts.push(ConvergenceAlert {
                category: AlertCategory::Stall,
                severity,
                message: format!(
                    "Proving rate stalled for {} consecutive iterations (threshold: {})",
                    trailing_flat, self.config.stall_threshold
                ),
                iteration,
                context: AlertContext::Stall {
                    consecutive_flat: trailing_flat,
                    threshold: self.config.stall_threshold,
                },
            });
        }
    }

    fn check_regression(
        &self,
        metrics: &ConvergenceMetrics,
        iteration: u32,
        alerts: &mut Vec<ConvergenceAlert>,
    ) {
        let vcs = &metrics.vcs_proven_per_iteration;
        if vcs.len() < 2 {
            return;
        }

        // Check the most recent transition
        let len = vcs.len();
        let prev = vcs[len - 2];
        let curr = vcs[len - 1];
        if curr < prev {
            alerts.push(ConvergenceAlert {
                category: AlertCategory::Regression,
                severity: Severity::Warning,
                message: format!(
                    "VCs proven decreased from {} to {} (iteration {} -> {})",
                    prev,
                    curr,
                    len - 2,
                    len - 1
                ),
                iteration,
                context: AlertContext::Regression {
                    from_value: prev,
                    to_value: curr,
                    from_iteration: (len - 2) as u32,
                    to_iteration: (len - 1) as u32,
                },
            });
        }
    }

    fn check_timeout_budget(
        &self,
        metrics: &ConvergenceMetrics,
        iteration: u32,
        alerts: &mut Vec<ConvergenceAlert>,
    ) {
        let total_ms: u64 = metrics.time_per_iteration.iter().sum();
        if total_ms > self.config.time_budget_ms {
            let overshoot_pct =
                (total_ms as f64 - self.config.time_budget_ms as f64) / self.config.time_budget_ms as f64 * 100.0;
            alerts.push(ConvergenceAlert {
                category: AlertCategory::TimeoutBudget,
                severity: Severity::Critical,
                message: format!(
                    "Time budget exceeded: {}ms / {}ms ({:.1}% over)",
                    total_ms, self.config.time_budget_ms, overshoot_pct
                ),
                iteration,
                context: AlertContext::TimeoutBudget {
                    total_ms,
                    budget_ms: self.config.time_budget_ms,
                    overshoot_pct,
                },
            });
        }
    }

    fn check_cache_degradation(
        &self,
        metrics: &ConvergenceMetrics,
        iteration: u32,
        alerts: &mut Vec<ConvergenceAlert>,
    ) {
        let rates = &metrics.cache_hit_rate_per_iteration;
        if rates.len() < 2 {
            return;
        }

        let prev = rates[rates.len() - 2];
        let curr = rates[rates.len() - 1];
        let drop = prev - curr;

        if drop > self.config.cache_drop_threshold && prev > 0.0 {
            let drop_pct = drop / prev * 100.0;
            alerts.push(ConvergenceAlert {
                category: AlertCategory::CacheDegradation,
                severity: Severity::Warning,
                message: format!(
                    "Cache hit rate dropped from {:.0}% to {:.0}% ({:.1}% decrease)",
                    prev * 100.0,
                    curr * 100.0,
                    drop_pct
                ),
                iteration,
                context: AlertContext::CacheDegradation {
                    previous_rate: prev,
                    current_rate: curr,
                    drop_pct,
                },
            });
        }
    }

    fn check_pattern_shift(
        &mut self,
        metrics: &ConvergenceMetrics,
        iteration: u32,
        alerts: &mut Vec<ConvergenceAlert>,
    ) {
        let pattern = detect_pattern(&metrics.vcs_proven_per_iteration);
        let current = pattern.pattern;

        if let Some(previous) = self.previous_pattern {
            let is_degradation = matches!(
                (previous, current),
                (ConvergencePattern::MonotonicImprovement, ConvergencePattern::Oscillation)
                    | (ConvergencePattern::MonotonicImprovement, ConvergencePattern::Plateau)
                    | (ConvergencePattern::MonotonicImprovement, ConvergencePattern::Divergence)
                    | (ConvergencePattern::Plateau, ConvergencePattern::Divergence)
                    | (ConvergencePattern::Oscillation, ConvergencePattern::Divergence)
            );

            if is_degradation {
                alerts.push(ConvergenceAlert {
                    category: AlertCategory::PatternShift,
                    severity: Severity::Warning,
                    message: format!(
                        "Convergence pattern degraded from {:?} to {:?}",
                        previous, current
                    ),
                    iteration,
                    context: AlertContext::PatternShift {
                        previous_pattern: format!("{previous:?}"),
                        current_pattern: format!("{current:?}"),
                    },
                });
            }
        }

        self.previous_pattern = Some(current);
    }
}

impl Default for AlertEvaluator {
    fn default() -> Self {
        Self::with_defaults()
    }
}

// ---------------------------------------------------------------------------
// Free functions for CEGAR refinement alerts
// ---------------------------------------------------------------------------

/// Check if CEGAR refinement count exceeds the configured limit.
#[must_use]
pub(crate) fn check_cegar_refinement(
    refinement_count: u32,
    config: &AlertConfig,
    iteration: u32,
) -> Option<ConvergenceAlert> {
    if refinement_count >= config.max_cegar_refinements {
        Some(ConvergenceAlert {
            category: AlertCategory::CegarRefinement,
            severity: if refinement_count >= config.max_cegar_refinements * 2 {
                Severity::Critical
            } else {
                Severity::Warning
            },
            message: format!(
                "CEGAR refinement count ({}) reached limit ({})",
                refinement_count, config.max_cegar_refinements
            ),
            iteration,
            context: AlertContext::CegarRefinement {
                refinement_count,
                max_refinements: config.max_cegar_refinements,
            },
        })
    } else {
        None
    }
}

// ---------------------------------------------------------------------------
// Private helpers
// ---------------------------------------------------------------------------

/// Count trailing consecutive iterations where VCs proven equals the last value.
fn count_trailing_flat(vcs_proven: &[u32]) -> u32 {
    if vcs_proven.len() < 2 {
        return 0;
    }
    let last = *vcs_proven.last().unwrap_or(&0);
    let mut count = 1u32;
    for &v in vcs_proven.iter().rev().skip(1) {
        if v == last {
            count += 1;
        } else {
            break;
        }
    }
    if count < 2 { 0 } else { count }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use trust_types::fx::FxHashMap;

    use super::*;

    fn make_metrics(vcs_proven: Vec<u32>, times: Vec<u64>, cache_rates: Vec<f64>) -> ConvergenceMetrics {
        ConvergenceMetrics {
            iterations: vcs_proven.len() as u32,
            time_per_iteration: times,
            vcs_proven_per_iteration: vcs_proven,
            strengthening_proposals_per_iteration: vec![],
            cache_hit_rate_per_iteration: cache_rates,
            solver_time_totals: FxHashMap::default(),
            vc_kind_failure_totals: FxHashMap::default(),
            function_retry_totals: FxHashMap::default(),
        }
    }

    // -- Stall detection --

    #[test]
    fn test_stall_detected_at_threshold() {
        let mut eval = AlertEvaluator::new(AlertConfig {
            stall_threshold: 3,
            ..AlertConfig::default()
        });
        let metrics = make_metrics(vec![5, 5, 5, 5], vec![100; 4], vec![0.5; 4]);
        let alerts = eval.evaluate(&metrics);
        let stall = alerts.iter().find(|a| a.category == AlertCategory::Stall);
        assert!(stall.is_some(), "should detect stall");
        assert_eq!(stall.unwrap().severity, Severity::Warning);
    }

    #[test]
    fn test_stall_critical_at_double_threshold() {
        let mut eval = AlertEvaluator::new(AlertConfig {
            stall_threshold: 2,
            ..AlertConfig::default()
        });
        let metrics = make_metrics(vec![5; 5], vec![100; 5], vec![0.5; 5]);
        let alerts = eval.evaluate(&metrics);
        let stall = alerts.iter().find(|a| a.category == AlertCategory::Stall);
        assert!(stall.is_some());
        assert_eq!(stall.unwrap().severity, Severity::Critical);
    }

    #[test]
    fn test_no_stall_when_improving() {
        let mut eval = AlertEvaluator::with_defaults();
        let metrics = make_metrics(vec![2, 4, 6, 8], vec![100; 4], vec![0.5; 4]);
        let alerts = eval.evaluate(&metrics);
        assert!(!alerts.iter().any(|a| a.category == AlertCategory::Stall));
    }

    // -- Regression --

    #[test]
    fn test_regression_detected() {
        let mut eval = AlertEvaluator::with_defaults();
        let metrics = make_metrics(vec![5, 7, 4], vec![100; 3], vec![0.5; 3]);
        let alerts = eval.evaluate(&metrics);
        let reg = alerts.iter().find(|a| a.category == AlertCategory::Regression);
        assert!(reg.is_some(), "should detect regression");
        assert_eq!(reg.unwrap().severity, Severity::Warning);
    }

    #[test]
    fn test_no_regression_when_improving() {
        let mut eval = AlertEvaluator::with_defaults();
        let metrics = make_metrics(vec![3, 5, 7], vec![100; 3], vec![0.5; 3]);
        let alerts = eval.evaluate(&metrics);
        assert!(!alerts.iter().any(|a| a.category == AlertCategory::Regression));
    }

    // -- Timeout budget --

    #[test]
    fn test_timeout_budget_exceeded() {
        let mut eval = AlertEvaluator::new(AlertConfig {
            time_budget_ms: 500,
            ..AlertConfig::default()
        });
        let metrics = make_metrics(vec![5, 5], vec![300, 400], vec![0.5; 2]);
        let alerts = eval.evaluate(&metrics);
        let budget = alerts.iter().find(|a| a.category == AlertCategory::TimeoutBudget);
        assert!(budget.is_some());
        assert_eq!(budget.unwrap().severity, Severity::Critical);
        match &budget.unwrap().context {
            AlertContext::TimeoutBudget { total_ms, budget_ms, overshoot_pct } => {
                assert_eq!(*total_ms, 700);
                assert_eq!(*budget_ms, 500);
                assert!(*overshoot_pct > 0.0);
            }
            _ => panic!("wrong context type"),
        }
    }

    #[test]
    fn test_timeout_budget_within_limit() {
        let mut eval = AlertEvaluator::new(AlertConfig {
            time_budget_ms: 1000,
            ..AlertConfig::default()
        });
        let metrics = make_metrics(vec![5], vec![500], vec![0.5]);
        let alerts = eval.evaluate(&metrics);
        assert!(!alerts.iter().any(|a| a.category == AlertCategory::TimeoutBudget));
    }

    // -- Cache degradation --

    #[test]
    fn test_cache_degradation_detected() {
        let mut eval = AlertEvaluator::new(AlertConfig {
            cache_drop_threshold: 0.1,
            ..AlertConfig::default()
        });
        let metrics = make_metrics(vec![5, 5], vec![100; 2], vec![0.8, 0.5]);
        let alerts = eval.evaluate(&metrics);
        let cache = alerts.iter().find(|a| a.category == AlertCategory::CacheDegradation);
        assert!(cache.is_some(), "should detect cache degradation");
    }

    #[test]
    fn test_no_cache_degradation_when_improving() {
        let mut eval = AlertEvaluator::with_defaults();
        let metrics = make_metrics(vec![5, 5], vec![100; 2], vec![0.3, 0.7]);
        let alerts = eval.evaluate(&metrics);
        assert!(!alerts.iter().any(|a| a.category == AlertCategory::CacheDegradation));
    }

    // -- Pattern shift --

    #[test]
    fn test_pattern_shift_detected() {
        let mut eval = AlertEvaluator::with_defaults();

        // First evaluation: monotonic improvement
        let m1 = make_metrics(vec![2, 4, 6], vec![100; 3], vec![0.5; 3]);
        let _ = eval.evaluate(&m1);

        // Second evaluation: divergence
        let m2 = make_metrics(vec![6, 4, 2, 1], vec![100; 4], vec![0.5; 4]);
        let alerts = eval.evaluate(&m2);
        let shift = alerts.iter().find(|a| a.category == AlertCategory::PatternShift);
        assert!(shift.is_some(), "should detect pattern degradation");
    }

    #[test]
    fn test_no_pattern_shift_on_first_eval() {
        let mut eval = AlertEvaluator::with_defaults();
        let metrics = make_metrics(vec![2, 4, 6], vec![100; 3], vec![0.5; 3]);
        let alerts = eval.evaluate(&metrics);
        assert!(!alerts.iter().any(|a| a.category == AlertCategory::PatternShift));
    }

    // -- CEGAR refinement --

    #[test]
    fn test_cegar_refinement_alert() {
        let config = AlertConfig {
            max_cegar_refinements: 10,
            ..AlertConfig::default()
        };
        let alert = check_cegar_refinement(15, &config, 5);
        assert!(alert.is_some());
        let alert = alert.unwrap();
        assert_eq!(alert.category, AlertCategory::CegarRefinement);
        assert_eq!(alert.severity, Severity::Warning);
    }

    #[test]
    fn test_cegar_refinement_critical() {
        let config = AlertConfig {
            max_cegar_refinements: 10,
            ..AlertConfig::default()
        };
        let alert = check_cegar_refinement(25, &config, 5);
        assert!(alert.is_some());
        assert_eq!(alert.unwrap().severity, Severity::Critical);
    }

    #[test]
    fn test_cegar_refinement_within_limit() {
        let config = AlertConfig::default();
        let alert = check_cegar_refinement(5, &config, 0);
        assert!(alert.is_none());
    }

    // -- Alert sorting --

    #[test]
    fn test_alerts_sorted_by_severity() {
        let mut eval = AlertEvaluator::new(AlertConfig {
            stall_threshold: 2,
            time_budget_ms: 100,
            ..AlertConfig::default()
        });
        // Trigger both stall (warning) and budget (critical)
        let metrics = make_metrics(vec![5, 5, 5], vec![200, 200, 200], vec![0.5; 3]);
        let alerts = eval.evaluate(&metrics);
        assert!(alerts.len() >= 2);
        // Critical should come first
        assert_eq!(alerts[0].severity, Severity::Critical);
    }

    // -- Trailing flat helper --

    #[test]
    fn test_count_trailing_flat_all_same() {
        assert_eq!(count_trailing_flat(&[5, 5, 5, 5]), 4);
    }

    #[test]
    fn test_count_trailing_flat_tail_only() {
        assert_eq!(count_trailing_flat(&[3, 5, 5, 5]), 3);
    }

    #[test]
    fn test_count_trailing_flat_no_flat() {
        assert_eq!(count_trailing_flat(&[2, 4, 6]), 0);
    }

    #[test]
    fn test_count_trailing_flat_single() {
        assert_eq!(count_trailing_flat(&[5]), 0);
    }

    // -- Serialization --

    #[test]
    fn test_alert_serialization() {
        let alert = ConvergenceAlert {
            category: AlertCategory::Stall,
            severity: Severity::Warning,
            message: "test stall".to_string(),
            iteration: 5,
            context: AlertContext::Stall {
                consecutive_flat: 3,
                threshold: 3,
            },
        };
        let json = serde_json::to_string(&alert).expect("serialize");
        let deser: ConvergenceAlert = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(alert, deser);
    }

    #[test]
    fn test_alert_context_none_serialization() {
        let alert = ConvergenceAlert {
            category: AlertCategory::Regression,
            severity: Severity::Info,
            message: "test".to_string(),
            iteration: 0,
            context: AlertContext::None,
        };
        let json = serde_json::to_string(&alert).expect("serialize");
        let deser: ConvergenceAlert = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(alert, deser);
    }

    // -- Default --

    #[test]
    fn test_default_config() {
        let config = AlertConfig::default();
        assert_eq!(config.stall_threshold, 3);
        assert_eq!(config.time_budget_ms, 600_000);
        assert_eq!(config.max_cegar_refinements, 20);
        assert!((config.cache_drop_threshold - 0.2).abs() < f64::EPSILON);
    }

    #[test]
    fn test_default_evaluator() {
        let eval = AlertEvaluator::default();
        assert!(eval.previous_pattern.is_none());
    }
}
