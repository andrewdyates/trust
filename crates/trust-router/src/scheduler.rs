// trust-router/scheduler.rs: Adaptive scheduling for portfolio solver
//
// tRust: Allocates time budgets across strategies based on VC characteristics.
// Uses the CEGAR classifier score to determine how much time to give each
// strategy. High-scoring VCs get more CEGAR time; low-scoring VCs get more
// direct SMT time.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::time::Duration;

use trust_types::VerificationCondition;

use crate::cegar_classifier;
use crate::strategies::Strategy;

/// tRust: Time budget allocation for a single strategy in the portfolio.
#[derive(Debug, Clone, PartialEq)]
pub struct TimeBudget {
    /// The strategy this budget applies to.
    pub strategy: Strategy,
    /// Allocated time for this strategy.
    pub timeout: Duration,
    /// Priority (lower = higher priority, tried first in cascade mode).
    pub priority: u32,
}

/// tRust: A complete schedule: ordered list of strategies with time budgets.
#[derive(Debug, Clone)]
pub struct Schedule {
    /// Budgets ordered by priority (lowest priority number first).
    pub budgets: Vec<TimeBudget>,
    /// Total time budget across all strategies.
    pub total_budget: Duration,
}

impl Schedule {
    /// Number of strategies in this schedule.
    #[must_use]
    pub fn strategy_count(&self) -> usize {
        self.budgets.len()
    }

    /// Get the strategy names in priority order.
    #[must_use]
    pub fn strategy_names(&self) -> Vec<&'static str> {
        self.budgets.iter().map(|b| b.strategy.name()).collect()
    }

    /// Total allocated time.
    #[must_use]
    pub fn total_allocated(&self) -> Duration {
        self.budgets.iter().map(|b| b.timeout).sum()
    }
}

/// tRust: Scheduler configuration.
#[derive(Debug, Clone)]
pub struct SchedulerConfig {
    /// Total time budget for all strategies combined.
    pub total_budget: Duration,
    /// Minimum time any single strategy gets.
    pub min_strategy_time: Duration,
    /// CEGAR classifier score threshold for CEGAR-heavy allocation.
    pub cegar_threshold: u32,
    /// Fraction of budget for the primary strategy (0.0..=1.0).
    pub primary_fraction: f64,
}

impl Default for SchedulerConfig {
    fn default() -> Self {
        Self {
            total_budget: Duration::from_secs(30),
            min_strategy_time: Duration::from_millis(500),
            cegar_threshold: 30,
            primary_fraction: 0.5,
        }
    }
}

/// tRust: Build a schedule for the given VC and strategy set.
///
/// Uses the CEGAR classifier score to determine the primary strategy:
/// - High score (>= threshold): CEGAR gets the primary budget share.
/// - Low score (< threshold): DirectSMT gets the primary budget share.
///
/// Remaining budget is divided among secondary strategies proportionally.
#[must_use]
pub fn build_schedule(
    vc: &VerificationCondition,
    strategies: &[Strategy],
    config: &SchedulerConfig,
) -> Schedule {
    if strategies.is_empty() {
        return Schedule {
            budgets: Vec::new(),
            total_budget: config.total_budget,
        };
    }

    let classification = cegar_classifier::classify_with_threshold(vc, config.cegar_threshold);
    let total_ms = config.total_budget.as_millis() as f64;
    let min_ms = config.min_strategy_time.as_millis() as f64;

    // Determine primary strategy index based on classifier.
    let primary_idx = if classification.should_use_cegar {
        // Prefer CEGAR strategy if available.
        strategies
            .iter()
            .position(|s| matches!(s, Strategy::Cegar { .. }))
            .unwrap_or(0)
    } else {
        // Prefer DirectSMT if available.
        strategies
            .iter()
            .position(|s| matches!(s, Strategy::DirectSmt { .. }))
            .unwrap_or(0)
    };

    // Allocate budgets.
    let primary_ms = (total_ms * config.primary_fraction).max(min_ms);
    let remaining_ms = (total_ms - primary_ms).max(0.0);
    let secondary_count = strategies.len().saturating_sub(1);
    let per_secondary_ms = if secondary_count > 0 {
        (remaining_ms / secondary_count as f64).max(min_ms)
    } else {
        0.0
    };

    // Scale CEGAR budget based on classifier score.
    let cegar_bonus = if classification.should_use_cegar {
        // Give CEGAR strategies a bonus proportional to their score.
        (classification.score as f64 / 100.0).min(0.5)
    } else {
        0.0
    };

    let mut budgets: Vec<TimeBudget> = strategies
        .iter()
        .enumerate()
        .map(|(idx, strategy)| {
            let base_ms = if idx == primary_idx {
                primary_ms
            } else {
                per_secondary_ms
            };

            // Apply CEGAR bonus to CEGAR strategies.
            let adjusted_ms = if matches!(strategy, Strategy::Cegar { .. }) {
                base_ms * (1.0 + cegar_bonus)
            } else {
                base_ms
            };

            let timeout_ms = adjusted_ms.max(min_ms) as u64;

            TimeBudget {
                strategy: strategy.clone(),
                timeout: Duration::from_millis(timeout_ms),
                priority: if idx == primary_idx { 0 } else { (idx + 1) as u32 },
            }
        })
        .collect();

    // Sort by priority.
    budgets.sort_by_key(|b| b.priority);

    Schedule {
        budgets,
        total_budget: config.total_budget,
    }
}

/// tRust: Build a schedule using default configuration.
#[must_use]
pub fn schedule_default(
    vc: &VerificationCondition,
    strategies: &[Strategy],
) -> Schedule {
    build_schedule(vc, strategies, &SchedulerConfig::default())
}

#[cfg(test)]
mod tests {
    use trust_types::*;

    use super::*;

    fn safety_vc() -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "test".to_string(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
        }
    }

    fn complex_vc() -> VerificationCondition {
        // tRust #194: Use a loop-invariant assertion (not NonTermination) as a
        // "complex VC" for scheduler tests. NonTermination VCs must NOT be routed
        // to CEGAR/IC3/PDR because PDR proves safety (AG !bad), not termination.
        // Score: loop-invariant assertion (25) + loop pattern via primed var (20) = 45 > threshold 30.
        let x = Formula::Var("x".into(), Sort::Int);
        let x_next = Formula::Var("x_next_step".into(), Sort::Int);
        let formula = Formula::Lt(Box::new(x_next), Box::new(x));
        VerificationCondition {
            kind: VcKind::Assertion {
                message: "loop invariant: counter decreases".to_string(),
            },
            function: "loop_fn".to_string(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
        }
    }

    #[test]
    fn test_schedule_empty_strategies() {
        let schedule = schedule_default(&safety_vc(), &[]);
        assert_eq!(schedule.strategy_count(), 0);
    }

    #[test]
    fn test_schedule_single_strategy() {
        let strategies = vec![Strategy::direct_smt(5000)];
        let schedule = schedule_default(&safety_vc(), &strategies);
        assert_eq!(schedule.strategy_count(), 1);
        assert_eq!(schedule.budgets[0].priority, 0);
    }

    #[test]
    fn test_schedule_smt_primary_for_simple_vc() {
        let strategies = vec![
            Strategy::direct_smt(5000),
            Strategy::cegar(100),
            Strategy::bounded_mc(50),
        ];
        let schedule = schedule_default(&safety_vc(), &strategies);
        assert_eq!(schedule.strategy_count(), 3);
        // DirectSMT should be primary (priority 0) for simple safety VCs.
        assert_eq!(schedule.budgets[0].strategy.name(), "direct-smt");
        assert_eq!(schedule.budgets[0].priority, 0);
    }

    #[test]
    fn test_schedule_cegar_primary_for_complex_vc() {
        let strategies = vec![
            Strategy::direct_smt(5000),
            Strategy::cegar(100),
            Strategy::bounded_mc(50),
        ];
        let schedule = schedule_default(&complex_vc(), &strategies);
        // CEGAR should be primary for non-termination VCs (high classifier score).
        assert_eq!(schedule.budgets[0].strategy.name(), "cegar");
        assert_eq!(schedule.budgets[0].priority, 0);
    }

    #[test]
    fn test_schedule_cegar_bonus() {
        let strategies = vec![
            Strategy::direct_smt(5000),
            Strategy::cegar(100),
        ];
        let config = SchedulerConfig {
            total_budget: Duration::from_secs(10),
            cegar_threshold: 30,
            ..SchedulerConfig::default()
        };

        // Complex VC: CEGAR gets a bonus.
        let schedule = build_schedule(&complex_vc(), &strategies, &config);
        let cegar_budget = schedule
            .budgets
            .iter()
            .find(|b| b.strategy.name() == "cegar")
            .expect("cegar should be in schedule");

        // CEGAR should get more than half the budget due to bonus.
        assert!(cegar_budget.timeout > Duration::from_secs(5));
    }

    #[test]
    fn test_schedule_minimum_time_enforced() {
        let strategies = vec![
            Strategy::direct_smt(5000),
            Strategy::cegar(100),
            Strategy::bounded_mc(50),
        ];
        let config = SchedulerConfig {
            total_budget: Duration::from_millis(100), // Very small
            min_strategy_time: Duration::from_millis(500),
            ..SchedulerConfig::default()
        };

        let schedule = build_schedule(&safety_vc(), &strategies, &config);
        for budget in &schedule.budgets {
            assert!(budget.timeout >= Duration::from_millis(500));
        }
    }

    #[test]
    fn test_schedule_strategy_names() {
        let strategies = vec![
            Strategy::direct_smt(5000),
            Strategy::bounded_mc(50),
        ];
        let schedule = schedule_default(&safety_vc(), &strategies);
        let names = schedule.strategy_names();
        assert!(names.contains(&"direct-smt"));
        assert!(names.contains(&"bounded-mc"));
    }

    #[test]
    fn test_schedule_total_allocated() {
        let strategies = vec![Strategy::direct_smt(5000)];
        let schedule = schedule_default(&safety_vc(), &strategies);
        assert!(schedule.total_allocated() > Duration::ZERO);
    }

    #[test]
    fn test_scheduler_config_default() {
        let config = SchedulerConfig::default();
        assert_eq!(config.total_budget, Duration::from_secs(30));
        assert_eq!(config.min_strategy_time, Duration::from_millis(500));
        assert_eq!(config.cegar_threshold, 30);
        assert!((config.primary_fraction - 0.5).abs() < f64::EPSILON);
    }
}
