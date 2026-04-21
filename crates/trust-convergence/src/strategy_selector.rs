// trust-convergence/strategy_selector.rs: Dynamic strengthening strategy selection.
//
// Chooses between heuristic and LLM-based strengthening based on convergence
// feedback, budget constraints, and cost models.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::feedback::{ConvergenceFeedback, SuggestedStrategy};

/// Which strengthening approach to use for the next iteration.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum StrengtheningApproach {
    /// Fast, deterministic pattern-matching and counterexample analysis.
    Heuristic,
    /// Pattern library lookup (binary search, sort, etc.).
    Pattern,
    /// LLM-based spec inference (expensive, powerful).
    Llm,
    /// Combined heuristic + LLM approach.
    Hybrid {
        /// Run heuristic first; escalate to LLM for remaining failures.
        heuristic_first: bool,
    },
}

impl StrengtheningApproach {
    /// Estimated cost in arbitrary units (lower is cheaper).
    #[must_use]
    pub fn estimated_cost(&self) -> u32 {
        match self {
            Self::Heuristic => 1,
            Self::Pattern => 2,
            Self::Llm => 100,
            Self::Hybrid { .. } => 50,
        }
    }

    /// Whether this approach uses the LLM backend.
    #[must_use]
    pub fn uses_llm(&self) -> bool {
        matches!(self, Self::Llm | Self::Hybrid { .. })
    }
}

/// Budget constraints for the strategy selector.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Budget {
    /// Remaining LLM calls allowed (None = unlimited).
    pub remaining_llm_calls: Option<u32>,
    /// Remaining time budget in milliseconds (None = unlimited).
    pub time_budget_ms: Option<u64>,
    /// Total LLM calls used so far.
    pub llm_calls_used: u32,
    /// Total time spent so far in milliseconds.
    pub time_spent_ms: u64,
}

impl Budget {
    /// Create a new budget with the given limits.
    #[must_use]
    pub fn new(max_llm_calls: Option<u32>, time_budget_ms: Option<u64>) -> Self {
        Self {
            remaining_llm_calls: max_llm_calls,
            time_budget_ms,
            llm_calls_used: 0,
            time_spent_ms: 0,
        }
    }

    /// Create an unlimited budget.
    #[must_use]
    pub fn unlimited() -> Self {
        Self::new(None, None)
    }

    /// Whether the LLM budget is exhausted.
    #[must_use]
    pub fn llm_exhausted(&self) -> bool {
        self.remaining_llm_calls == Some(0)
    }

    /// Whether the time budget is exhausted.
    #[must_use]
    pub fn time_exhausted(&self) -> bool {
        match self.time_budget_ms {
            Some(budget) => self.time_spent_ms >= budget,
            None => false,
        }
    }

    /// Whether any budget is exhausted.
    #[must_use]
    pub fn any_exhausted(&self) -> bool {
        self.llm_exhausted() || self.time_exhausted()
    }

    /// Record an LLM call, decrementing the remaining count.
    pub fn record_llm_call(&mut self) {
        self.llm_calls_used += 1;
        if let Some(ref mut remaining) = self.remaining_llm_calls {
            *remaining = remaining.saturating_sub(1);
        }
    }

    /// Record time spent.
    pub fn record_time(&mut self, ms: u64) {
        self.time_spent_ms += ms;
    }
}

impl Default for Budget {
    fn default() -> Self {
        // Default: 10 LLM calls, 5 minutes.
        Self::new(Some(10), Some(300_000))
    }
}

/// Dynamic strategy selector that chooses between strengthening approaches
/// based on convergence feedback and budget constraints.
#[derive(Debug, Clone)]
pub(crate) struct StrategySelector {
    /// Budget constraints.
    budget: Budget,
    /// Number of consecutive heuristic-only iterations.
    heuristic_streak: u32,
    /// Maximum heuristic-only iterations before considering escalation.
    max_heuristic_streak: u32,
}

impl StrategySelector {
    /// Create a new strategy selector with the given budget.
    #[must_use]
    pub fn new(budget: Budget) -> Self {
        Self {
            budget,
            heuristic_streak: 0,
            max_heuristic_streak: 3,
        }
    }

    /// Create a strategy selector with custom heuristic streak limit.
    #[must_use]
    pub fn with_max_heuristic_streak(mut self, limit: u32) -> Self {
        self.max_heuristic_streak = limit;
        self
    }

    /// Select the best strengthening approach based on convergence feedback.
    #[must_use]
    pub fn select_strategy(&self, feedback: &ConvergenceFeedback) -> StrengtheningApproach {
        // If both budgets are exhausted, fall back to heuristic.
        if self.budget.any_exhausted() {
            return StrengtheningApproach::Heuristic;
        }

        match &feedback.suggested_strategy {
            SuggestedStrategy::Continue => {
                // Making progress: stick with cheap heuristic.
                StrengtheningApproach::Heuristic
            }
            SuggestedStrategy::FocusArithmeticGuards
            | SuggestedStrategy::FocusBoundsChecks
            | SuggestedStrategy::FocusDivisionGuards => {
                // Targeted heuristic can handle these.
                if self.heuristic_streak >= self.max_heuristic_streak {
                    // Heuristic has been tried enough; escalate.
                    self.select_with_budget(StrengtheningApproach::Hybrid {
                        heuristic_first: true,
                    })
                } else {
                    StrengtheningApproach::Heuristic
                }
            }
            SuggestedStrategy::EscalateToLlm => {
                self.select_with_budget(StrengtheningApproach::Llm)
            }
            SuggestedStrategy::Hybrid { .. } => {
                self.select_with_budget(StrengtheningApproach::Hybrid {
                    heuristic_first: true,
                })
            }
            SuggestedStrategy::GiveUp { .. } => {
                // Last-ditch: try LLM if we have budget, otherwise heuristic.
                if !self.budget.llm_exhausted() {
                    self.select_with_budget(StrengtheningApproach::Llm)
                } else {
                    StrengtheningApproach::Heuristic
                }
            }
        }
    }

    /// Record the result of using a strategy, updating internal state.
    pub fn record_strategy_used(&mut self, approach: &StrengtheningApproach, time_ms: u64) {
        self.budget.record_time(time_ms);

        if approach.uses_llm() {
            self.budget.record_llm_call();
            self.heuristic_streak = 0;
        } else {
            self.heuristic_streak += 1;
        }
    }

    /// Access the current budget state.
    #[must_use]
    pub fn budget(&self) -> &Budget {
        &self.budget
    }

    /// Current heuristic streak count.
    #[must_use]
    pub fn heuristic_streak(&self) -> u32 {
        self.heuristic_streak
    }

    /// Select with budget awareness: downgrade to cheaper option if needed.
    fn select_with_budget(&self, preferred: StrengtheningApproach) -> StrengtheningApproach {
        if preferred.uses_llm() && self.budget.llm_exhausted() {
            return StrengtheningApproach::Heuristic;
        }
        if preferred.uses_llm() && self.budget.time_exhausted() {
            return StrengtheningApproach::Heuristic;
        }
        preferred
    }
}

impl Default for StrategySelector {
    fn default() -> Self {
        Self::new(Budget::default())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::feedback::{ConvergenceFeedback, SuggestedStrategy, VcCategory};

    fn make_feedback(
        strategy: SuggestedStrategy,
        net_delta: i64,
    ) -> ConvergenceFeedback {
        ConvergenceFeedback {
            what_improved: Vec::new(),
            what_stalled: Vec::new(),
            suggested_strategy: strategy,
            iterations_analyzed: 5,
            net_proved_delta: net_delta,
        }
    }

    // --- StrengtheningApproach tests ---

    #[test]
    fn test_approach_cost_ordering() {
        assert!(StrengtheningApproach::Heuristic.estimated_cost()
            < StrengtheningApproach::Pattern.estimated_cost());
        assert!(StrengtheningApproach::Pattern.estimated_cost()
            < StrengtheningApproach::Hybrid { heuristic_first: true }.estimated_cost());
        assert!(StrengtheningApproach::Hybrid { heuristic_first: true }.estimated_cost()
            < StrengtheningApproach::Llm.estimated_cost());
    }

    #[test]
    fn test_approach_uses_llm() {
        assert!(!StrengtheningApproach::Heuristic.uses_llm());
        assert!(!StrengtheningApproach::Pattern.uses_llm());
        assert!(StrengtheningApproach::Llm.uses_llm());
        assert!(StrengtheningApproach::Hybrid { heuristic_first: true }.uses_llm());
    }

    // --- Budget tests ---

    #[test]
    fn test_budget_unlimited() {
        let budget = Budget::unlimited();
        assert!(!budget.llm_exhausted());
        assert!(!budget.time_exhausted());
        assert!(!budget.any_exhausted());
    }

    #[test]
    fn test_budget_default() {
        let budget = Budget::default();
        assert_eq!(budget.remaining_llm_calls, Some(10));
        assert_eq!(budget.time_budget_ms, Some(300_000));
        assert!(!budget.any_exhausted());
    }

    #[test]
    fn test_budget_llm_exhaustion() {
        let mut budget = Budget::new(Some(2), None);
        assert!(!budget.llm_exhausted());
        budget.record_llm_call();
        assert!(!budget.llm_exhausted());
        budget.record_llm_call();
        assert!(budget.llm_exhausted());
        assert!(budget.any_exhausted());
        assert_eq!(budget.llm_calls_used, 2);
    }

    #[test]
    fn test_budget_time_exhaustion() {
        let mut budget = Budget::new(None, Some(1000));
        assert!(!budget.time_exhausted());
        budget.record_time(500);
        assert!(!budget.time_exhausted());
        budget.record_time(600);
        assert!(budget.time_exhausted());
        assert!(budget.any_exhausted());
    }

    #[test]
    fn test_budget_llm_saturating_sub() {
        let mut budget = Budget::new(Some(1), None);
        budget.record_llm_call();
        budget.record_llm_call(); // Should not underflow.
        assert_eq!(budget.remaining_llm_calls, Some(0));
        assert_eq!(budget.llm_calls_used, 2);
    }

    // --- StrategySelector tests ---

    #[test]
    fn test_select_continue_uses_heuristic() {
        let selector = StrategySelector::default();
        let feedback = make_feedback(SuggestedStrategy::Continue, 5);
        assert_eq!(selector.select_strategy(&feedback), StrengtheningApproach::Heuristic);
    }

    #[test]
    fn test_select_arithmetic_stall_uses_heuristic_initially() {
        let selector = StrategySelector::default();
        let feedback = make_feedback(SuggestedStrategy::FocusArithmeticGuards, 0);
        assert_eq!(selector.select_strategy(&feedback), StrengtheningApproach::Heuristic);
    }

    #[test]
    fn test_select_arithmetic_stall_escalates_after_streak() {
        let mut selector = StrategySelector::new(Budget::unlimited())
            .with_max_heuristic_streak(2);
        // Simulate streak.
        selector.record_strategy_used(&StrengtheningApproach::Heuristic, 100);
        selector.record_strategy_used(&StrengtheningApproach::Heuristic, 100);
        assert_eq!(selector.heuristic_streak(), 2);

        let feedback = make_feedback(SuggestedStrategy::FocusArithmeticGuards, 0);
        let approach = selector.select_strategy(&feedback);
        assert!(matches!(approach, StrengtheningApproach::Hybrid { .. }));
    }

    #[test]
    fn test_select_escalate_to_llm() {
        let selector = StrategySelector::new(Budget::unlimited());
        let feedback = make_feedback(SuggestedStrategy::EscalateToLlm, -1);
        assert_eq!(selector.select_strategy(&feedback), StrengtheningApproach::Llm);
    }

    #[test]
    fn test_select_escalate_falls_back_when_budget_exhausted() {
        let selector = StrategySelector::new(Budget::new(Some(0), None));
        let feedback = make_feedback(SuggestedStrategy::EscalateToLlm, -1);
        assert_eq!(selector.select_strategy(&feedback), StrengtheningApproach::Heuristic);
    }

    #[test]
    fn test_select_hybrid() {
        let selector = StrategySelector::new(Budget::unlimited());
        let feedback = make_feedback(
            SuggestedStrategy::Hybrid {
                categories: vec![VcCategory::Arithmetic, VcCategory::Pointer],
            },
            0,
        );
        let approach = selector.select_strategy(&feedback);
        assert!(matches!(approach, StrengtheningApproach::Hybrid { heuristic_first: true }));
    }

    #[test]
    fn test_select_give_up_with_budget_tries_llm() {
        let selector = StrategySelector::new(Budget::new(Some(5), None));
        let feedback = make_feedback(
            SuggestedStrategy::GiveUp { reason: "all stalled".into() },
            -3,
        );
        assert_eq!(selector.select_strategy(&feedback), StrengtheningApproach::Llm);
    }

    #[test]
    fn test_select_give_up_without_budget_uses_heuristic() {
        let selector = StrategySelector::new(Budget::new(Some(0), None));
        let feedback = make_feedback(
            SuggestedStrategy::GiveUp { reason: "all stalled".into() },
            -3,
        );
        assert_eq!(selector.select_strategy(&feedback), StrengtheningApproach::Heuristic);
    }

    #[test]
    fn test_record_strategy_resets_heuristic_streak() {
        let mut selector = StrategySelector::new(Budget::unlimited());
        selector.record_strategy_used(&StrengtheningApproach::Heuristic, 50);
        selector.record_strategy_used(&StrengtheningApproach::Heuristic, 50);
        assert_eq!(selector.heuristic_streak(), 2);

        selector.record_strategy_used(&StrengtheningApproach::Llm, 1000);
        assert_eq!(selector.heuristic_streak(), 0);
        assert_eq!(selector.budget().llm_calls_used, 1);
    }

    #[test]
    fn test_record_strategy_tracks_time() {
        let mut selector = StrategySelector::new(Budget::new(None, Some(5000)));
        selector.record_strategy_used(&StrengtheningApproach::Heuristic, 1000);
        selector.record_strategy_used(&StrengtheningApproach::Heuristic, 2000);
        assert_eq!(selector.budget().time_spent_ms, 3000);
        assert!(!selector.budget().time_exhausted());

        selector.record_strategy_used(&StrengtheningApproach::Heuristic, 3000);
        assert!(selector.budget().time_exhausted());
    }

    #[test]
    fn test_all_exhausted_always_heuristic() {
        let selector = StrategySelector::new(Budget::new(Some(0), Some(0)));
        // Even an LLM escalation should fall back.
        let feedback = make_feedback(SuggestedStrategy::EscalateToLlm, -5);
        assert_eq!(selector.select_strategy(&feedback), StrengtheningApproach::Heuristic);
    }

    #[test]
    fn test_bounds_check_stall_uses_heuristic() {
        let selector = StrategySelector::default();
        let feedback = make_feedback(SuggestedStrategy::FocusBoundsChecks, 0);
        assert_eq!(selector.select_strategy(&feedback), StrengtheningApproach::Heuristic);
    }

    #[test]
    fn test_division_guard_stall_uses_heuristic() {
        let selector = StrategySelector::default();
        let feedback = make_feedback(SuggestedStrategy::FocusDivisionGuards, 0);
        assert_eq!(selector.select_strategy(&feedback), StrengtheningApproach::Heuristic);
    }
}
