// trust-convergence/feedback.rs: Convergence-to-strengthen feedback loop.
//
// Connects convergence tracking to spec strengthening: analyzes iteration
// history to determine what improved, what stalled, and which strengthening
// strategy to suggest next.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::export::IterationRecord;
use crate::stagnation::StagnationResult;

/// Category of verification condition for strategy selection.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub(crate) enum VcCategory {
    /// Arithmetic overflow, cast overflow, negation overflow, shift overflow.
    Arithmetic,
    /// Division by zero, remainder by zero.
    DivisionByZero,
    /// Index out of bounds, slice bounds check.
    Pointer,
    /// Assertion failure, precondition, postcondition.
    Contract,
    /// Unreachable code reached.
    Unreachable,
    /// Termination / liveness / temporal.
    Temporal,
    /// Other / unrecognized.
    Other,
}

impl VcCategory {
    /// Classify a verdict string (from `IterationRecord`) into a category.
    ///
    /// This is a best-effort heuristic operating on the human-readable verdict
    /// strings stored in export records. For precise classification, use the
    /// `VcKind` directly.
    #[must_use]
    pub fn from_verdict(verdict: &str) -> Self {
        let lower = verdict.to_lowercase();
        if lower.contains("overflow") || lower.contains("arithmetic") || lower.contains("cast")
            || lower.contains("negation") || lower.contains("shift")
        {
            Self::Arithmetic
        } else if lower.contains("division") || lower.contains("remainder") || lower.contains("div") {
            Self::DivisionByZero
        } else if lower.contains("index") || lower.contains("bounds") || lower.contains("slice")
            || lower.contains("null") || lower.contains("pointer")
        {
            Self::Pointer
        } else if lower.contains("assert") || lower.contains("precondition")
            || lower.contains("postcondition") || lower.contains("contract")
        {
            Self::Contract
        } else if lower.contains("unreachable") {
            Self::Unreachable
        } else if lower.contains("termination") || lower.contains("liveness")
            || lower.contains("temporal")
        {
            Self::Temporal
        } else {
            Self::Other
        }
    }
}

/// What the convergence analysis suggests for the next strengthening pass.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ConvergenceFeedback {
    /// VC categories that improved in the recent history window.
    pub what_improved: Vec<VcCategory>,
    /// VC categories that stalled (no improvement over recent iterations).
    pub what_stalled: Vec<VcCategory>,
    /// Suggested strengthening strategy based on stalling patterns.
    pub suggested_strategy: SuggestedStrategy,
    /// Number of iterations analyzed.
    pub iterations_analyzed: usize,
    /// Overall trend: positive means net improvement, negative means regression.
    pub net_proved_delta: i64,
}

/// Strategy suggestion derived from convergence analysis.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum SuggestedStrategy {
    /// Continue with current approach (making progress).
    Continue,
    /// Arithmetic VCs are stalling: suggest overflow guard heuristics.
    FocusArithmeticGuards,
    /// Pointer/bounds VCs are stalling: suggest null/bounds checks.
    FocusBoundsChecks,
    /// Division VCs are stalling: suggest non-zero preconditions.
    FocusDivisionGuards,
    /// Contract VCs are stalling: suggest LLM-based inference.
    EscalateToLlm,
    /// Multiple categories stalling: try a hybrid approach.
    Hybrid { categories: Vec<VcCategory> },
    /// Everything is stalled: consider giving up or major redesign.
    GiveUp { reason: String },
}

/// Response to a stagnation event from the convergence tracker.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum StagnationResponse {
    /// Switch to a different strengthening strategy.
    ChangeStrategy { from: String, to: SuggestedStrategy },
    /// Increase the solver timeout for stalled VCs.
    IncreaseTimeout { current_ms: u64, proposed_ms: u64 },
    /// Escalate to LLM-based spec inference.
    EscalateToLlm { reason: String },
    /// The loop should stop: no further improvement expected.
    GiveUp { reason: String },
}

/// Analyze iteration history to produce convergence feedback.
///
/// Examines the most recent `window_size` iterations (or all if fewer exist)
/// to determine which VC categories are improving and which are stalled.
#[must_use]
pub(crate) fn analyze_progress(history: &[IterationRecord], window_size: usize) -> ConvergenceFeedback {
    if history.is_empty() {
        return ConvergenceFeedback {
            what_improved: Vec::new(),
            what_stalled: Vec::new(),
            suggested_strategy: SuggestedStrategy::Continue,
            iterations_analyzed: 0,
            net_proved_delta: 0,
        };
    }

    let window = if history.len() > window_size {
        &history[history.len() - window_size..]
    } else {
        history
    };

    // Compute net proved delta across the window.
    let net_proved_delta = compute_net_proved_delta(window);

    // Classify verdicts in the window to find improving vs stalling categories.
    let (improved, stalled) = classify_progress(window);

    let suggested_strategy = derive_strategy(&improved, &stalled, net_proved_delta);

    ConvergenceFeedback {
        what_improved: improved,
        what_stalled: stalled,
        suggested_strategy,
        iterations_analyzed: window.len(),
        net_proved_delta,
    }
}

/// Decide how to respond to a stagnation event.
#[must_use]
pub(crate) fn respond_to_stagnation(stagnation: &StagnationResult) -> StagnationResponse {
    if !stagnation.should_stop {
        // Not stagnant yet, but getting close: suggest timeout increase.
        if stagnation.stale_iterations >= stagnation.threshold / 2 {
            return StagnationResponse::IncreaseTimeout {
                current_ms: 5000,
                proposed_ms: 10000,
            };
        }
        return StagnationResponse::ChangeStrategy {
            from: "current".into(),
            to: SuggestedStrategy::Continue,
        };
    }

    // Fully stagnant: decide based on how long we've been stuck.
    if stagnation.stale_iterations <= stagnation.threshold + 2 {
        StagnationResponse::EscalateToLlm {
            reason: format!(
                "Stagnant for {} iterations: heuristic strengthening exhausted",
                stagnation.stale_iterations
            ),
        }
    } else {
        StagnationResponse::GiveUp {
            reason: format!(
                "Stagnant for {} iterations (threshold {}): no further improvement expected",
                stagnation.stale_iterations, stagnation.threshold
            ),
        }
    }
}

/// The main feedback loop struct connecting convergence tracking to strengthening.
///
/// Maintains a rolling window of iteration records and produces feedback
/// that guides the strengthening strategy selection.
#[derive(Debug, Clone)]
pub(crate) struct FeedbackLoop {
    /// Rolling history of iteration records.
    history: Vec<IterationRecord>,
    /// Window size for analysis (how many recent iterations to consider).
    window_size: usize,
    /// Maximum iterations before forced stop.
    max_iterations: usize,
}

impl FeedbackLoop {
    /// Create a new feedback loop with the given analysis window and iteration limit.
    #[must_use]
    pub fn new(window_size: usize, max_iterations: usize) -> Self {
        assert!(window_size > 0, "window_size must be non-zero");
        assert!(max_iterations > 0, "max_iterations must be non-zero");
        Self {
            history: Vec::new(),
            window_size,
            max_iterations,
        }
    }

    /// Record a new iteration and get feedback for the next strengthening pass.
    #[must_use]
    pub fn record_and_analyze(&mut self, record: IterationRecord) -> ConvergenceFeedback {
        self.history.push(record);
        analyze_progress(&self.history, self.window_size)
    }

    /// Whether the loop has reached the maximum iteration count.
    #[must_use]
    pub fn is_exhausted(&self) -> bool {
        self.history.len() >= self.max_iterations
    }

    /// Number of iterations recorded so far.
    #[must_use]
    pub fn iteration_count(&self) -> usize {
        self.history.len()
    }

    /// Access the full iteration history.
    #[must_use]
    pub fn history(&self) -> &[IterationRecord] {
        &self.history
    }

    /// Get the latest convergence feedback without recording a new iteration.
    #[must_use]
    pub fn latest_feedback(&self) -> ConvergenceFeedback {
        analyze_progress(&self.history, self.window_size)
    }
}

impl Default for FeedbackLoop {
    fn default() -> Self {
        Self::new(5, 20)
    }
}

// --- Private helpers ---

/// Compute the net change in proved obligations across a window of iterations.
fn compute_net_proved_delta(window: &[IterationRecord]) -> i64 {
    if window.len() < 2 {
        return 0;
    }
    let first = &window[0].frontier;
    let last = &window[window.len() - 1].frontier;
    let first_proved = (first.trusted + first.certified) as i64;
    let last_proved = (last.trusted + last.certified) as i64;
    last_proved - first_proved
}

/// Classify which VC categories improved and which stalled in the window.
///
/// An "improved" iteration has verdict "improved" in the record. We examine
/// deltas to determine which categories are moving.
fn classify_progress(window: &[IterationRecord]) -> (Vec<VcCategory>, Vec<VcCategory>) {
    use trust_types::fx::FxHashSet;

    let mut improving_cats = FxHashSet::default();
    let mut all_cats = FxHashSet::default();

    for record in window {
        // If the verdict is "improved", track which delta fields improved.
        if let Some(ref delta) = record.delta {
            // Track all categories that have any activity.
            if delta.trusted != 0 || delta.certified != 0 {
                all_cats.insert(VcCategory::Arithmetic);
                all_cats.insert(VcCategory::DivisionByZero);
                all_cats.insert(VcCategory::Pointer);
                all_cats.insert(VcCategory::Contract);
            }
            if delta.failed != 0 {
                all_cats.insert(VcCategory::Arithmetic);
                all_cats.insert(VcCategory::DivisionByZero);
                all_cats.insert(VcCategory::Pointer);
            }

            // If proved count increased, something improved.
            if delta.trusted > 0 || delta.certified > 0 {
                // We cannot know exactly which category from aggregate deltas,
                // but we can look at the verdict string for hints.
                if let Some(ref verdict) = record.verdict {
                    improving_cats.insert(VcCategory::from_verdict(verdict));
                } else {
                    // Default: attribute to arithmetic (most common).
                    improving_cats.insert(VcCategory::Arithmetic);
                }
            }

            // If failures decreased, that's progress.
            if delta.failed < 0 {
                improving_cats.insert(VcCategory::Contract);
            }
        }
    }

    let improved: Vec<VcCategory> = improving_cats.iter().copied().collect();
    let stalled: Vec<VcCategory> = all_cats
        .difference(&improving_cats)
        .copied()
        .collect();

    (improved, stalled)
}

/// Derive a strategy suggestion from the improving/stalling category sets.
fn derive_strategy(
    improved: &[VcCategory],
    stalled: &[VcCategory],
    net_proved_delta: i64,
) -> SuggestedStrategy {
    // If nothing is stalling, continue.
    if stalled.is_empty() {
        return SuggestedStrategy::Continue;
    }

    // If everything is stalling and we're regressing, give up.
    if improved.is_empty() && net_proved_delta <= 0 && stalled.len() >= 3 {
        return SuggestedStrategy::GiveUp {
            reason: format!(
                "{} categories stalled with net delta {net_proved_delta}",
                stalled.len()
            ),
        };
    }

    // Single stalling category: targeted suggestion.
    if stalled.len() == 1 {
        return match stalled[0] {
            VcCategory::Arithmetic => SuggestedStrategy::FocusArithmeticGuards,
            VcCategory::DivisionByZero => SuggestedStrategy::FocusDivisionGuards,
            VcCategory::Pointer => SuggestedStrategy::FocusBoundsChecks,
            VcCategory::Contract => SuggestedStrategy::EscalateToLlm,
            _ => SuggestedStrategy::EscalateToLlm,
        };
    }

    // Multiple stalling categories: hybrid.
    SuggestedStrategy::Hybrid {
        categories: stalled.to_vec(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::export::{SerializableDelta, SerializableFrontier};

    fn make_frontier(trusted: u32, failed: u32) -> SerializableFrontier {
        SerializableFrontier {
            trusted,
            certified: 0,
            runtime_checked: 0,
            failed,
            unknown: 0,
        }
    }

    fn make_record(
        iteration: u32,
        trusted: u32,
        failed: u32,
        delta: Option<(i64, i64)>,
        verdict: Option<&str>,
    ) -> IterationRecord {
        IterationRecord {
            iteration,
            frontier: make_frontier(trusted, failed),
            delta: delta.map(|(dt, df)| SerializableDelta {
                trusted: dt,
                certified: 0,
                runtime_checked: 0,
                failed: df,
                unknown: 0,
            }),
            verdict: verdict.map(String::from),
            fingerprint: None,
        }
    }

    // --- VcCategory tests ---

    #[test]
    fn test_vc_category_from_verdict_arithmetic() {
        assert_eq!(VcCategory::from_verdict("arithmetic overflow"), VcCategory::Arithmetic);
        assert_eq!(VcCategory::from_verdict("cast_overflow"), VcCategory::Arithmetic);
        assert_eq!(VcCategory::from_verdict("Shift Overflow"), VcCategory::Arithmetic);
    }

    #[test]
    fn test_vc_category_from_verdict_division() {
        assert_eq!(VcCategory::from_verdict("division by zero"), VcCategory::DivisionByZero);
        assert_eq!(VcCategory::from_verdict("remainder check"), VcCategory::DivisionByZero);
    }

    #[test]
    fn test_vc_category_from_verdict_pointer() {
        assert_eq!(VcCategory::from_verdict("index out of bounds"), VcCategory::Pointer);
        assert_eq!(VcCategory::from_verdict("slice_bounds"), VcCategory::Pointer);
        assert_eq!(VcCategory::from_verdict("null pointer"), VcCategory::Pointer);
    }

    #[test]
    fn test_vc_category_from_verdict_contract() {
        assert_eq!(VcCategory::from_verdict("assertion failure"), VcCategory::Contract);
        assert_eq!(VcCategory::from_verdict("precondition"), VcCategory::Contract);
        assert_eq!(VcCategory::from_verdict("postcondition"), VcCategory::Contract);
    }

    #[test]
    fn test_vc_category_from_verdict_other() {
        assert_eq!(VcCategory::from_verdict("unknown"), VcCategory::Other);
        assert_eq!(VcCategory::from_verdict(""), VcCategory::Other);
    }

    // --- analyze_progress tests ---

    #[test]
    fn test_analyze_empty_history() {
        let feedback = analyze_progress(&[], 5);
        assert!(feedback.what_improved.is_empty());
        assert!(feedback.what_stalled.is_empty());
        assert_eq!(feedback.suggested_strategy, SuggestedStrategy::Continue);
        assert_eq!(feedback.iterations_analyzed, 0);
        assert_eq!(feedback.net_proved_delta, 0);
    }

    #[test]
    fn test_analyze_single_iteration() {
        let history = vec![make_record(0, 3, 1, None, None)];
        let feedback = analyze_progress(&history, 5);
        assert_eq!(feedback.iterations_analyzed, 1);
        assert_eq!(feedback.net_proved_delta, 0);
    }

    #[test]
    fn test_analyze_improving_history() {
        let history = vec![
            make_record(0, 1, 3, None, None),
            make_record(1, 3, 1, Some((2, -2)), Some("improved")),
        ];
        let feedback = analyze_progress(&history, 5);
        assert_eq!(feedback.net_proved_delta, 2);
        assert!(!feedback.what_improved.is_empty());
    }

    #[test]
    fn test_analyze_stalling_history() {
        let history = vec![
            make_record(0, 3, 1, None, None),
            make_record(1, 3, 1, Some((0, 0)), Some("stable")),
            make_record(2, 3, 1, Some((0, 0)), Some("stable")),
        ];
        let feedback = analyze_progress(&history, 5);
        assert_eq!(feedback.net_proved_delta, 0);
    }

    #[test]
    fn test_analyze_window_limits() {
        // Create 10 iterations but window is 3.
        let mut history = Vec::new();
        for i in 0..10 {
            history.push(make_record(i, i + 1, 10 - i, None, None));
        }
        let feedback = analyze_progress(&history, 3);
        assert_eq!(feedback.iterations_analyzed, 3);
    }

    // --- respond_to_stagnation tests ---

    #[test]
    fn test_respond_not_stagnant_early() {
        let result = StagnationResult {
            should_stop: false,
            stale_iterations: 0,
            threshold: 5,
            reason: "improving".into(),
        };
        let response = respond_to_stagnation(&result);
        assert!(matches!(response, StagnationResponse::ChangeStrategy { .. }));
    }

    #[test]
    fn test_respond_not_stagnant_near_threshold() {
        let result = StagnationResult {
            should_stop: false,
            stale_iterations: 3,
            threshold: 5,
            reason: "3 of 5 stale iterations".into(),
        };
        let response = respond_to_stagnation(&result);
        assert!(matches!(response, StagnationResponse::IncreaseTimeout { .. }));
        if let StagnationResponse::IncreaseTimeout { current_ms, proposed_ms } = response {
            assert!(proposed_ms > current_ms);
        }
    }

    #[test]
    fn test_respond_stagnant_escalate() {
        let result = StagnationResult {
            should_stop: true,
            stale_iterations: 3,
            threshold: 3,
            reason: "no improvement".into(),
        };
        let response = respond_to_stagnation(&result);
        assert!(matches!(response, StagnationResponse::EscalateToLlm { .. }));
    }

    #[test]
    fn test_respond_deeply_stagnant_give_up() {
        let result = StagnationResult {
            should_stop: true,
            stale_iterations: 10,
            threshold: 3,
            reason: "no improvement".into(),
        };
        let response = respond_to_stagnation(&result);
        assert!(matches!(response, StagnationResponse::GiveUp { .. }));
    }

    // --- FeedbackLoop tests ---

    #[test]
    fn test_feedback_loop_creation() {
        let fl = FeedbackLoop::new(5, 20);
        assert_eq!(fl.iteration_count(), 0);
        assert!(!fl.is_exhausted());
    }

    #[test]
    fn test_feedback_loop_default() {
        let fl = FeedbackLoop::default();
        assert_eq!(fl.window_size, 5);
        assert_eq!(fl.max_iterations, 20);
    }

    #[test]
    fn test_feedback_loop_record_and_analyze() {
        let mut fl = FeedbackLoop::new(3, 10);
        let record = make_record(0, 3, 1, None, None);
        let feedback = fl.record_and_analyze(record);
        assert_eq!(feedback.iterations_analyzed, 1);
        assert_eq!(fl.iteration_count(), 1);
    }

    #[test]
    fn test_feedback_loop_exhaustion() {
        let mut fl = FeedbackLoop::new(3, 2);
        let _ = fl.record_and_analyze(make_record(0, 1, 3, None, None));
        assert!(!fl.is_exhausted());
        let _ = fl.record_and_analyze(make_record(1, 2, 2, Some((1, -1)), Some("improved")));
        assert!(fl.is_exhausted());
    }

    #[test]
    fn test_feedback_loop_latest_feedback() {
        let mut fl = FeedbackLoop::new(3, 10);
        let _ = fl.record_and_analyze(make_record(0, 1, 3, None, None));
        let _ = fl.record_and_analyze(make_record(1, 3, 1, Some((2, -2)), Some("improved")));
        let feedback = fl.latest_feedback();
        assert_eq!(feedback.iterations_analyzed, 2);
        assert_eq!(feedback.net_proved_delta, 2);
    }

    #[test]
    fn test_feedback_loop_history_access() {
        let mut fl = FeedbackLoop::new(3, 10);
        let _ = fl.record_and_analyze(make_record(0, 1, 3, None, None));
        let _ = fl.record_and_analyze(make_record(1, 3, 1, Some((2, -2)), Some("improved")));
        assert_eq!(fl.history().len(), 2);
        assert_eq!(fl.history()[0].iteration, 0);
        assert_eq!(fl.history()[1].iteration, 1);
    }

    #[test]
    #[should_panic(expected = "window_size must be non-zero")]
    fn test_feedback_loop_zero_window_panics() {
        let _ = FeedbackLoop::new(0, 10);
    }

    #[test]
    #[should_panic(expected = "max_iterations must be non-zero")]
    fn test_feedback_loop_zero_max_panics() {
        let _ = FeedbackLoop::new(5, 0);
    }

    // --- derive_strategy tests ---

    #[test]
    fn test_derive_strategy_nothing_stalled() {
        let strategy = derive_strategy(&[VcCategory::Arithmetic], &[], 5);
        assert_eq!(strategy, SuggestedStrategy::Continue);
    }

    #[test]
    fn test_derive_strategy_arithmetic_stalled() {
        let strategy = derive_strategy(&[], &[VcCategory::Arithmetic], 0);
        assert_eq!(strategy, SuggestedStrategy::FocusArithmeticGuards);
    }

    #[test]
    fn test_derive_strategy_pointer_stalled() {
        let strategy = derive_strategy(&[], &[VcCategory::Pointer], 0);
        assert_eq!(strategy, SuggestedStrategy::FocusBoundsChecks);
    }

    #[test]
    fn test_derive_strategy_division_stalled() {
        let strategy = derive_strategy(&[], &[VcCategory::DivisionByZero], 0);
        assert_eq!(strategy, SuggestedStrategy::FocusDivisionGuards);
    }

    #[test]
    fn test_derive_strategy_contract_stalled_escalates() {
        let strategy = derive_strategy(&[], &[VcCategory::Contract], 0);
        assert_eq!(strategy, SuggestedStrategy::EscalateToLlm);
    }

    #[test]
    fn test_derive_strategy_multiple_stalled_hybrid() {
        let strategy = derive_strategy(
            &[],
            &[VcCategory::Arithmetic, VcCategory::Pointer],
            0,
        );
        assert!(matches!(strategy, SuggestedStrategy::Hybrid { .. }));
    }

    #[test]
    fn test_derive_strategy_everything_stalled_give_up() {
        let strategy = derive_strategy(
            &[],
            &[VcCategory::Arithmetic, VcCategory::Pointer, VcCategory::Contract],
            -1,
        );
        assert!(matches!(strategy, SuggestedStrategy::GiveUp { .. }));
    }

    // --- compute_net_proved_delta tests ---

    #[test]
    fn test_net_proved_delta_empty() {
        assert_eq!(compute_net_proved_delta(&[]), 0);
    }

    #[test]
    fn test_net_proved_delta_single() {
        let records = vec![make_record(0, 5, 0, None, None)];
        assert_eq!(compute_net_proved_delta(&records), 0);
    }

    #[test]
    fn test_net_proved_delta_improvement() {
        let records = vec![
            make_record(0, 1, 3, None, None),
            make_record(1, 4, 0, Some((3, -3)), Some("improved")),
        ];
        assert_eq!(compute_net_proved_delta(&records), 3);
    }

    #[test]
    fn test_net_proved_delta_regression() {
        let records = vec![
            make_record(0, 5, 0, None, None),
            make_record(1, 3, 2, Some((-2, 2)), Some("regressed")),
        ];
        assert_eq!(compute_net_proved_delta(&records), -2);
    }
}
