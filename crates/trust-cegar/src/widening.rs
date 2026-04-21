// trust-cegar/widening.rs: Widening strategy selection (#273)
//
// Provides configurable widening strategies for abstract interpretation fixpoint
// computation. Supports standard widening, delayed widening (apply join for
// several iterations before switching to widen), threshold-based widening
// (jump to next threshold instead of infinity), and narrowing refinement.
//
// References:
//   Cousot, Cousot. "Comparing the Galois Connection and Widening/Narrowing
//     Approaches to Abstract Interpretation" (PLILP 1992).
//   Blanchet et al. "A Static Analyzer for Large Safety-Critical Software"
//     (PLDI 2003) — threshold widening in Astree.
//   Halbwachs, Henry. "When the Decreasing Sequence Fails" (SAS 2012).
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::lattice::{IntervalLattice, Lattice, Widenable};

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

/// Widening strategy for fixpoint acceleration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum WideningStrategy {
    /// Standard widening: jump to infinity on any growth.
    Standard,
    /// Delayed widening: apply join for `delay` iterations, then widen.
    Delayed { delay: usize },
    /// Threshold widening: jump to next threshold instead of infinity.
    WithThresholds,
    /// Narrowing: refine an over-approximation downward.
    Narrowing,
}

/// A sorted, deduplicated set of threshold values for threshold widening.
#[derive(Debug, Clone)]
pub(crate) struct ThresholdSet {
    /// Threshold values in ascending order (no duplicates).
    pub thresholds: Vec<i64>,
}

impl ThresholdSet {
    /// Create a new threshold set. Sorts and deduplicates the input.
    #[must_use]
    pub(crate) fn new(mut values: Vec<i64>) -> Self {
        values.sort_unstable();
        values.dedup();
        Self { thresholds: values }
    }

    /// Find the smallest threshold strictly greater than `val`, or `None`.
    #[must_use]
    pub(crate) fn next_above(&self, val: i64) -> Option<i64> {
        self.thresholds.iter().copied().find(|&t| t > val)
    }

    /// Find the largest threshold strictly less than `val`, or `None`.
    #[must_use]
    pub(crate) fn next_below(&self, val: i64) -> Option<i64> {
        self.thresholds.iter().rev().copied().find(|&t| t < val)
    }

    /// Number of thresholds.
    #[must_use]
    pub(crate) fn len(&self) -> usize {
        self.thresholds.len()
    }

    /// Whether the set is empty.
    #[must_use]
    pub(crate) fn is_empty(&self) -> bool {
        self.thresholds.is_empty()
    }
}

/// Configuration for widening behavior.
#[derive(Debug, Clone)]
pub(crate) struct WideningConfig {
    /// Selected widening strategy.
    pub strategy: WideningStrategy,
    /// Optional threshold set (used with `WithThresholds` strategy).
    pub threshold_set: Option<ThresholdSet>,
    /// Maximum number of narrowing steps after widening stabilises.
    pub max_narrowing_steps: usize,
}

impl Default for WideningConfig {
    fn default() -> Self {
        Self {
            strategy: WideningStrategy::Standard,
            threshold_set: None,
            max_narrowing_steps: 5,
        }
    }
}

/// Mutable state for delayed widening.
#[derive(Debug, Clone)]
pub(crate) struct DelayedWidening {
    /// Number of join iterations before switching to widen.
    pub delay: usize,
    /// Current iteration counter.
    pub counter: usize,
}

impl DelayedWidening {
    /// Create a new delayed-widening state with the given delay.
    #[must_use]
    pub(crate) fn new(delay: usize) -> Self {
        Self { delay, counter: 0 }
    }

    /// Whether the delay has been exhausted (counter >= delay).
    #[must_use]
    pub(crate) fn is_exhausted(&self) -> bool {
        self.counter >= self.delay
    }

    /// Reset the counter to zero.
    pub(crate) fn reset(&mut self) {
        self.counter = 0;
    }
}

/// Result of a widening/narrowing step.
#[derive(Debug, Clone)]
pub(crate) struct WideningResult<T> {
    /// The resulting abstract value.
    pub value: T,
    /// Whether widening was applied.
    pub widened: bool,
    /// Whether narrowing was applied.
    pub narrowed: bool,
}

// ---------------------------------------------------------------------------
// Strategy selection
// ---------------------------------------------------------------------------

/// Select the effective widening strategy for the current iteration.
///
/// For `Delayed` strategy, returns `Standard` once the delay is exhausted;
/// otherwise returns `Standard` (signalling that plain join should be used
/// by the caller — the `delayed_widen` function handles this properly).
/// All other strategies are returned as-is.
#[must_use]
pub(crate) fn select_strategy(iteration: usize, config: &WideningConfig) -> WideningStrategy {
    match &config.strategy {
        WideningStrategy::Delayed { delay } => {
            if iteration >= *delay {
                WideningStrategy::Standard
            } else {
                WideningStrategy::Delayed { delay: *delay }
            }
        }
        other => other.clone(),
    }
}

// ---------------------------------------------------------------------------
// Threshold widening
// ---------------------------------------------------------------------------

/// Widen with thresholds: instead of jumping to `i64::MIN`/`i64::MAX`, jump
/// to the next threshold value. Falls back to standard widening when no
/// suitable threshold exists.
#[must_use]
pub(crate) fn widen_with_thresholds(
    current: &IntervalLattice,
    next: &IntervalLattice,
    thresholds: &ThresholdSet,
) -> IntervalLattice {
    match (current, next) {
        (IntervalLattice::Bottom, x) | (x, IntervalLattice::Bottom) => x.clone(),
        (IntervalLattice::Top, _) | (_, IntervalLattice::Top) => IntervalLattice::Top,
        (
            IntervalLattice::Interval { lo: l1, hi: h1 },
            IntervalLattice::Interval { lo: l2, hi: h2 },
        ) => {
            // Lower bound: if next is lower, jump down to next threshold (or MIN).
            let lo = if l2 < l1 {
                thresholds.next_below(*l1).unwrap_or(i64::MIN)
            } else {
                *l1
            };
            // Upper bound: if next is higher, jump up to next threshold (or MAX).
            let hi = if h2 > h1 {
                thresholds.next_above(*h1).unwrap_or(i64::MAX)
            } else {
                *h1
            };
            if lo == i64::MIN && hi == i64::MAX {
                IntervalLattice::Top
            } else {
                IntervalLattice::Interval { lo, hi }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Delayed widening
// ---------------------------------------------------------------------------

/// Apply delayed widening: use join for the first `delay` iterations, then
/// switch to standard widening. Increments the internal counter.
pub(crate) fn delayed_widen(
    state: &mut DelayedWidening,
    current: &IntervalLattice,
    next: &IntervalLattice,
) -> IntervalLattice {
    state.counter += 1;
    if state.is_exhausted() {
        current.widen(next)
    } else {
        current.join(next)
    }
}

// ---------------------------------------------------------------------------
// Narrowing
// ---------------------------------------------------------------------------

/// Single narrowing step: refine a widened over-approximation using precise
/// information. Only tightens bounds that were pushed to infinity by widening.
#[must_use]
pub(crate) fn narrowing_step(
    widened: &IntervalLattice,
    precise: &IntervalLattice,
) -> IntervalLattice {
    widened.narrow(precise)
}

// ---------------------------------------------------------------------------
// Full widening sequence
// ---------------------------------------------------------------------------

/// Process a sequence of abstract values using the configured strategy.
///
/// Folds the `values` slice left-to-right, applying the chosen widening
/// operator at each step. For `Narrowing` strategy, the first pass uses
/// standard widening to reach a post-fixpoint, then applies up to
/// `max_narrowing_steps` narrowing iterations.
#[must_use]
pub(crate) fn full_widening_sequence(
    values: &[IntervalLattice],
    config: &WideningConfig,
) -> IntervalLattice {
    if values.is_empty() {
        return IntervalLattice::Bottom;
    }

    let mut result = values[0].clone();

    match &config.strategy {
        WideningStrategy::Standard => {
            for v in &values[1..] {
                result = result.widen(v);
            }
        }

        WideningStrategy::Delayed { delay } => {
            let mut state = DelayedWidening::new(*delay);
            for v in &values[1..] {
                result = delayed_widen(&mut state, &result, v);
            }
        }

        WideningStrategy::WithThresholds => {
            let thresholds = config
                .threshold_set
                .as_ref()
                .cloned()
                .unwrap_or_else(|| ThresholdSet::new(vec![]));
            for v in &values[1..] {
                result = widen_with_thresholds(&result, v, &thresholds);
            }
        }

        WideningStrategy::Narrowing => {
            // Phase 1: widen to a post-fixpoint.
            for v in &values[1..] {
                result = result.widen(v);
            }
            // Phase 2: narrow using the original values (up to max steps).
            let steps = config.max_narrowing_steps.min(values.len());
            for v in values.iter().rev().take(steps) {
                let narrowed = narrowing_step(&result, v);
                if narrowed == result {
                    break;
                }
                result = narrowed;
            }
        }
    }

    result
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // -- ThresholdSet -------------------------------------------------------

    #[test]
    fn test_threshold_set_sorts_and_deduplicates() {
        let ts = ThresholdSet::new(vec![10, 5, 10, -3, 5, 100]);
        assert_eq!(ts.thresholds, vec![-3, 5, 10, 100]);
    }

    #[test]
    fn test_threshold_set_next_above() {
        let ts = ThresholdSet::new(vec![0, 10, 50, 100]);
        assert_eq!(ts.next_above(5), Some(10));
        assert_eq!(ts.next_above(10), Some(50));
        assert_eq!(ts.next_above(100), None);
        assert_eq!(ts.next_above(-1), Some(0));
    }

    #[test]
    fn test_threshold_set_next_below() {
        let ts = ThresholdSet::new(vec![0, 10, 50, 100]);
        assert_eq!(ts.next_below(5), Some(0));
        assert_eq!(ts.next_below(10), Some(0));
        assert_eq!(ts.next_below(0), None);
        assert_eq!(ts.next_below(101), Some(100));
    }

    #[test]
    fn test_threshold_set_empty() {
        let ts = ThresholdSet::new(vec![]);
        assert!(ts.is_empty());
        assert_eq!(ts.len(), 0);
        assert_eq!(ts.next_above(0), None);
        assert_eq!(ts.next_below(0), None);
    }

    // -- WideningConfig default ---------------------------------------------

    #[test]
    fn test_widening_config_default() {
        let cfg = WideningConfig::default();
        assert_eq!(cfg.strategy, WideningStrategy::Standard);
        assert!(cfg.threshold_set.is_none());
        assert_eq!(cfg.max_narrowing_steps, 5);
    }

    // -- select_strategy ----------------------------------------------------

    #[test]
    fn test_select_strategy_standard_passthrough() {
        let cfg = WideningConfig::default();
        assert_eq!(select_strategy(0, &cfg), WideningStrategy::Standard);
        assert_eq!(select_strategy(100, &cfg), WideningStrategy::Standard);
    }

    #[test]
    fn test_select_strategy_delayed_before_and_after() {
        let cfg = WideningConfig {
            strategy: WideningStrategy::Delayed { delay: 3 },
            ..WideningConfig::default()
        };
        // Before delay exhausted: returns Delayed.
        assert_eq!(select_strategy(0, &cfg), WideningStrategy::Delayed { delay: 3 });
        assert_eq!(select_strategy(2, &cfg), WideningStrategy::Delayed { delay: 3 });
        // At or past delay: returns Standard.
        assert_eq!(select_strategy(3, &cfg), WideningStrategy::Standard);
        assert_eq!(select_strategy(10, &cfg), WideningStrategy::Standard);
    }

    #[test]
    fn test_select_strategy_with_thresholds_passthrough() {
        let cfg = WideningConfig {
            strategy: WideningStrategy::WithThresholds,
            threshold_set: Some(ThresholdSet::new(vec![10])),
            ..WideningConfig::default()
        };
        assert_eq!(select_strategy(5, &cfg), WideningStrategy::WithThresholds);
    }

    // -- widen_with_thresholds ----------------------------------------------

    #[test]
    fn test_widen_thresholds_upper_bound() {
        let ts = ThresholdSet::new(vec![0, 10, 50, 100]);
        let current = IntervalLattice::range(0, 5);
        let next = IntervalLattice::range(0, 8);
        // hi grew (5→8), should jump to next threshold above 5, which is 10.
        let result = widen_with_thresholds(&current, &next, &ts);
        assert_eq!(result, IntervalLattice::range(0, 10));
    }

    #[test]
    fn test_widen_thresholds_lower_bound() {
        let ts = ThresholdSet::new(vec![-100, -50, 0, 10]);
        let current = IntervalLattice::range(0, 10);
        let next = IntervalLattice::range(-3, 10);
        // lo shrunk (0→-3), should jump to next threshold below 0, which is -50.
        let result = widen_with_thresholds(&current, &next, &ts);
        assert_eq!(result, IntervalLattice::range(-50, 10));
    }

    #[test]
    fn test_widen_thresholds_no_growth_unchanged() {
        let ts = ThresholdSet::new(vec![0, 10, 50]);
        let current = IntervalLattice::range(0, 10);
        let next = IntervalLattice::range(2, 8);
        // No growth in either direction: keeps current bounds.
        let result = widen_with_thresholds(&current, &next, &ts);
        assert_eq!(result, IntervalLattice::range(0, 10));
    }

    #[test]
    fn test_widen_thresholds_fallback_to_max() {
        let ts = ThresholdSet::new(vec![0, 10]);
        let current = IntervalLattice::range(0, 10);
        let next = IntervalLattice::range(0, 15);
        // hi grew past all thresholds, falls back to i64::MAX.
        let result = widen_with_thresholds(&current, &next, &ts);
        assert_eq!(result, IntervalLattice::Interval { lo: 0, hi: i64::MAX });
    }

    #[test]
    fn test_widen_thresholds_with_bottom() {
        let ts = ThresholdSet::new(vec![0, 10]);
        let result = widen_with_thresholds(&IntervalLattice::Bottom, &IntervalLattice::range(1, 5), &ts);
        assert_eq!(result, IntervalLattice::range(1, 5));
    }

    // -- delayed_widen ------------------------------------------------------

    #[test]
    fn test_delayed_widen_joins_during_delay() {
        let mut state = DelayedWidening::new(3);
        let a = IntervalLattice::range(0, 5);
        let b = IntervalLattice::range(0, 10);
        // Iteration 1 (counter becomes 1, still < 3): join.
        let r1 = delayed_widen(&mut state, &a, &b);
        assert_eq!(r1, IntervalLattice::range(0, 10)); // join result
        assert_eq!(state.counter, 1);
    }

    #[test]
    fn test_delayed_widen_widens_after_delay() {
        let mut state = DelayedWidening::new(2);
        let a = IntervalLattice::range(0, 5);
        let b = IntervalLattice::range(0, 10);
        // Exhaust delay.
        let _ = delayed_widen(&mut state, &a, &b); // counter=1
        let _ = delayed_widen(&mut state, &a, &b); // counter=2, exhausted
        // Now it should widen.
        let r = delayed_widen(&mut state, &a, &b);
        assert_eq!(r, IntervalLattice::Interval { lo: 0, hi: i64::MAX });
    }

    #[test]
    fn test_delayed_widening_reset() {
        let mut state = DelayedWidening::new(2);
        state.counter = 5;
        assert!(state.is_exhausted());
        state.reset();
        assert!(!state.is_exhausted());
        assert_eq!(state.counter, 0);
    }

    // -- narrowing_step -----------------------------------------------------

    #[test]
    fn test_narrowing_step_tightens_infinity() {
        let widened = IntervalLattice::Interval { lo: 0, hi: i64::MAX };
        let precise = IntervalLattice::range(0, 42);
        let result = narrowing_step(&widened, &precise);
        assert_eq!(result, IntervalLattice::range(0, 42));
    }

    #[test]
    fn test_narrowing_step_preserves_finite_bounds() {
        let widened = IntervalLattice::range(0, 100);
        let precise = IntervalLattice::range(5, 50);
        // Neither bound is at infinity, so narrowing keeps widened bounds.
        let result = narrowing_step(&widened, &precise);
        assert_eq!(result, IntervalLattice::range(0, 100));
    }

    // -- full_widening_sequence ---------------------------------------------

    #[test]
    fn test_full_sequence_empty() {
        let cfg = WideningConfig::default();
        let result = full_widening_sequence(&[], &cfg);
        assert!(result.is_bottom());
    }

    #[test]
    fn test_full_sequence_single_value() {
        let cfg = WideningConfig::default();
        let values = vec![IntervalLattice::range(0, 10)];
        let result = full_widening_sequence(&values, &cfg);
        assert_eq!(result, IntervalLattice::range(0, 10));
    }

    #[test]
    fn test_full_sequence_standard_widens() {
        let cfg = WideningConfig::default();
        let values = vec![
            IntervalLattice::range(0, 1),
            IntervalLattice::range(0, 2),
            IntervalLattice::range(0, 3),
        ];
        let result = full_widening_sequence(&values, &cfg);
        // After first widen: [0, MAX]. Subsequent widens keep it there.
        assert_eq!(result, IntervalLattice::Interval { lo: 0, hi: i64::MAX });
    }

    #[test]
    fn test_full_sequence_with_thresholds() {
        let cfg = WideningConfig {
            strategy: WideningStrategy::WithThresholds,
            threshold_set: Some(ThresholdSet::new(vec![0, 10, 100, 1000])),
            max_narrowing_steps: 5,
        };
        let values = vec![
            IntervalLattice::range(0, 1),
            IntervalLattice::range(0, 5),
            IntervalLattice::range(0, 15),
        ];
        // Step 1: [0,1] widen [0,5] → hi grew, jump to 10 → [0, 10].
        // Step 2: [0,10] widen [0,15] → hi grew, jump to next above 10 = 100 → [0, 100].
        let result = full_widening_sequence(&values, &cfg);
        assert_eq!(result, IntervalLattice::range(0, 100));
    }

    #[test]
    fn test_full_sequence_narrowing_refines() {
        let cfg = WideningConfig {
            strategy: WideningStrategy::Narrowing,
            threshold_set: None,
            max_narrowing_steps: 5,
        };
        let values = vec![
            IntervalLattice::range(0, 1),
            IntervalLattice::range(0, 5),
            IntervalLattice::range(0, 10),
        ];
        // Phase 1 (widen): [0,1] widen [0,5] → [0, MAX]; widen [0,10] → [0, MAX].
        // Phase 2 (narrow): narrow [0,MAX] with [0,10] → [0,10];
        //   narrow [0,10] with [0,5] → [0,10] (no infinity, unchanged);
        //   narrow [0,10] with [0,1] → [0,10] (same). Fixpoint reached.
        let result = full_widening_sequence(&values, &cfg);
        assert_eq!(result, IntervalLattice::range(0, 10));
    }

    #[test]
    fn test_full_sequence_delayed() {
        let cfg = WideningConfig {
            strategy: WideningStrategy::Delayed { delay: 2 },
            threshold_set: None,
            max_narrowing_steps: 5,
        };
        let values = vec![
            IntervalLattice::range(0, 1),
            IntervalLattice::range(0, 5),
            IntervalLattice::range(0, 10),
            IntervalLattice::range(0, 15),
        ];
        // Step 1 (counter=1 < 2): join [0,1] ∪ [0,5] = [0,5].
        // Step 2 (counter=2, exhausted): widen [0,5] ▽ [0,10] = [0, MAX].
        // Step 3 (counter=3, exhausted): widen [0,MAX] ▽ [0,15] = [0, MAX].
        let result = full_widening_sequence(&values, &cfg);
        assert_eq!(result, IntervalLattice::Interval { lo: 0, hi: i64::MAX });
    }
}
