// trust-convergence/fixpoint_widening.rs: Abstract fixpoint computation with widening.
//
// Provides generic abstract fixpoint iteration with configurable widening and
// narrowing operators. The `AbstractDomain` trait defines the lattice operations
// and `FixpointEngine` drives the iteration to convergence.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

/// Trait for abstract domains used in fixpoint computation.
///
/// Implementors define a lattice with join (least upper bound), meet (greatest
/// lower bound), widening (over-approximation for convergence), and narrowing
/// (precision recovery after widening).
pub(crate) trait AbstractDomain: Clone + PartialEq + std::fmt::Debug {
    /// Least upper bound: smallest element above both `self` and `other`.
    fn join(&self, other: &Self) -> Self;

    /// Greatest lower bound: largest element below both `self` and `other`.
    fn meet(&self, other: &Self) -> Self;

    /// Widening operator: over-approximate to ensure ascending chains stabilize.
    ///
    /// Must satisfy: `self <= widen(self, other)` and the ascending chain
    /// `x0, widen(x0, x1), widen(widen(x0, x1), x2), ...` eventually stabilizes.
    fn widen(&self, other: &Self) -> Self;

    /// Narrowing operator: recover precision after widening.
    ///
    /// Must satisfy: `other <= narrow(self, other) <= self` when `other <= self`.
    fn narrow(&self, other: &Self) -> Self;

    /// Whether this element is the bottom of the lattice (no information).
    fn is_bottom(&self) -> bool;

    /// Whether this element is the top of the lattice (all information).
    fn is_top(&self) -> bool;

    /// Partial order: `self <= other` in the lattice ordering.
    fn leq(&self, other: &Self) -> bool;
}

/// Configuration for the fixpoint engine.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct WidenConfig {
    /// Number of iterations to delay before applying widening.
    /// During the delay, plain join is used instead.
    pub delay_count: usize,
    /// Widening thresholds: if the domain supports threshold widening,
    /// these values guide where widening jumps to.
    pub thresholds: Vec<i64>,
    /// Number of narrowing passes to apply after the widened fixpoint is reached.
    pub narrowing_passes: usize,
    /// Maximum total iterations (widening + narrowing) before giving up.
    pub max_iterations: usize,
}

impl WidenConfig {
    /// Create a config with the given delay and narrowing passes.
    #[must_use]
    pub fn new(delay_count: usize, narrowing_passes: usize) -> Self {
        Self {
            delay_count,
            thresholds: Vec::new(),
            narrowing_passes,
            max_iterations: 1000,
        }
    }

    /// Add widening thresholds.
    #[must_use]
    pub fn with_thresholds(mut self, thresholds: Vec<i64>) -> Self {
        self.thresholds = thresholds;
        self
    }

    /// Set the maximum total iteration count.
    #[must_use]
    pub fn with_max_iterations(mut self, max: usize) -> Self {
        self.max_iterations = max;
        self
    }
}

impl Default for WidenConfig {
    fn default() -> Self {
        Self {
            delay_count: 3,
            thresholds: Vec::new(),
            narrowing_passes: 2,
            max_iterations: 1000,
        }
    }
}

/// Result of a fixpoint computation.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct FixpointResult<D: AbstractDomain> {
    /// The computed abstract state at the fixpoint.
    pub state: D,
    /// Number of widening iterations performed.
    pub widening_iterations: usize,
    /// Number of narrowing iterations performed.
    pub narrowing_iterations: usize,
    /// Whether the fixpoint was reached within the iteration limit.
    pub converged: bool,
}

impl<D: AbstractDomain> FixpointResult<D> {
    /// Total iterations (widening + narrowing).
    #[must_use]
    pub fn total_iterations(&self) -> usize {
        self.widening_iterations + self.narrowing_iterations
    }
}

/// Engine that computes abstract fixpoints with widening and narrowing.
#[derive(Debug, Clone)]
pub(crate) struct FixpointEngine {
    config: WidenConfig,
}

impl FixpointEngine {
    /// Create a new engine with the given configuration.
    #[must_use]
    pub fn new(config: WidenConfig) -> Self {
        Self { config }
    }

    /// Create an engine with default configuration.
    #[must_use]
    pub fn with_defaults() -> Self {
        Self { config: WidenConfig::default() }
    }

    /// Access the configuration.
    #[must_use]
    pub fn config(&self) -> &WidenConfig {
        &self.config
    }

    /// Compute the fixpoint of `transfer` starting from `init`.
    ///
    /// The transfer function models one iteration of the abstract semantics.
    /// Widening is applied after `delay_count` iterations to force convergence.
    /// Narrowing is then applied for up to `narrowing_passes` iterations to
    /// recover precision.
    pub fn compute_fixpoint<D, F>(&self, init: D, transfer: F) -> FixpointResult<D>
    where
        D: AbstractDomain,
        F: Fn(&D) -> D,
    {
        let widened = self.ascending_with_widening(&init, &transfer);
        if !widened.converged {
            return widened;
        }
        self.apply_narrowing(widened, &transfer)
    }

    /// Ascending iteration with widening to reach a post-fixpoint.
    fn ascending_with_widening<D, F>(&self, init: &D, transfer: &F) -> FixpointResult<D>
    where
        D: AbstractDomain,
        F: Fn(&D) -> D,
    {
        let mut current = init.clone();
        let mut iteration = 0;

        loop {
            if iteration >= self.config.max_iterations {
                return FixpointResult {
                    state: current,
                    widening_iterations: iteration,
                    narrowing_iterations: 0,
                    converged: false,
                };
            }

            let next = transfer(&current);
            let joined = current.join(&next);

            // Check if we have reached a fixpoint (no new information).
            if joined.leq(&current) {
                return FixpointResult {
                    state: current,
                    widening_iterations: iteration,
                    narrowing_iterations: 0,
                    converged: true,
                };
            }

            // Apply widening after the delay period.
            current = if iteration >= self.config.delay_count {
                current.widen(&joined)
            } else {
                joined
            };

            iteration += 1;
        }
    }

    /// Apply narrowing passes to recover precision from a widened fixpoint.
    ///
    /// Narrowing refines the post-fixpoint by computing `narrow(current, transfer(current))`.
    /// The transfer result is a tighter approximation than the widened fixpoint, and
    /// narrowing uses it to shrink the over-approximation.
    fn apply_narrowing<D, F>(
        &self,
        mut result: FixpointResult<D>,
        transfer: &F,
    ) -> FixpointResult<D>
    where
        D: AbstractDomain,
        F: Fn(&D) -> D,
    {
        let max_narrow = self.config.narrowing_passes;
        let mut narrowing_count = 0;

        for _ in 0..max_narrow {
            if result.total_iterations() >= self.config.max_iterations {
                break;
            }

            let next = transfer(&result.state);
            let narrowed = result.state.narrow(&next);

            if narrowed == result.state {
                break;
            }

            result.state = narrowed;
            narrowing_count += 1;
        }

        result.narrowing_iterations = narrowing_count;
        result
    }
}

/// Compute a fixpoint with the given configuration, init state, and transfer function.
///
/// Convenience wrapper around [`FixpointEngine::compute_fixpoint`].
pub(crate) fn compute_fixpoint<D, F>(config: &WidenConfig, init: D, transfer: F) -> FixpointResult<D>
where
    D: AbstractDomain,
    F: Fn(&D) -> D,
{
    let engine = FixpointEngine::new(config.clone());
    engine.compute_fixpoint(init, transfer)
}

/// Apply narrowing to an existing fixpoint result with a given transfer function.
///
/// Convenience wrapper for post-hoc narrowing on an already-computed fixpoint.
pub(crate) fn apply_narrowing<D, F>(
    state: D,
    transfer: F,
    passes: usize,
) -> D
where
    D: AbstractDomain,
    F: Fn(&D) -> D,
{
    let mut current = state;
    for _ in 0..passes {
        let next = transfer(&current);
        let narrowed = current.narrow(&next);
        if narrowed == current {
            break;
        }
        current = narrowed;
    }
    current
}

// ---------------------------------------------------------------------------
// IntervalDomain: concrete AbstractDomain implementation with i64 bounds
// ---------------------------------------------------------------------------

/// An interval abstract domain over i64 values: [lo, hi].
///
/// Represents the set of integers in the closed interval `[lo, hi]`.
/// Bottom is represented by `lo > hi`. Top is `[i64::MIN, i64::MAX]`.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct IntervalDomain {
    /// Lower bound (inclusive).
    pub lo: i64,
    /// Upper bound (inclusive).
    pub hi: i64,
}

impl IntervalDomain {
    /// Create a new interval `[lo, hi]`.
    #[must_use]
    pub fn new(lo: i64, hi: i64) -> Self {
        Self { lo, hi }
    }

    /// Create a singleton interval `[v, v]`.
    #[must_use]
    pub fn singleton(v: i64) -> Self {
        Self { lo: v, hi: v }
    }

    /// The bottom element (empty interval).
    #[must_use]
    pub fn bottom() -> Self {
        Self { lo: 1, hi: 0 }
    }

    /// The top element (all integers).
    #[must_use]
    pub fn top() -> Self {
        Self { lo: i64::MIN, hi: i64::MAX }
    }
}

impl AbstractDomain for IntervalDomain {
    fn join(&self, other: &Self) -> Self {
        if self.is_bottom() {
            return other.clone();
        }
        if other.is_bottom() {
            return self.clone();
        }
        Self {
            lo: self.lo.min(other.lo),
            hi: self.hi.max(other.hi),
        }
    }

    fn meet(&self, other: &Self) -> Self {
        if self.is_bottom() || other.is_bottom() {
            return Self::bottom();
        }
        let lo = self.lo.max(other.lo);
        let hi = self.hi.min(other.hi);
        if lo > hi {
            Self::bottom()
        } else {
            Self { lo, hi }
        }
    }

    fn widen(&self, other: &Self) -> Self {
        if self.is_bottom() {
            return other.clone();
        }
        if other.is_bottom() {
            return self.clone();
        }
        let lo = if other.lo < self.lo { i64::MIN } else { self.lo };
        let hi = if other.hi > self.hi { i64::MAX } else { self.hi };
        Self { lo, hi }
    }

    fn narrow(&self, other: &Self) -> Self {
        if self.is_bottom() || other.is_bottom() {
            return other.clone();
        }
        let lo = if self.lo == i64::MIN { other.lo } else { self.lo };
        let hi = if self.hi == i64::MAX { other.hi } else { self.hi };
        Self { lo, hi }
    }

    fn is_bottom(&self) -> bool {
        self.lo > self.hi
    }

    fn is_top(&self) -> bool {
        self.lo == i64::MIN && self.hi == i64::MAX
    }

    fn leq(&self, other: &Self) -> bool {
        if self.is_bottom() {
            return true;
        }
        if other.is_bottom() {
            return false;
        }
        other.lo <= self.lo && self.hi <= other.hi
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // --- IntervalDomain lattice operations ---

    #[test]
    fn test_interval_bottom_is_bottom() {
        let b = IntervalDomain::bottom();
        assert!(b.is_bottom());
        assert!(!b.is_top());
    }

    #[test]
    fn test_interval_top_is_top() {
        let t = IntervalDomain::top();
        assert!(t.is_top());
        assert!(!t.is_bottom());
    }

    #[test]
    fn test_interval_singleton() {
        let s = IntervalDomain::singleton(42);
        assert!(!s.is_bottom());
        assert!(!s.is_top());
        assert_eq!(s.lo, 42);
        assert_eq!(s.hi, 42);
    }

    #[test]
    fn test_interval_join_with_bottom() {
        let a = IntervalDomain::new(1, 5);
        let b = IntervalDomain::bottom();
        assert_eq!(a.join(&b), a);
        assert_eq!(b.join(&a), a);
    }

    #[test]
    fn test_interval_join_overlapping() {
        let a = IntervalDomain::new(1, 5);
        let b = IntervalDomain::new(3, 10);
        let j = a.join(&b);
        assert_eq!(j.lo, 1);
        assert_eq!(j.hi, 10);
    }

    #[test]
    fn test_interval_meet_overlapping() {
        let a = IntervalDomain::new(1, 5);
        let b = IntervalDomain::new(3, 10);
        let m = a.meet(&b);
        assert_eq!(m.lo, 3);
        assert_eq!(m.hi, 5);
    }

    #[test]
    fn test_interval_meet_disjoint_is_bottom() {
        let a = IntervalDomain::new(1, 3);
        let b = IntervalDomain::new(5, 10);
        let m = a.meet(&b);
        assert!(m.is_bottom());
    }

    #[test]
    fn test_interval_leq() {
        let a = IntervalDomain::new(2, 4);
        let b = IntervalDomain::new(1, 5);
        assert!(a.leq(&b));
        assert!(!b.leq(&a));
    }

    #[test]
    fn test_interval_bottom_leq_everything() {
        let b = IntervalDomain::bottom();
        let a = IntervalDomain::new(1, 5);
        assert!(b.leq(&a));
        assert!(b.leq(&IntervalDomain::top()));
    }

    #[test]
    fn test_interval_widen_lower_decreases() {
        let old = IntervalDomain::new(0, 10);
        let new = IntervalDomain::new(-5, 10);
        let w = old.widen(&new);
        assert_eq!(w.lo, i64::MIN);
        assert_eq!(w.hi, 10);
    }

    #[test]
    fn test_interval_widen_upper_increases() {
        let old = IntervalDomain::new(0, 10);
        let new = IntervalDomain::new(0, 15);
        let w = old.widen(&new);
        assert_eq!(w.lo, 0);
        assert_eq!(w.hi, i64::MAX);
    }

    #[test]
    fn test_interval_widen_stable() {
        let old = IntervalDomain::new(0, 10);
        let new = IntervalDomain::new(2, 8);
        let w = old.widen(&new);
        assert_eq!(w.lo, 0);
        assert_eq!(w.hi, 10);
    }

    #[test]
    fn test_interval_narrow_from_top() {
        let wide = IntervalDomain::top();
        let precise = IntervalDomain::new(3, 7);
        let n = wide.narrow(&precise);
        assert_eq!(n.lo, 3);
        assert_eq!(n.hi, 7);
    }

    #[test]
    fn test_interval_narrow_partial() {
        let wide = IntervalDomain::new(i64::MIN, 10);
        let precise = IntervalDomain::new(2, 10);
        let n = wide.narrow(&precise);
        assert_eq!(n.lo, 2);
        assert_eq!(n.hi, 10);
    }

    // --- WidenConfig ---

    #[test]
    fn test_widen_config_default() {
        let c = WidenConfig::default();
        assert_eq!(c.delay_count, 3);
        assert_eq!(c.narrowing_passes, 2);
        assert_eq!(c.max_iterations, 1000);
        assert!(c.thresholds.is_empty());
    }

    #[test]
    fn test_widen_config_builder() {
        let c = WidenConfig::new(5, 3)
            .with_thresholds(vec![0, 10, 100])
            .with_max_iterations(500);
        assert_eq!(c.delay_count, 5);
        assert_eq!(c.narrowing_passes, 3);
        assert_eq!(c.max_iterations, 500);
        assert_eq!(c.thresholds, vec![0, 10, 100]);
    }

    // --- FixpointEngine: simple convergence ---

    #[test]
    fn test_fixpoint_constant_transfer() {
        // Transfer always returns the same state => immediate convergence.
        let config = WidenConfig::new(0, 0).with_max_iterations(100);
        let init = IntervalDomain::new(0, 0);
        let result = compute_fixpoint(&config, init, |_| IntervalDomain::new(0, 0));
        assert!(result.converged);
        assert_eq!(result.widening_iterations, 0);
        assert_eq!(result.state, IntervalDomain::new(0, 0));
    }

    #[test]
    fn test_fixpoint_monotone_bounded_without_widening() {
        // Transfer grows the interval by 1 each step up to [0, 5].
        let config = WidenConfig::new(100, 0).with_max_iterations(100);
        let init = IntervalDomain::new(0, 0);
        let result = compute_fixpoint(&config, init, |d| {
            let new_hi = (d.hi + 1).min(5);
            IntervalDomain::new(0, new_hi)
        });
        assert!(result.converged);
        assert_eq!(result.state, IntervalDomain::new(0, 5));
        assert_eq!(result.widening_iterations, 5);
    }

    #[test]
    fn test_fixpoint_unbounded_needs_widening() {
        // Transfer grows upper bound by 1 each step (unbounded ascending chain).
        // Without widening, would never converge. With delay=2, widening kicks in.
        let config = WidenConfig::new(2, 1).with_max_iterations(100);
        let init = IntervalDomain::new(0, 0);
        let result = compute_fixpoint(&config, init, |d| {
            IntervalDomain::new(0, d.hi.saturating_add(1))
        });
        assert!(result.converged);
        // After widening, upper bound jumps to i64::MAX.
        assert_eq!(result.state.lo, 0);
        assert_eq!(result.state.hi, i64::MAX);
    }

    #[test]
    fn test_fixpoint_with_narrowing_recovers_precision() {
        // Transfer: always produce [0, 10]. Widening overshoots to [0, MAX].
        // Narrowing should recover [0, 10].
        let config = WidenConfig::new(0, 5).with_max_iterations(100);
        let init = IntervalDomain::new(0, 0);
        let result = compute_fixpoint(&config, init, |_d| {
            IntervalDomain::new(0, 10)
        });
        assert!(result.converged);
        // After widening, hi goes to MAX. Narrowing recovers to 10.
        assert_eq!(result.state.lo, 0);
        assert_eq!(result.state.hi, 10);
        assert!(result.narrowing_iterations > 0);
    }

    #[test]
    fn test_fixpoint_max_iterations_exceeded() {
        // Transfer keeps growing; delay is high so widening never kicks in.
        let config = WidenConfig::new(100, 0).with_max_iterations(10);
        let init = IntervalDomain::new(0, 0);
        let counter = std::cell::Cell::new(0usize);
        let result = compute_fixpoint(&config, init, |_d| {
            counter.set(counter.get() + 1);
            IntervalDomain::new(0, counter.get() as i64)
        });
        assert!(!result.converged);
        assert_eq!(result.widening_iterations, 10);
    }

    #[test]
    fn test_fixpoint_bottom_init() {
        // Start from bottom, transfer produces [0, 3].
        let config = WidenConfig::new(0, 0).with_max_iterations(100);
        let init = IntervalDomain::bottom();
        let result = compute_fixpoint(&config, init, |_| IntervalDomain::new(0, 3));
        assert!(result.converged);
        // After widening from bottom: widen(bottom, [0,3]) = [0,3].
        // Then widen([0,3], join([0,3],[0,3])) = [0,3]. Stable.
        assert_eq!(result.state, IntervalDomain::new(0, 3));
    }

    #[test]
    fn test_fixpoint_result_total_iterations() {
        let result = FixpointResult {
            state: IntervalDomain::new(0, 5),
            widening_iterations: 7,
            narrowing_iterations: 3,
            converged: true,
        };
        assert_eq!(result.total_iterations(), 10);
    }

    #[test]
    fn test_apply_narrowing_standalone() {
        // Start from an over-approximate [0, MAX], transfer always gives [0, 10].
        let wide = IntervalDomain::new(0, i64::MAX);
        let result = apply_narrowing(wide, |_| IntervalDomain::new(0, 10), 5);
        assert_eq!(result.lo, 0);
        assert_eq!(result.hi, 10);
    }

    #[test]
    fn test_engine_with_defaults() {
        let engine = FixpointEngine::with_defaults();
        assert_eq!(engine.config().delay_count, 3);
        assert_eq!(engine.config().narrowing_passes, 2);
    }

    // --- Descending lower bound with widening ---

    #[test]
    fn test_fixpoint_descending_lower_bound() {
        // Transfer decreases lower bound by 1 each step (saturating).
        let config = WidenConfig::new(2, 1).with_max_iterations(100);
        let init = IntervalDomain::new(0, 0);
        let result = compute_fixpoint(&config, init, |d| {
            IntervalDomain::new(d.lo.saturating_sub(1), 0)
        });
        assert!(result.converged);
        assert_eq!(result.state.lo, i64::MIN);
        assert_eq!(result.state.hi, 0);
    }
}
