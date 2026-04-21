// trust-cegar/lattice.rs: Abstract value lattices (#260)
//
// Provides lattice structures for abstract interpretation within the CEGAR
// framework. Supports interval, sign, and bitfield domains with widening
// and narrowing operators for fixpoint convergence.
//
// References:
//   Cousot, Cousot. "Abstract Interpretation" (POPL 1977).
//   Miné. "The Octagon Abstract Domain" (HOSC 2006).
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::fmt;

// ---------------------------------------------------------------------------
// Lattice trait
// ---------------------------------------------------------------------------

/// A lattice with join (least upper bound) and meet (greatest lower bound).
pub(crate) trait Lattice: Clone + PartialEq + fmt::Debug {
    /// Bottom element (least element).
    fn bottom() -> Self;

    /// Top element (greatest element).
    fn top() -> Self;

    /// Join (least upper bound).
    fn join(&self, other: &Self) -> Self;

    /// Meet (greatest lower bound).
    fn meet(&self, other: &Self) -> Self;

    /// Check if this is the bottom element.
    fn is_bottom(&self) -> bool;

    /// Check if this is the top element.
    fn is_top(&self) -> bool;

    /// Partial order: self <= other.
    fn leq(&self, other: &Self) -> bool;
}

/// Extension trait for lattices that support widening.
pub(crate) trait Widenable: Lattice {
    /// Widening operator for convergence acceleration.
    fn widen(&self, other: &Self) -> Self;

    /// Narrowing operator (optional refinement after widening).
    fn narrow(&self, other: &Self) -> Self;
}

// ---------------------------------------------------------------------------
// Interval lattice
// ---------------------------------------------------------------------------

/// An interval lattice over i64 values: [lo, hi] or bottom.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum IntervalLattice {
    /// No possible value (unreachable).
    Bottom,
    /// Values in [lo, hi].
    Interval { lo: i64, hi: i64 },
    /// All possible values.
    Top,
}

impl IntervalLattice {
    /// Create a single-value interval.
    #[must_use]
    pub(crate) fn constant(val: i64) -> Self {
        Self::Interval { lo: val, hi: val }
    }

    /// Create a bounded interval.
    #[must_use]
    pub(crate) fn range(lo: i64, hi: i64) -> Self {
        if lo > hi {
            Self::Bottom
        } else {
            Self::Interval { lo, hi }
        }
    }

    /// Check if a concrete value is in this interval.
    #[must_use]
    pub(crate) fn contains(&self, val: i64) -> bool {
        match self {
            Self::Bottom => false,
            Self::Interval { lo, hi } => val >= *lo && val <= *hi,
            Self::Top => true,
        }
    }

    /// Get the width of the interval, or None for bottom/top.
    #[must_use]
    pub(crate) fn width(&self) -> Option<u64> {
        match self {
            Self::Interval { lo, hi } => Some((*hi as u64).wrapping_sub(*lo as u64)),
            _ => None,
        }
    }
}

impl fmt::Display for IntervalLattice {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Bottom => write!(f, "⊥"),
            Self::Interval { lo, hi } => write!(f, "[{lo}, {hi}]"),
            Self::Top => write!(f, "⊤"),
        }
    }
}

impl Lattice for IntervalLattice {
    fn bottom() -> Self { Self::Bottom }
    fn top() -> Self { Self::Top }

    fn join(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Bottom, x) | (x, Self::Bottom) => x.clone(),
            (Self::Top, _) | (_, Self::Top) => Self::Top,
            (Self::Interval { lo: l1, hi: h1 }, Self::Interval { lo: l2, hi: h2 }) => {
                Self::Interval { lo: (*l1).min(*l2), hi: (*h1).max(*h2) }
            }
        }
    }

    fn meet(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Bottom, _) | (_, Self::Bottom) => Self::Bottom,
            (Self::Top, x) | (x, Self::Top) => x.clone(),
            (Self::Interval { lo: l1, hi: h1 }, Self::Interval { lo: l2, hi: h2 }) => {
                let lo = (*l1).max(*l2);
                let hi = (*h1).min(*h2);
                if lo > hi { Self::Bottom } else { Self::Interval { lo, hi } }
            }
        }
    }

    fn is_bottom(&self) -> bool { matches!(self, Self::Bottom) }
    fn is_top(&self) -> bool { matches!(self, Self::Top) }

    fn leq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Bottom, _) => true,
            (_, Self::Top) => true,
            (Self::Top, _) => other.is_top(),
            (_, Self::Bottom) => self.is_bottom(),
            (Self::Interval { lo: l1, hi: h1 }, Self::Interval { lo: l2, hi: h2 }) => {
                l2 <= l1 && h1 <= h2
            }
        }
    }
}

impl Widenable for IntervalLattice {
    fn widen(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Bottom, x) | (x, Self::Bottom) => x.clone(),
            (Self::Top, _) | (_, Self::Top) => Self::Top,
            (Self::Interval { lo: l1, hi: h1 }, Self::Interval { lo: l2, hi: h2 }) => {
                let lo = if l2 < l1 { i64::MIN } else { *l1 };
                let hi = if h2 > h1 { i64::MAX } else { *h1 };
                if lo == i64::MIN && hi == i64::MAX { Self::Top }
                else { Self::Interval { lo, hi } }
            }
        }
    }

    fn narrow(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Bottom, _) | (_, Self::Bottom) => Self::Bottom,
            (Self::Top, x) => x.clone(),
            (x, Self::Top) => x.clone(),
            (Self::Interval { lo: l1, hi: h1 }, Self::Interval { lo: l2, hi: h2 }) => {
                let lo = if *l1 == i64::MIN { *l2 } else { *l1 };
                let hi = if *h1 == i64::MAX { *h2 } else { *h1 };
                if lo > hi { Self::Bottom } else { Self::Interval { lo, hi } }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Sign lattice
// ---------------------------------------------------------------------------

/// Sign abstract domain: {⊥, Negative, Zero, Positive, NonNegative, NonPositive, ⊤}.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum SignLattice {
    Bottom,
    Negative,
    Zero,
    Positive,
    NonNegative,
    NonPositive,
    Top,
}

impl fmt::Display for SignLattice {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Bottom => write!(f, "⊥"),
            Self::Negative => write!(f, "<0"),
            Self::Zero => write!(f, "=0"),
            Self::Positive => write!(f, ">0"),
            Self::NonNegative => write!(f, "≥0"),
            Self::NonPositive => write!(f, "≤0"),
            Self::Top => write!(f, "⊤"),
        }
    }
}

impl SignLattice {
    /// Abstract a concrete value to its sign.
    #[must_use]
    pub(crate) fn from_value(val: i64) -> Self {
        if val < 0 { Self::Negative }
        else if val == 0 { Self::Zero }
        else { Self::Positive }
    }
}

impl Lattice for SignLattice {
    fn bottom() -> Self { Self::Bottom }
    fn top() -> Self { Self::Top }

    fn join(&self, other: &Self) -> Self {
        if self == other { return *self; }
        match (*self, *other) {
            (Self::Bottom, x) | (x, Self::Bottom) => x,
            (Self::Top, _) | (_, Self::Top) => Self::Top,
            // Same values handled by early return above
            (Self::Negative, Self::Zero) | (Self::Zero, Self::Negative) => Self::NonPositive,
            (Self::Positive, Self::Zero) | (Self::Zero, Self::Positive) => Self::NonNegative,
            (Self::Negative, Self::Positive) | (Self::Positive, Self::Negative) => Self::Top,
            (Self::NonNegative, Self::Negative) | (Self::Negative, Self::NonNegative) => Self::Top,
            (Self::NonPositive, Self::Positive) | (Self::Positive, Self::NonPositive) => Self::Top,
            (Self::NonNegative, Self::Zero) | (Self::Zero, Self::NonNegative) => Self::NonNegative,
            (Self::NonPositive, Self::Zero) | (Self::Zero, Self::NonPositive) => Self::NonPositive,
            (Self::NonNegative, Self::Positive) | (Self::Positive, Self::NonNegative) => Self::NonNegative,
            (Self::NonPositive, Self::Negative) | (Self::Negative, Self::NonPositive) => Self::NonPositive,
            (Self::NonNegative, Self::NonPositive) | (Self::NonPositive, Self::NonNegative) => Self::Top,
            _ => unreachable!("equal case handled above"),
        }
    }

    fn meet(&self, other: &Self) -> Self {
        if self == other { return *self; }
        match (*self, *other) {
            (Self::Bottom, _) | (_, Self::Bottom) => Self::Bottom,
            (Self::Top, x) | (x, Self::Top) => x,
            (Self::NonNegative, Self::Positive) | (Self::Positive, Self::NonNegative) => Self::Positive,
            (Self::NonNegative, Self::Zero) | (Self::Zero, Self::NonNegative) => Self::Zero,
            (Self::NonPositive, Self::Negative) | (Self::Negative, Self::NonPositive) => Self::Negative,
            (Self::NonPositive, Self::Zero) | (Self::Zero, Self::NonPositive) => Self::Zero,
            (Self::NonNegative, Self::NonPositive) | (Self::NonPositive, Self::NonNegative) => Self::Zero,
            (Self::NonNegative, Self::Negative) | (Self::Negative, Self::NonNegative) => Self::Bottom,
            (Self::NonPositive, Self::Positive) | (Self::Positive, Self::NonPositive) => Self::Bottom,
            (Self::Negative, Self::Zero) | (Self::Zero, Self::Negative) => Self::Bottom,
            (Self::Negative, Self::Positive) | (Self::Positive, Self::Negative) => Self::Bottom,
            (Self::Positive, Self::Zero) | (Self::Zero, Self::Positive) => Self::Bottom,
            _ => unreachable!("equal case handled above"),
        }
    }

    fn is_bottom(&self) -> bool { *self == Self::Bottom }
    fn is_top(&self) -> bool { *self == Self::Top }

    fn leq(&self, other: &Self) -> bool {
        *self == Self::Bottom || *other == Self::Top || *self == *other
            || (*self == Self::Negative && *other == Self::NonPositive)
            || (*self == Self::Positive && *other == Self::NonNegative)
            || (*self == Self::Zero && (*other == Self::NonNegative || *other == Self::NonPositive))
    }
}

// ---------------------------------------------------------------------------
// Product lattice
// ---------------------------------------------------------------------------

/// Product of two lattices: (A, B) with component-wise operations.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct ProductLattice<A: Lattice, B: Lattice> {
    pub first: A,
    pub second: B,
}

impl<A: Lattice, B: Lattice> ProductLattice<A, B> {
    pub(crate) fn new(first: A, second: B) -> Self {
        Self { first, second }
    }
}

impl<A: Lattice, B: Lattice> Lattice for ProductLattice<A, B> {
    fn bottom() -> Self { Self { first: A::bottom(), second: B::bottom() } }
    fn top() -> Self { Self { first: A::top(), second: B::top() } }

    fn join(&self, other: &Self) -> Self {
        Self {
            first: self.first.join(&other.first),
            second: self.second.join(&other.second),
        }
    }

    fn meet(&self, other: &Self) -> Self {
        Self {
            first: self.first.meet(&other.first),
            second: self.second.meet(&other.second),
        }
    }

    fn is_bottom(&self) -> bool { self.first.is_bottom() && self.second.is_bottom() }
    fn is_top(&self) -> bool { self.first.is_top() && self.second.is_top() }

    fn leq(&self, other: &Self) -> bool {
        self.first.leq(&other.first) && self.second.leq(&other.second)
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // Interval lattice tests

    #[test]
    fn test_interval_constant() {
        let c = IntervalLattice::constant(42);
        assert!(c.contains(42));
        assert!(!c.contains(41));
    }

    #[test]
    fn test_interval_range() {
        let r = IntervalLattice::range(1, 10);
        assert!(r.contains(1));
        assert!(r.contains(10));
        assert!(!r.contains(0));
        assert!(!r.contains(11));
    }

    #[test]
    fn test_interval_invalid_range_is_bottom() {
        let r = IntervalLattice::range(10, 1);
        assert!(r.is_bottom());
    }

    #[test]
    fn test_interval_join() {
        let a = IntervalLattice::range(1, 5);
        let b = IntervalLattice::range(3, 10);
        assert_eq!(a.join(&b), IntervalLattice::range(1, 10));
    }

    #[test]
    fn test_interval_meet() {
        let a = IntervalLattice::range(1, 10);
        let b = IntervalLattice::range(5, 15);
        assert_eq!(a.meet(&b), IntervalLattice::range(5, 10));
    }

    #[test]
    fn test_interval_meet_disjoint() {
        let a = IntervalLattice::range(1, 3);
        let b = IntervalLattice::range(5, 10);
        assert!(a.meet(&b).is_bottom());
    }

    #[test]
    fn test_interval_join_with_bottom() {
        let a = IntervalLattice::range(1, 5);
        assert_eq!(a.join(&IntervalLattice::Bottom), a);
        assert_eq!(IntervalLattice::Bottom.join(&a), a);
    }

    #[test]
    fn test_interval_leq() {
        let a = IntervalLattice::range(2, 5);
        let b = IntervalLattice::range(1, 10);
        assert!(a.leq(&b));
        assert!(!b.leq(&a));
        assert!(IntervalLattice::Bottom.leq(&a));
        assert!(a.leq(&IntervalLattice::Top));
    }

    #[test]
    fn test_interval_widen() {
        let a = IntervalLattice::range(0, 5);
        let b = IntervalLattice::range(0, 10);
        let w = a.widen(&b);
        // hi grew, so widened to MAX
        assert_eq!(w, IntervalLattice::Interval { lo: 0, hi: i64::MAX });
    }

    #[test]
    fn test_interval_narrow() {
        let a = IntervalLattice::Interval { lo: 0, hi: i64::MAX };
        let b = IntervalLattice::range(0, 100);
        let n = a.narrow(&b);
        assert_eq!(n, IntervalLattice::range(0, 100));
    }

    #[test]
    fn test_interval_width() {
        assert_eq!(IntervalLattice::constant(5).width(), Some(0));
        assert_eq!(IntervalLattice::range(0, 10).width(), Some(10));
        assert!(IntervalLattice::Bottom.width().is_none());
        assert!(IntervalLattice::Top.width().is_none());
    }

    #[test]
    fn test_interval_display() {
        assert_eq!(IntervalLattice::Bottom.to_string(), "⊥");
        assert_eq!(IntervalLattice::Top.to_string(), "⊤");
        assert_eq!(IntervalLattice::range(1, 10).to_string(), "[1, 10]");
    }

    // Sign lattice tests

    #[test]
    fn test_sign_from_value() {
        assert_eq!(SignLattice::from_value(-5), SignLattice::Negative);
        assert_eq!(SignLattice::from_value(0), SignLattice::Zero);
        assert_eq!(SignLattice::from_value(3), SignLattice::Positive);
    }

    #[test]
    fn test_sign_join() {
        assert_eq!(SignLattice::Negative.join(&SignLattice::Zero), SignLattice::NonPositive);
        assert_eq!(SignLattice::Positive.join(&SignLattice::Zero), SignLattice::NonNegative);
        assert_eq!(SignLattice::Negative.join(&SignLattice::Positive), SignLattice::Top);
    }

    #[test]
    fn test_sign_meet() {
        assert_eq!(SignLattice::NonNegative.meet(&SignLattice::NonPositive), SignLattice::Zero);
        assert_eq!(SignLattice::NonNegative.meet(&SignLattice::Positive), SignLattice::Positive);
        assert_eq!(SignLattice::Negative.meet(&SignLattice::Positive), SignLattice::Bottom);
    }

    #[test]
    fn test_sign_leq() {
        assert!(SignLattice::Bottom.leq(&SignLattice::Negative));
        assert!(SignLattice::Zero.leq(&SignLattice::NonNegative));
        assert!(SignLattice::Positive.leq(&SignLattice::NonNegative));
        assert!(!SignLattice::Negative.leq(&SignLattice::NonNegative));
    }

    #[test]
    fn test_sign_display() {
        assert_eq!(SignLattice::Negative.to_string(), "<0");
        assert_eq!(SignLattice::NonNegative.to_string(), "≥0");
    }

    // Product lattice tests

    #[test]
    fn test_product_join() {
        let a = ProductLattice::new(IntervalLattice::range(1, 5), SignLattice::Positive);
        let b = ProductLattice::new(IntervalLattice::range(3, 10), SignLattice::Zero);
        let j = a.join(&b);
        assert_eq!(j.first, IntervalLattice::range(1, 10));
        assert_eq!(j.second, SignLattice::NonNegative);
    }

    #[test]
    fn test_product_bottom_top() {
        let bot: ProductLattice<IntervalLattice, SignLattice> = ProductLattice::bottom();
        assert!(bot.is_bottom());
        let top: ProductLattice<IntervalLattice, SignLattice> = ProductLattice::top();
        assert!(top.is_top());
    }

    #[test]
    fn test_product_leq() {
        let a = ProductLattice::new(IntervalLattice::range(2, 5), SignLattice::Positive);
        let b = ProductLattice::new(IntervalLattice::range(1, 10), SignLattice::NonNegative);
        assert!(a.leq(&b));
        assert!(!b.leq(&a));
    }
}
