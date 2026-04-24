// trust-cegar/abstract_lattice.rs: Abstract domain lattice operations (#330)
//
// Provides a unified `LatticeElement` enum with free-function lattice operations
// for abstract interpretation in CEGAR. Supports interval, sign, congruence, and
// product domains with widening/narrowing for fixpoint convergence.
//
// Complements the trait-based `lattice.rs` with a concrete enum approach suitable
// for heterogeneous domain combinations in the CEGAR refinement loop.
//
// References:
//   Cousot, Cousot. "Abstract Interpretation" (POPL 1977).
//   Granger. "Static Analysis of Congruence Properties" (SAS 1997).
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::fmt;

// ---------------------------------------------------------------------------
// Sign domain
// ---------------------------------------------------------------------------

/// Sign abstract values for the sign domain.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum SignValue {
    Negative,
    Zero,
    Positive,
    NonNegative,
    NonPositive,
    NonZero,
    AnySign,
}

impl fmt::Display for SignValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Negative => write!(f, "<0"),
            Self::Zero => write!(f, "=0"),
            Self::Positive => write!(f, ">0"),
            Self::NonNegative => write!(f, ">=0"),
            Self::NonPositive => write!(f, "<=0"),
            Self::NonZero => write!(f, "!=0"),
            Self::AnySign => write!(f, "?"),
        }
    }
}

// ---------------------------------------------------------------------------
// Lattice element
// ---------------------------------------------------------------------------

/// A unified lattice element supporting multiple abstract domains.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum LatticeElement {
    /// Least element -- no concrete values.
    Bottom,
    /// Greatest element -- all concrete values.
    Top,
    /// Interval domain: [lo, hi].
    Interval { lo: i64, hi: i64 },
    /// Sign domain.
    Sign(SignValue),
    /// Congruence domain: value === remainder (mod modulus).
    Congruence { modulus: u64, remainder: u64 },
    /// Product of two lattice elements.
    Product(Box<LatticeElement>, Box<LatticeElement>),
}

impl fmt::Display for LatticeElement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Bottom => write!(f, "bot"),
            Self::Top => write!(f, "top"),
            Self::Interval { lo, hi } => write!(f, "[{lo}, {hi}]"),
            Self::Sign(s) => write!(f, "sign({s})"),
            Self::Congruence { modulus, remainder } => {
                write!(f, "{remainder} (mod {modulus})")
            }
            Self::Product(a, b) => write!(f, "({a}, {b})"),
        }
    }
}

// ---------------------------------------------------------------------------
// Lattice predicates
// ---------------------------------------------------------------------------

/// Returns true if the element is the bottom (least) element.
#[must_use]
pub fn is_bottom(e: &LatticeElement) -> bool {
    matches!(e, LatticeElement::Bottom)
}

/// Returns true if the element is the top (greatest) element.
#[must_use]
pub fn is_top(e: &LatticeElement) -> bool {
    matches!(e, LatticeElement::Top)
}

/// Returns true if `a` includes (is greater than or equal to) `b` in the lattice order.
///
/// `includes(a, b)` means b <= a, i.e., every concrete value in b is also in a.
#[must_use]
pub fn includes(a: &LatticeElement, b: &LatticeElement) -> bool {
    if is_bottom(b) || is_top(a) {
        return true;
    }
    if is_top(b) || is_bottom(a) {
        return false;
    }
    match (a, b) {
        (
            LatticeElement::Interval { lo: l1, hi: h1 },
            LatticeElement::Interval { lo: l2, hi: h2 },
        ) => l1 <= l2 && h2 <= h1,
        (LatticeElement::Sign(s1), LatticeElement::Sign(s2)) => sign_includes(s1, s2),
        (
            LatticeElement::Congruence { modulus: m1, remainder: r1 },
            LatticeElement::Congruence { modulus: m2, remainder: r2 },
        ) => {
            // m2 divides m1, and r2 === r1 (mod m1)
            if *m1 == 0 {
                return *m2 == 0 && r1 == r2;
            }
            *m2 % *m1 == 0 && *r2 % *m1 == *r1 % *m1
        }
        (LatticeElement::Product(a1, a2), LatticeElement::Product(b1, b2)) => {
            includes(a1, b1) && includes(a2, b2)
        }
        _ => false,
    }
}

/// Check if sign `a` includes sign `b`.
fn sign_includes(a: &SignValue, b: &SignValue) -> bool {
    if a == b {
        return true;
    }
    match a {
        SignValue::AnySign => true,
        SignValue::NonNegative => matches!(b, SignValue::Zero | SignValue::Positive),
        SignValue::NonPositive => matches!(b, SignValue::Zero | SignValue::Negative),
        SignValue::NonZero => matches!(b, SignValue::Negative | SignValue::Positive),
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Join (least upper bound)
// ---------------------------------------------------------------------------

/// Compute the join (least upper bound) of two lattice elements.
#[must_use]
pub fn join(a: &LatticeElement, b: &LatticeElement) -> LatticeElement {
    if is_bottom(a) {
        return b.clone();
    }
    if is_bottom(b) {
        return a.clone();
    }
    if is_top(a) || is_top(b) {
        return LatticeElement::Top;
    }
    match (a, b) {
        (
            LatticeElement::Interval { lo: l1, hi: h1 },
            LatticeElement::Interval { lo: l2, hi: h2 },
        ) => {
            let (lo, hi) = interval_join((*l1, *h1), (*l2, *h2));
            LatticeElement::Interval { lo, hi }
        }
        (LatticeElement::Sign(s1), LatticeElement::Sign(s2)) => {
            let result = sign_join(s1, s2);
            if result == SignValue::AnySign {
                LatticeElement::Top
            } else {
                LatticeElement::Sign(result)
            }
        }
        (
            LatticeElement::Congruence { modulus: m1, remainder: r1 },
            LatticeElement::Congruence { modulus: m2, remainder: r2 },
        ) => {
            if m1 == m2 && r1 == r2 {
                return a.clone();
            }
            // Join of congruences: gcd of moduli, check remainder compatibility
            let g = gcd(*m1, *m2);
            if g == 0 {
                LatticeElement::Top
            } else {
                let rem = *r1 % g;
                let rem2 = *r2 % g;
                if rem == rem2 {
                    LatticeElement::Congruence { modulus: g, remainder: rem }
                } else {
                    LatticeElement::Top
                }
            }
        }
        (LatticeElement::Product(a1, a2), LatticeElement::Product(b1, b2)) => {
            LatticeElement::Product(Box::new(join(a1, b1)), Box::new(join(a2, b2)))
        }
        _ => LatticeElement::Top,
    }
}

// ---------------------------------------------------------------------------
// Meet (greatest lower bound)
// ---------------------------------------------------------------------------

/// Compute the meet (greatest lower bound) of two lattice elements.
#[must_use]
pub fn meet(a: &LatticeElement, b: &LatticeElement) -> LatticeElement {
    if is_top(a) {
        return b.clone();
    }
    if is_top(b) {
        return a.clone();
    }
    if is_bottom(a) || is_bottom(b) {
        return LatticeElement::Bottom;
    }
    match (a, b) {
        (
            LatticeElement::Interval { lo: l1, hi: h1 },
            LatticeElement::Interval { lo: l2, hi: h2 },
        ) => {
            let lo = (*l1).max(*l2);
            let hi = (*h1).min(*h2);
            if lo > hi { LatticeElement::Bottom } else { LatticeElement::Interval { lo, hi } }
        }
        (LatticeElement::Sign(s1), LatticeElement::Sign(s2)) => {
            let result = sign_meet(s1, s2);
            match result {
                None => LatticeElement::Bottom,
                Some(s) => LatticeElement::Sign(s),
            }
        }
        (
            LatticeElement::Congruence { modulus: m1, remainder: r1 },
            LatticeElement::Congruence { modulus: m2, remainder: r2 },
        ) => {
            // Meet of congruences: lcm of moduli if remainders compatible
            let l = lcm(*m1, *m2);
            if l == 0 {
                if r1 == r2 {
                    return a.clone();
                }
                return LatticeElement::Bottom;
            }
            // Check if there exists x such that x === r1 (mod m1) and x === r2 (mod m2)
            // by CRT: need r1 === r2 (mod gcd(m1, m2))
            let g = gcd(*m1, *m2);
            if g > 0 && (*r1 % g) != (*r2 % g) {
                LatticeElement::Bottom
            } else {
                // CRT solution: remainder is r1 mod lcm (simplified)
                LatticeElement::Congruence { modulus: l, remainder: *r1 % l }
            }
        }
        (LatticeElement::Product(a1, a2), LatticeElement::Product(b1, b2)) => {
            let m1 = meet(a1, b1);
            let m2 = meet(a2, b2);
            if is_bottom(&m1) || is_bottom(&m2) {
                LatticeElement::Bottom
            } else {
                LatticeElement::Product(Box::new(m1), Box::new(m2))
            }
        }
        _ => LatticeElement::Bottom,
    }
}

// ---------------------------------------------------------------------------
// Widening
// ---------------------------------------------------------------------------

/// Widening operator for convergence acceleration.
///
/// Ensures termination of fixpoint iteration by extrapolating to limits
/// when bounds grow.
#[must_use]
pub fn widen(a: &LatticeElement, b: &LatticeElement) -> LatticeElement {
    if is_bottom(a) {
        return b.clone();
    }
    if is_bottom(b) {
        return a.clone();
    }
    if is_top(a) || is_top(b) {
        return LatticeElement::Top;
    }
    match (a, b) {
        (
            LatticeElement::Interval { lo: l1, hi: h1 },
            LatticeElement::Interval { lo: l2, hi: h2 },
        ) => {
            let (lo, hi) = interval_widen((*l1, *h1), (*l2, *h2));
            if lo == i64::MIN && hi == i64::MAX {
                LatticeElement::Top
            } else {
                LatticeElement::Interval { lo, hi }
            }
        }
        (LatticeElement::Sign(s1), LatticeElement::Sign(s2)) => {
            // Signs don't need widening (finite domain), use join
            let result = sign_join(s1, s2);
            if result == SignValue::AnySign {
                LatticeElement::Top
            } else {
                LatticeElement::Sign(result)
            }
        }
        (LatticeElement::Product(a1, a2), LatticeElement::Product(b1, b2)) => {
            LatticeElement::Product(Box::new(widen(a1, b1)), Box::new(widen(a2, b2)))
        }
        _ => LatticeElement::Top,
    }
}

// ---------------------------------------------------------------------------
// Narrowing
// ---------------------------------------------------------------------------

/// Narrowing operator for precision recovery after widening.
///
/// Refines an over-approximation toward a tighter fixpoint without
/// losing soundness.
#[must_use]
pub fn narrow(a: &LatticeElement, b: &LatticeElement) -> LatticeElement {
    if is_bottom(a) || is_bottom(b) {
        return LatticeElement::Bottom;
    }
    if is_top(a) {
        return b.clone();
    }
    if is_top(b) {
        return a.clone();
    }
    match (a, b) {
        (
            LatticeElement::Interval { lo: l1, hi: h1 },
            LatticeElement::Interval { lo: l2, hi: h2 },
        ) => {
            let lo = if *l1 == i64::MIN { *l2 } else { *l1 };
            let hi = if *h1 == i64::MAX { *h2 } else { *h1 };
            if lo > hi { LatticeElement::Bottom } else { LatticeElement::Interval { lo, hi } }
        }
        (LatticeElement::Sign(s1), LatticeElement::Sign(s2)) => {
            // Finite domain: narrowing = meet
            let result = sign_meet(s1, s2);
            match result {
                None => LatticeElement::Bottom,
                Some(s) => LatticeElement::Sign(s),
            }
        }
        (LatticeElement::Product(a1, a2), LatticeElement::Product(b1, b2)) => {
            let n1 = narrow(a1, b1);
            let n2 = narrow(a2, b2);
            if is_bottom(&n1) || is_bottom(&n2) {
                LatticeElement::Bottom
            } else {
                LatticeElement::Product(Box::new(n1), Box::new(n2))
            }
        }
        _ => a.clone(),
    }
}

// ---------------------------------------------------------------------------
// Sign domain operations
// ---------------------------------------------------------------------------

/// Join (least upper bound) in the sign domain.
#[must_use]
pub fn sign_join(a: &SignValue, b: &SignValue) -> SignValue {
    if a == b {
        return *a;
    }
    match (*a, *b) {
        (SignValue::AnySign, _) | (_, SignValue::AnySign) => SignValue::AnySign,
        (SignValue::Negative, SignValue::Zero) | (SignValue::Zero, SignValue::Negative) => {
            SignValue::NonPositive
        }
        (SignValue::Positive, SignValue::Zero) | (SignValue::Zero, SignValue::Positive) => {
            SignValue::NonNegative
        }
        (SignValue::Negative, SignValue::Positive) | (SignValue::Positive, SignValue::Negative) => {
            SignValue::NonZero
        }
        // NonNegative joins
        (SignValue::NonNegative, SignValue::Zero)
        | (SignValue::Zero, SignValue::NonNegative)
        | (SignValue::NonNegative, SignValue::Positive)
        | (SignValue::Positive, SignValue::NonNegative) => SignValue::NonNegative,
        // NonPositive joins
        (SignValue::NonPositive, SignValue::Zero)
        | (SignValue::Zero, SignValue::NonPositive)
        | (SignValue::NonPositive, SignValue::Negative)
        | (SignValue::Negative, SignValue::NonPositive) => SignValue::NonPositive,
        // NonZero joins
        (SignValue::NonZero, SignValue::Negative)
        | (SignValue::Negative, SignValue::NonZero)
        | (SignValue::NonZero, SignValue::Positive)
        | (SignValue::Positive, SignValue::NonZero) => SignValue::NonZero,
        // Everything else goes to AnySign
        _ => SignValue::AnySign,
    }
}

/// Meet (greatest lower bound) in the sign domain.
///
/// Returns `None` when the meet is bottom (empty intersection).
#[must_use]
pub fn sign_meet(a: &SignValue, b: &SignValue) -> Option<SignValue> {
    if a == b {
        return Some(*a);
    }
    match (*a, *b) {
        (SignValue::AnySign, x) | (x, SignValue::AnySign) => Some(x),
        // NonNegative meets
        (SignValue::NonNegative, SignValue::Positive)
        | (SignValue::Positive, SignValue::NonNegative) => Some(SignValue::Positive),
        (SignValue::NonNegative, SignValue::Zero) | (SignValue::Zero, SignValue::NonNegative) => {
            Some(SignValue::Zero)
        }
        (SignValue::NonNegative, SignValue::NonPositive)
        | (SignValue::NonPositive, SignValue::NonNegative) => Some(SignValue::Zero),
        (SignValue::NonNegative, SignValue::NonZero)
        | (SignValue::NonZero, SignValue::NonNegative) => Some(SignValue::Positive),
        // NonPositive meets
        (SignValue::NonPositive, SignValue::Negative)
        | (SignValue::Negative, SignValue::NonPositive) => Some(SignValue::Negative),
        (SignValue::NonPositive, SignValue::Zero) | (SignValue::Zero, SignValue::NonPositive) => {
            Some(SignValue::Zero)
        }
        (SignValue::NonPositive, SignValue::NonZero)
        | (SignValue::NonZero, SignValue::NonPositive) => Some(SignValue::Negative),
        // NonZero meets
        (SignValue::NonZero, SignValue::Zero) | (SignValue::Zero, SignValue::NonZero) => None,
        (SignValue::NonZero, SignValue::Positive) | (SignValue::Positive, SignValue::NonZero) => {
            Some(SignValue::Positive)
        }
        (SignValue::NonZero, SignValue::Negative) | (SignValue::Negative, SignValue::NonZero) => {
            Some(SignValue::Negative)
        }
        // Disjoint base signs
        (SignValue::Negative, SignValue::Zero)
        | (SignValue::Zero, SignValue::Negative)
        | (SignValue::Negative, SignValue::Positive)
        | (SignValue::Positive, SignValue::Negative)
        | (SignValue::Positive, SignValue::Zero)
        | (SignValue::Zero, SignValue::Positive) => None,
        _ => None,
    }
}

/// Derive a sign from an interval [lo, hi].
#[must_use]
pub fn sign_from_interval(lo: i64, hi: i64) -> SignValue {
    if lo > hi {
        // Empty interval -- caller should use Bottom instead
        return SignValue::AnySign;
    }
    if lo > 0 {
        SignValue::Positive
    } else if hi < 0 {
        SignValue::Negative
    } else if lo == 0 && hi == 0 {
        SignValue::Zero
    } else if lo >= 0 {
        SignValue::NonNegative
    } else if hi <= 0 {
        SignValue::NonPositive
    } else if lo < 0 && hi > 0 {
        // Spans negative and positive but might include zero
        SignValue::AnySign
    } else {
        SignValue::AnySign
    }
}

// ---------------------------------------------------------------------------
// Interval operations
// ---------------------------------------------------------------------------

/// Join (least upper bound) of two intervals.
#[must_use]
pub fn interval_join(a: (i64, i64), b: (i64, i64)) -> (i64, i64) {
    (a.0.min(b.0), a.1.max(b.1))
}

/// Widening of two intervals. Pushes bounds to i64::MIN/MAX when they grow.
#[must_use]
pub fn interval_widen(a: (i64, i64), b: (i64, i64)) -> (i64, i64) {
    let lo = if b.0 < a.0 { i64::MIN } else { a.0 };
    let hi = if b.1 > a.1 { i64::MAX } else { a.1 };
    (lo, hi)
}

/// Abstract addition of two intervals.
#[must_use]
pub fn interval_add(a: (i64, i64), b: (i64, i64)) -> (i64, i64) {
    (a.0.saturating_add(b.0), a.1.saturating_add(b.1))
}

/// Abstract multiplication of two intervals.
#[must_use]
pub fn interval_mul(a: (i64, i64), b: (i64, i64)) -> (i64, i64) {
    let products = [
        a.0.saturating_mul(b.0),
        a.0.saturating_mul(b.1),
        a.1.saturating_mul(b.0),
        a.1.saturating_mul(b.1),
    ];
    let lo = products.iter().copied().min().expect("invariant: non-empty array");
    let hi = products.iter().copied().max().expect("invariant: non-empty array");
    (lo, hi)
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a
}

fn lcm(a: u64, b: u64) -> u64 {
    if a == 0 || b == 0 {
        return 0;
    }
    a / gcd(a, b) * b
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // --- is_bottom / is_top ---

    #[test]
    fn test_is_bottom_top() {
        assert!(is_bottom(&LatticeElement::Bottom));
        assert!(!is_bottom(&LatticeElement::Top));
        assert!(is_top(&LatticeElement::Top));
        assert!(!is_top(&LatticeElement::Bottom));
        assert!(!is_top(&LatticeElement::Interval { lo: 0, hi: 10 }));
    }

    // --- join ---

    #[test]
    fn test_join_intervals() {
        let a = LatticeElement::Interval { lo: 1, hi: 5 };
        let b = LatticeElement::Interval { lo: 3, hi: 10 };
        assert_eq!(join(&a, &b), LatticeElement::Interval { lo: 1, hi: 10 });
    }

    #[test]
    fn test_join_with_bottom() {
        let a = LatticeElement::Interval { lo: 1, hi: 5 };
        assert_eq!(join(&a, &LatticeElement::Bottom), a);
        assert_eq!(join(&LatticeElement::Bottom, &a), a);
    }

    #[test]
    fn test_join_with_top() {
        let a = LatticeElement::Interval { lo: 1, hi: 5 };
        assert_eq!(join(&a, &LatticeElement::Top), LatticeElement::Top);
    }

    #[test]
    fn test_join_signs() {
        let a = LatticeElement::Sign(SignValue::Positive);
        let b = LatticeElement::Sign(SignValue::Zero);
        assert_eq!(join(&a, &b), LatticeElement::Sign(SignValue::NonNegative));
    }

    #[test]
    fn test_join_signs_to_top() {
        let a = LatticeElement::Sign(SignValue::NonNegative);
        let b = LatticeElement::Sign(SignValue::NonPositive);
        // NonNegative join NonPositive = AnySign -> Top
        assert_eq!(join(&a, &b), LatticeElement::Top);
    }

    // --- meet ---

    #[test]
    fn test_meet_intervals() {
        let a = LatticeElement::Interval { lo: 1, hi: 10 };
        let b = LatticeElement::Interval { lo: 5, hi: 15 };
        assert_eq!(meet(&a, &b), LatticeElement::Interval { lo: 5, hi: 10 });
    }

    #[test]
    fn test_meet_disjoint_intervals() {
        let a = LatticeElement::Interval { lo: 1, hi: 3 };
        let b = LatticeElement::Interval { lo: 5, hi: 10 };
        assert_eq!(meet(&a, &b), LatticeElement::Bottom);
    }

    #[test]
    fn test_meet_with_top() {
        let a = LatticeElement::Interval { lo: 1, hi: 5 };
        assert_eq!(meet(&a, &LatticeElement::Top), a);
    }

    #[test]
    fn test_meet_signs() {
        let a = LatticeElement::Sign(SignValue::NonNegative);
        let b = LatticeElement::Sign(SignValue::NonPositive);
        assert_eq!(meet(&a, &b), LatticeElement::Sign(SignValue::Zero));
    }

    // --- widen ---

    #[test]
    fn test_widen_intervals() {
        let a = LatticeElement::Interval { lo: 0, hi: 5 };
        let b = LatticeElement::Interval { lo: 0, hi: 10 };
        // hi grew, so widened to MAX
        assert_eq!(widen(&a, &b), LatticeElement::Interval { lo: 0, hi: i64::MAX });
    }

    #[test]
    fn test_widen_stable() {
        let a = LatticeElement::Interval { lo: 0, hi: 10 };
        let b = LatticeElement::Interval { lo: 0, hi: 10 };
        assert_eq!(widen(&a, &b), LatticeElement::Interval { lo: 0, hi: 10 });
    }

    #[test]
    fn test_widen_both_bounds_grow() {
        let a = LatticeElement::Interval { lo: 0, hi: 5 };
        let b = LatticeElement::Interval { lo: -1, hi: 10 };
        assert_eq!(widen(&a, &b), LatticeElement::Top);
    }

    // --- narrow ---

    #[test]
    fn test_narrow_intervals() {
        let a = LatticeElement::Interval { lo: 0, hi: i64::MAX };
        let b = LatticeElement::Interval { lo: 0, hi: 100 };
        assert_eq!(narrow(&a, &b), LatticeElement::Interval { lo: 0, hi: 100 });
    }

    #[test]
    fn test_narrow_from_top() {
        let b = LatticeElement::Interval { lo: 0, hi: 100 };
        assert_eq!(narrow(&LatticeElement::Top, &b), b);
    }

    // --- includes ---

    #[test]
    fn test_includes_intervals() {
        let wide = LatticeElement::Interval { lo: 0, hi: 100 };
        let narrow_iv = LatticeElement::Interval { lo: 10, hi: 50 };
        assert!(includes(&wide, &narrow_iv));
        assert!(!includes(&narrow_iv, &wide));
    }

    #[test]
    fn test_includes_bottom_top() {
        let a = LatticeElement::Interval { lo: 0, hi: 10 };
        assert!(includes(&a, &LatticeElement::Bottom));
        assert!(includes(&LatticeElement::Top, &a));
        assert!(!includes(&a, &LatticeElement::Top));
    }

    #[test]
    fn test_includes_signs() {
        let nonneg = LatticeElement::Sign(SignValue::NonNegative);
        let pos = LatticeElement::Sign(SignValue::Positive);
        assert!(includes(&nonneg, &pos));
        assert!(!includes(&pos, &nonneg));
    }

    // --- sign operations ---

    #[test]
    fn test_sign_join_basic() {
        assert_eq!(sign_join(&SignValue::Negative, &SignValue::Positive), SignValue::NonZero);
        assert_eq!(sign_join(&SignValue::Negative, &SignValue::Zero), SignValue::NonPositive);
        assert_eq!(sign_join(&SignValue::Positive, &SignValue::Zero), SignValue::NonNegative);
    }

    #[test]
    fn test_sign_meet_basic() {
        assert_eq!(
            sign_meet(&SignValue::NonNegative, &SignValue::Positive),
            Some(SignValue::Positive)
        );
        assert_eq!(sign_meet(&SignValue::Negative, &SignValue::Positive), None);
        assert_eq!(sign_meet(&SignValue::NonZero, &SignValue::Zero), None);
    }

    #[test]
    fn test_sign_from_interval_cases() {
        assert_eq!(sign_from_interval(1, 10), SignValue::Positive);
        assert_eq!(sign_from_interval(-10, -1), SignValue::Negative);
        assert_eq!(sign_from_interval(0, 0), SignValue::Zero);
        assert_eq!(sign_from_interval(0, 10), SignValue::NonNegative);
        assert_eq!(sign_from_interval(-10, 0), SignValue::NonPositive);
        assert_eq!(sign_from_interval(-10, 10), SignValue::AnySign);
    }

    // --- interval operations ---

    #[test]
    fn test_interval_join_fn() {
        assert_eq!(interval_join((1, 5), (3, 10)), (1, 10));
        assert_eq!(interval_join((0, 0), (0, 0)), (0, 0));
    }

    #[test]
    fn test_interval_widen_fn() {
        assert_eq!(interval_widen((0, 5), (0, 10)), (0, i64::MAX));
        assert_eq!(interval_widen((0, 10), (-1, 10)), (i64::MIN, 10));
    }

    #[test]
    fn test_interval_add_fn() {
        assert_eq!(interval_add((1, 5), (10, 20)), (11, 25));
        assert_eq!(interval_add((-5, 5), (-3, 3)), (-8, 8));
    }

    #[test]
    fn test_interval_mul_fn() {
        assert_eq!(interval_mul((2, 3), (4, 5)), (8, 15));
        assert_eq!(interval_mul((-2, 3), (-1, 4)), (-8, 12));
    }

    // --- product ---

    #[test]
    fn test_product_join() {
        let a = LatticeElement::Product(
            Box::new(LatticeElement::Interval { lo: 1, hi: 5 }),
            Box::new(LatticeElement::Sign(SignValue::Positive)),
        );
        let b = LatticeElement::Product(
            Box::new(LatticeElement::Interval { lo: 3, hi: 10 }),
            Box::new(LatticeElement::Sign(SignValue::Zero)),
        );
        let result = join(&a, &b);
        assert_eq!(
            result,
            LatticeElement::Product(
                Box::new(LatticeElement::Interval { lo: 1, hi: 10 }),
                Box::new(LatticeElement::Sign(SignValue::NonNegative)),
            )
        );
    }

    // --- congruence ---

    #[test]
    fn test_congruence_join() {
        // 0 mod 4 join 0 mod 6 => 0 mod gcd(4,6)=2
        let a = LatticeElement::Congruence { modulus: 4, remainder: 0 };
        let b = LatticeElement::Congruence { modulus: 6, remainder: 0 };
        assert_eq!(join(&a, &b), LatticeElement::Congruence { modulus: 2, remainder: 0 });
    }

    #[test]
    fn test_congruence_incompatible_join() {
        // 1 mod 4 join 0 mod 4 => top (remainders differ mod gcd)
        let a = LatticeElement::Congruence { modulus: 4, remainder: 1 };
        let b = LatticeElement::Congruence { modulus: 4, remainder: 0 };
        assert_eq!(join(&a, &b), LatticeElement::Top);
    }

    #[test]
    fn test_display() {
        assert_eq!(LatticeElement::Bottom.to_string(), "bot");
        assert_eq!(LatticeElement::Top.to_string(), "top");
        assert_eq!(LatticeElement::Interval { lo: 1, hi: 10 }.to_string(), "[1, 10]");
        assert_eq!(
            LatticeElement::Congruence { modulus: 4, remainder: 1 }.to_string(),
            "1 (mod 4)"
        );
    }
}
