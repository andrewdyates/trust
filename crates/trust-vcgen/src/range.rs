// trust-vcgen/range.rs: Shared integer range utilities
//
// Consolidates type_max_formula, type_min_formula, input_range_constraint,
// signed_min, signed_max, and unsigned_max that were previously duplicated
// across overflow.rs, shifts.rs, and casts.rs.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::*;

/// Return a formula representing the maximum value for an integer type.
/// For unsigned 128-bit, this returns Formula::UInt(u128::MAX) since u128::MAX
/// exceeds i128::MAX and cannot be represented as Formula::Int.
#[must_use]
pub(crate) fn type_max_formula(width: u32, signed: bool) -> Formula {
    if signed {
        Formula::Int(signed_max(width))
    } else if width == 128 {
        Formula::UInt(u128::MAX)
    } else {
        Formula::Int((1i128 << width) - 1)
    }
}

/// Return a formula representing the minimum value for an integer type.
#[must_use]
pub(crate) fn type_min_formula(width: u32, signed: bool) -> Formula {
    if signed { Formula::Int(signed_min(width)) } else { Formula::Int(0) }
}

/// Minimum value for a signed integer of the given bit width.
#[must_use]
pub(crate) fn signed_min(width: u32) -> i128 {
    if width == 128 { i128::MIN } else { -(1i128 << (width - 1)) }
}

/// Maximum value for a signed integer of the given bit width.
#[must_use]
pub(crate) fn signed_max(width: u32) -> i128 {
    if width == 128 { i128::MAX } else { (1i128 << (width - 1)) - 1 }
}

/// Maximum value for an unsigned integer of the given bit width.
#[must_use]
pub(crate) fn unsigned_max(width: u32) -> u128 {
    if width == 128 { u128::MAX } else { (1u128 << width) - 1 }
}

/// Constrain a variable to the valid range of its integer type.
#[must_use]
pub(crate) fn input_range_constraint(var: &Formula, width: u32, signed: bool) -> Formula {
    let min_f = type_min_formula(width, signed);
    let max_f = type_max_formula(width, signed);

    Formula::And(vec![
        Formula::Le(Box::new(min_f), Box::new(var.clone())),
        Formula::Le(Box::new(var.clone()), Box::new(max_f)),
    ])
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_type_max_formula_u8() {
        assert_eq!(type_max_formula(8, false), Formula::Int(255));
    }

    #[test]
    fn test_type_max_formula_i8() {
        assert_eq!(type_max_formula(8, true), Formula::Int(127));
    }

    #[test]
    fn test_type_max_formula_u128() {
        assert_eq!(type_max_formula(128, false), Formula::UInt(u128::MAX));
    }

    #[test]
    fn test_type_max_formula_i128() {
        assert_eq!(type_max_formula(128, true), Formula::Int(i128::MAX));
    }

    #[test]
    fn test_type_min_formula_u32() {
        assert_eq!(type_min_formula(32, false), Formula::Int(0));
    }

    #[test]
    fn test_type_min_formula_i32() {
        assert_eq!(type_min_formula(32, true), Formula::Int(-(1i128 << 31)));
    }

    #[test]
    fn test_type_min_formula_i128() {
        assert_eq!(type_min_formula(128, true), Formula::Int(i128::MIN));
    }

    #[test]
    fn test_signed_min_max_i8() {
        assert_eq!(signed_min(8), -128);
        assert_eq!(signed_max(8), 127);
    }

    #[test]
    fn test_signed_min_max_i128() {
        assert_eq!(signed_min(128), i128::MIN);
        assert_eq!(signed_max(128), i128::MAX);
    }

    #[test]
    fn test_unsigned_max_u8() {
        assert_eq!(unsigned_max(8), 255);
    }

    #[test]
    fn test_unsigned_max_u128() {
        assert_eq!(unsigned_max(128), u128::MAX);
    }

    #[test]
    fn test_input_range_constraint_u32() {
        let var = Formula::Var("x".into(), Sort::Int);
        let constraint = input_range_constraint(&var, 32, false);

        match constraint {
            Formula::And(clauses) => {
                assert_eq!(clauses.len(), 2);
                // Check lower bound: 0 <= x
                assert!(matches!(
                    &clauses[0],
                    Formula::Le(min, v) if matches!(min.as_ref(), Formula::Int(0))
                        && matches!(v.as_ref(), Formula::Var(n, _) if n == "x")
                ));
                // Check upper bound: x <= (2^32 - 1)
                assert!(matches!(
                    &clauses[1],
                    Formula::Le(v, max) if matches!(v.as_ref(), Formula::Var(n, _) if n == "x")
                        && matches!(max.as_ref(), Formula::Int(n) if *n == (1i128 << 32) - 1)
                ));
            }
            other => panic!("expected And, got {other:?}"),
        }
    }

    #[test]
    fn test_input_range_constraint_i16() {
        let var = Formula::Var("y".into(), Sort::Int);
        let constraint = input_range_constraint(&var, 16, true);

        match constraint {
            Formula::And(clauses) => {
                assert_eq!(clauses.len(), 2);
                assert!(matches!(
                    &clauses[0],
                    Formula::Le(min, _) if matches!(min.as_ref(), Formula::Int(n) if *n == -32768)
                ));
                assert!(matches!(
                    &clauses[1],
                    Formula::Le(_, max) if matches!(max.as_ref(), Formula::Int(n) if *n == 32767)
                ));
            }
            other => panic!("expected And, got {other:?}"),
        }
    }

    #[test]
    fn test_u128_input_range_constraint_uses_uint_upper_bound() {
        let var = Formula::Var("x".into(), Sort::Int);
        let constraint = input_range_constraint(&var, 128, false);

        match constraint {
            Formula::And(clauses) => {
                assert!(clauses.iter().any(|clause| matches!(
                    clause,
                    Formula::Le(_, rhs) if matches!(rhs.as_ref(), Formula::UInt(n) if *n == u128::MAX)
                )));
            }
            other => panic!("expected And, got {other:?}"),
        }
    }
}
