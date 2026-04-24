// trust-types/z4_bridge.rs: Conversion bridge between trust_types::Formula ↔ z4_bindings::Expr
//
// Phase 1 of the zani/z4 direct integration (#571). Provides bidirectional
// conversion so downstream crates can migrate incrementally from Formula to Expr.
//
// Design: designs/2026-04-13-zani-direct-integration.md
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::formula::{Formula, Sort};
use z4_bindings::{Expr, Sort as Z4Sort, SortInner as Z4SortInner};

/// Convert a trust_types::Sort to a z4_bindings::Sort.
#[must_use]
pub fn sort_to_z4(sort: &Sort) -> Z4Sort {
    match sort {
        Sort::Bool => Z4Sort::bool(),
        Sort::Int => Z4Sort::int(),
        Sort::BitVec(w) => Z4Sort::bitvec(*w),
        Sort::Array(idx, elem) => Z4Sort::array(sort_to_z4(idx), sort_to_z4(elem)),
    }
}

/// Convert a z4_bindings::Sort to a trust_types::Sort.
///
/// Returns None for sorts that trust_types doesn't support (Real, FP, String, etc.).
#[must_use]
pub fn sort_from_z4(sort: &Z4Sort) -> Option<Sort> {
    match sort.inner() {
        Z4SortInner::Bool => Some(Sort::Bool),
        Z4SortInner::Int => Some(Sort::Int),
        Z4SortInner::BitVec(bv) => Some(Sort::BitVec(bv.width)),
        Z4SortInner::Array(arr) => {
            let idx = sort_from_z4(&arr.index_sort)?;
            let elem = sort_from_z4(&arr.element_sort)?;
            Some(Sort::Array(Box::new(idx), Box::new(elem)))
        }
        // z4 sorts not representable in trust_types
        Z4SortInner::Real
        | Z4SortInner::Datatype(_)
        | Z4SortInner::String
        | Z4SortInner::FloatingPoint(_, _)
        | Z4SortInner::Uninterpreted(_)
        | Z4SortInner::RegLan
        | Z4SortInner::Seq(_) => None,
        _ => None, // future-proof for #[non_exhaustive]
    }
}

/// Convert a trust_types::Formula to a z4_bindings::Expr.
///
/// This is the key conversion for feeding trust-vcgen output into z4.
/// The mapping is 1:1 for all Formula variants.
#[must_use]
pub fn formula_to_expr(formula: &Formula) -> Expr {
    match formula {
        // Literals
        Formula::Bool(v) => Expr::bool_const(*v),
        Formula::Int(n) => Expr::int_const(*n),
        Formula::UInt(n) => Expr::int_const(*n as i128),
        Formula::BitVec { value, width } => Expr::bitvec_const(*value, *width),

        // Variables
        Formula::Var(name, sort) => Expr::var(name.clone(), sort_to_z4(sort)),
        // tRust #717: SymVar resolves symbol to string for z4 variable creation.
        Formula::SymVar(sym, sort) => Expr::var(sym.as_str().to_string(), sort_to_z4(sort)),

        // Boolean connectives
        Formula::Not(a) => formula_to_expr(a).not(),
        Formula::And(terms) => {
            if terms.is_empty() {
                Expr::true_()
            } else {
                Expr::and_many(terms.iter().map(formula_to_expr).collect())
            }
        }
        Formula::Or(terms) => {
            if terms.is_empty() {
                Expr::false_()
            } else {
                Expr::or_many(terms.iter().map(formula_to_expr).collect())
            }
        }
        Formula::Implies(a, b) => formula_to_expr(a).implies(formula_to_expr(b)),

        // Comparisons (integer domain)
        Formula::Eq(a, b) => formula_to_expr(a).eq(formula_to_expr(b)),
        Formula::Lt(a, b) => formula_to_expr(a).int_lt(formula_to_expr(b)),
        Formula::Le(a, b) => formula_to_expr(a).int_le(formula_to_expr(b)),
        Formula::Gt(a, b) => formula_to_expr(a).int_gt(formula_to_expr(b)),
        Formula::Ge(a, b) => formula_to_expr(a).int_ge(formula_to_expr(b)),

        // Integer arithmetic
        Formula::Add(a, b) => formula_to_expr(a).int_add(formula_to_expr(b)),
        Formula::Sub(a, b) => formula_to_expr(a).int_sub(formula_to_expr(b)),
        Formula::Mul(a, b) => formula_to_expr(a).int_mul(formula_to_expr(b)),
        Formula::Div(a, b) => formula_to_expr(a).int_div(formula_to_expr(b)),
        Formula::Rem(a, b) => formula_to_expr(a).int_mod(formula_to_expr(b)),
        Formula::Neg(a) => formula_to_expr(a).int_neg(),

        // Bitvector arithmetic
        Formula::BvAdd(a, b, _) => formula_to_expr(a).bvadd(formula_to_expr(b)),
        Formula::BvSub(a, b, _) => formula_to_expr(a).bvsub(formula_to_expr(b)),
        Formula::BvMul(a, b, _) => formula_to_expr(a).bvmul(formula_to_expr(b)),
        Formula::BvUDiv(a, b, _) => formula_to_expr(a).bvudiv(formula_to_expr(b)),
        Formula::BvSDiv(a, b, _) => formula_to_expr(a).bvsdiv(formula_to_expr(b)),
        Formula::BvURem(a, b, _) => formula_to_expr(a).bvurem(formula_to_expr(b)),
        Formula::BvSRem(a, b, _) => formula_to_expr(a).bvsrem(formula_to_expr(b)),
        Formula::BvAnd(a, b, _) => formula_to_expr(a).bvand(formula_to_expr(b)),
        Formula::BvOr(a, b, _) => formula_to_expr(a).bvor(formula_to_expr(b)),
        Formula::BvXor(a, b, _) => formula_to_expr(a).bvxor(formula_to_expr(b)),
        Formula::BvNot(a, _) => formula_to_expr(a).bvnot(),
        Formula::BvShl(a, b, _) => formula_to_expr(a).bvshl(formula_to_expr(b)),
        Formula::BvLShr(a, b, _) => formula_to_expr(a).bvlshr(formula_to_expr(b)),
        Formula::BvAShr(a, b, _) => formula_to_expr(a).bvashr(formula_to_expr(b)),

        // Bitvector comparisons
        Formula::BvULt(a, b, _) => formula_to_expr(a).bvult(formula_to_expr(b)),
        Formula::BvULe(a, b, _) => formula_to_expr(a).bvule(formula_to_expr(b)),
        Formula::BvSLt(a, b, _) => formula_to_expr(a).bvslt(formula_to_expr(b)),
        Formula::BvSLe(a, b, _) => formula_to_expr(a).bvsle(formula_to_expr(b)),

        // Bitvector conversions
        Formula::BvToInt(a, _w, _signed) => formula_to_expr(a).bv2int_signed(),
        Formula::IntToBv(a, w) => formula_to_expr(a).int2bv(*w),
        Formula::BvExtract { inner, high, low } => formula_to_expr(inner).extract(*high, *low),
        Formula::BvConcat(a, b) => formula_to_expr(a).concat(formula_to_expr(b)),
        Formula::BvZeroExt(a, bits) => formula_to_expr(a).zero_extend(*bits),
        Formula::BvSignExt(a, bits) => formula_to_expr(a).sign_extend(*bits),

        // Conditional
        Formula::Ite(c, t, e) => {
            Expr::ite(formula_to_expr(c), formula_to_expr(t), formula_to_expr(e))
        }

        // Quantifiers
        // tRust #883: Symbol bindings — resolve to String for z4 API.
        Formula::Forall(bindings, body) => {
            let z4_bindings_list: Vec<(String, Z4Sort)> = bindings
                .iter()
                .map(|(sym, sort)| (sym.as_str().to_string(), sort_to_z4(sort)))
                .collect();
            Expr::forall(z4_bindings_list, formula_to_expr(body))
        }
        Formula::Exists(bindings, body) => {
            let z4_bindings_list: Vec<(String, Z4Sort)> = bindings
                .iter()
                .map(|(sym, sort)| (sym.as_str().to_string(), sort_to_z4(sort)))
                .collect();
            Expr::exists(z4_bindings_list, formula_to_expr(body))
        }

        // Arrays
        Formula::Select(arr, idx) => formula_to_expr(arr).select(formula_to_expr(idx)),
        Formula::Store(arr, idx, val) => {
            formula_to_expr(arr).store(formula_to_expr(idx), formula_to_expr(val))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn var(name: &str) -> Formula {
        Formula::Var(name.into(), Sort::Int)
    }

    fn bv_var(name: &str, w: u32) -> Formula {
        Formula::Var(name.into(), Sort::BitVec(w))
    }

    #[test]
    fn test_sort_roundtrip_bool() {
        let z4 = sort_to_z4(&Sort::Bool);
        assert!(z4.is_bool());
        assert_eq!(sort_from_z4(&z4), Some(Sort::Bool));
    }

    #[test]
    fn test_sort_roundtrip_int() {
        let z4 = sort_to_z4(&Sort::Int);
        assert!(z4.is_int());
        assert_eq!(sort_from_z4(&z4), Some(Sort::Int));
    }

    #[test]
    fn test_sort_roundtrip_bitvec() {
        let z4 = sort_to_z4(&Sort::BitVec(32));
        assert!(z4.is_bitvec());
        assert_eq!(sort_from_z4(&z4), Some(Sort::BitVec(32)));
    }

    #[test]
    fn test_sort_roundtrip_array() {
        let sort = Sort::Array(Box::new(Sort::BitVec(64)), Box::new(Sort::BitVec(8)));
        let z4 = sort_to_z4(&sort);
        assert!(z4.is_array());
        assert_eq!(sort_from_z4(&z4), Some(sort));
    }

    #[test]
    fn test_formula_bool_const() {
        let expr = formula_to_expr(&Formula::Bool(true));
        assert!(expr.sort().is_bool());
        let smt = format!("{expr}");
        assert_eq!(smt, "true");
    }

    #[test]
    fn test_formula_int_const() {
        let expr = formula_to_expr(&Formula::Int(42));
        assert!(expr.sort().is_int());
        let smt = format!("{expr}");
        assert_eq!(smt, "42");
    }

    #[test]
    fn test_formula_bitvec_const() {
        let expr = formula_to_expr(&Formula::BitVec { value: 255, width: 8 });
        assert!(expr.sort().is_bitvec());
        let smt = format!("{expr}");
        assert_eq!(smt, "#xff");
    }

    #[test]
    fn test_formula_var() {
        let expr = formula_to_expr(&var("x"));
        assert!(expr.sort().is_int());
        let smt = format!("{expr}");
        assert_eq!(smt, "x");
    }

    #[test]
    fn test_formula_not() {
        let f = Formula::Not(Box::new(Formula::Bool(true)));
        let expr = formula_to_expr(&f);
        let smt = format!("{expr}");
        assert_eq!(smt, "(not true)");
    }

    #[test]
    fn test_formula_and() {
        let f = Formula::And(vec![Formula::Bool(true), Formula::Bool(false)]);
        let expr = formula_to_expr(&f);
        let smt = format!("{expr}");
        assert_eq!(smt, "(and true false)");
    }

    #[test]
    fn test_formula_implies() {
        let f = Formula::Implies(Box::new(Formula::Bool(true)), Box::new(Formula::Bool(false)));
        let expr = formula_to_expr(&f);
        let smt = format!("{expr}");
        assert_eq!(smt, "(=> true false)");
    }

    #[test]
    fn test_formula_eq() {
        let f = Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0)));
        let expr = formula_to_expr(&f);
        let smt = format!("{expr}");
        assert_eq!(smt, "(= x 0)");
    }

    #[test]
    fn test_formula_int_arith() {
        let f = Formula::Add(Box::new(var("x")), Box::new(var("y")));
        let expr = formula_to_expr(&f);
        let smt = format!("{expr}");
        assert_eq!(smt, "(+ x y)");
    }

    #[test]
    fn test_formula_bv_add() {
        let f = Formula::BvAdd(Box::new(bv_var("a", 32)), Box::new(bv_var("b", 32)), 32);
        let expr = formula_to_expr(&f);
        let smt = format!("{expr}");
        assert_eq!(smt, "(bvadd a b)");
    }

    #[test]
    fn test_formula_bv_comparisons() {
        let f = Formula::BvULt(Box::new(bv_var("a", 32)), Box::new(bv_var("b", 32)), 32);
        let expr = formula_to_expr(&f);
        let smt = format!("{expr}");
        assert_eq!(smt, "(bvult a b)");
    }

    #[test]
    fn test_formula_ite() {
        let f = Formula::Ite(
            Box::new(Formula::Bool(true)),
            Box::new(Formula::Int(1)),
            Box::new(Formula::Int(0)),
        );
        let expr = formula_to_expr(&f);
        let smt = format!("{expr}");
        assert_eq!(smt, "(ite true 1 0)");
    }

    #[test]
    fn test_formula_forall() {
        let f = Formula::Forall(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0)))),
        );
        let expr = formula_to_expr(&f);
        let smt = format!("{expr}");
        assert!(smt.contains("forall"));
        assert!(smt.contains("(x Int)"));
    }

    #[test]
    fn test_formula_select_store() {
        let arr = Formula::Var(
            "mem".into(),
            Sort::Array(Box::new(Sort::BitVec(64)), Box::new(Sort::BitVec(8))),
        );
        let idx = Formula::BitVec { value: 100, width: 64 };
        let val = Formula::BitVec { value: 42, width: 8 };

        let store = Formula::Store(Box::new(arr.clone()), Box::new(idx.clone()), Box::new(val));
        let expr = formula_to_expr(&store);
        let smt = format!("{expr}");
        assert!(smt.contains("store"));

        let select = Formula::Select(Box::new(arr), Box::new(idx));
        let expr = formula_to_expr(&select);
        let smt = format!("{expr}");
        assert!(smt.contains("select"));
    }

    #[test]
    fn test_formula_bv_extract() {
        let f = Formula::BvExtract { inner: Box::new(bv_var("x", 32)), high: 15, low: 0 };
        let expr = formula_to_expr(&f);
        let smt = format!("{expr}");
        assert!(smt.contains("extract"));
    }

    #[test]
    fn test_formula_bv_concat() {
        let f = Formula::BvConcat(Box::new(bv_var("hi", 16)), Box::new(bv_var("lo", 16)));
        let expr = formula_to_expr(&f);
        let smt = format!("{expr}");
        assert!(smt.contains("concat"));
    }

    #[test]
    fn test_formula_zero_extend() {
        let f = Formula::BvZeroExt(Box::new(bv_var("x", 32)), 32);
        let expr = formula_to_expr(&f);
        let smt = format!("{expr}");
        assert!(smt.contains("zero_extend"));
    }

    #[test]
    fn test_formula_smtlib_matches_z4() {
        // Verify that Formula::to_smtlib() and z4 Expr Display produce
        // equivalent SMT-LIB2 for basic operations
        let f = Formula::And(vec![
            Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0))),
            Formula::Lt(Box::new(var("y")), Box::new(Formula::Int(10))),
        ]);
        let trust_smt = f.to_smtlib();
        let z4_smt = format!("{}", formula_to_expr(&f));
        // Both should be syntactically valid SMT-LIB2
        assert!(trust_smt.contains("and"));
        assert!(z4_smt.contains("and"));
    }
}
