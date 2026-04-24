// trust-types/smt_logic.rs: Canonical SMT-LIB2 logic selection, free variable
// collection, and sort inference for Formula.
//
// tRust #713: Consolidated from trust-vcgen/smtlib2.rs, trust-vcgen/simplify_equivalence.rs,
// and trust-proof-cert/smt_equivalence.rs. This is the single authoritative location
// for these formula-level SMT utilities.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeSet;

use crate::{Formula, Sort};

/// Select the appropriate SMT-LIB2 logic based on formula features.
///
/// Analyzes the formula to determine which theories are needed:
/// - `QF_LIA`: quantifier-free linear integer arithmetic (default)
/// - `QF_BV`: quantifier-free bitvectors
/// - `QF_ABV`: quantifier-free arrays + bitvectors
/// - `QF_ALIA`: quantifier-free arrays + linear integer arithmetic
/// - `ALIA`: arrays + linear integer arithmetic (with quantifiers)
/// - `LIA`: linear integer arithmetic (with quantifiers)
/// - `ALL`: when multiple complex theories are combined
#[must_use]
pub fn select_logic(formula: &Formula) -> &'static str {
    let mut has_bv = false;
    let mut has_array = false;
    let mut has_quantifier = false;
    let mut has_int = false;

    formula.visit(&mut |f| match f {
        Formula::BitVec { .. }
        | Formula::BvAdd(..)
        | Formula::BvSub(..)
        | Formula::BvMul(..)
        | Formula::BvUDiv(..)
        | Formula::BvSDiv(..)
        | Formula::BvURem(..)
        | Formula::BvSRem(..)
        | Formula::BvAnd(..)
        | Formula::BvOr(..)
        | Formula::BvXor(..)
        | Formula::BvNot(..)
        | Formula::BvShl(..)
        | Formula::BvLShr(..)
        | Formula::BvAShr(..)
        | Formula::BvULt(..)
        | Formula::BvULe(..)
        | Formula::BvSLt(..)
        | Formula::BvSLe(..)
        | Formula::BvToInt(..)
        | Formula::IntToBv(..)
        | Formula::BvExtract { .. }
        | Formula::BvConcat(..)
        | Formula::BvZeroExt(..)
        | Formula::BvSignExt(..) => has_bv = true,
        Formula::Var(_, Sort::BitVec(_)) | Formula::SymVar(_, Sort::BitVec(_)) => has_bv = true,
        Formula::Select(..) | Formula::Store(..) => has_array = true,
        Formula::Var(_, Sort::Array(..)) | Formula::SymVar(_, Sort::Array(..)) => has_array = true,
        Formula::Forall(..) | Formula::Exists(..) => has_quantifier = true,
        Formula::Int(_) | Formula::UInt(_) => has_int = true,
        Formula::Var(_, Sort::Int) | Formula::SymVar(_, Sort::Int) => has_int = true,
        Formula::Add(..)
        | Formula::Sub(..)
        | Formula::Mul(..)
        | Formula::Div(..)
        | Formula::Rem(..)
        | Formula::Neg(..) => has_int = true,
        _ => {}
    });

    match (has_quantifier, has_array, has_bv, has_int) {
        // tRust: specific multi-theory logics before catch-all
        (false, true, true, false) => "QF_ABV",
        (_, true, true, _) | (_, _, true, true) => "ALL",
        (false, true, false, true) => "QF_ALIA",
        (true, true, false, true) => "ALIA",
        (false, false, true, false) => "QF_BV",
        (true, false, false, _) => "LIA",
        _ => "QF_LIA",
    }
}

/// Collect all free variable declarations from a formula.
///
/// Returns a sorted `BTreeSet` of `(name, sort)` pairs for deterministic output.
/// Bound variables (from `Forall`/`Exists`) are excluded.
#[must_use]
pub fn collect_free_var_decls(formula: &Formula) -> BTreeSet<(String, Sort)> {
    let free = formula.free_variables();
    let mut decls = BTreeSet::new();

    formula.visit(&mut |f| {
        match f {
            Formula::Var(name, sort) if free.contains(name) => {
                decls.insert((name.clone(), sort.clone()));
            }
            // tRust #717: SymVar — resolve symbol to string for free var decl collection.
            Formula::SymVar(sym, sort) => {
                let name = sym.as_str().to_string();
                if free.contains(&name) {
                    decls.insert((name, sort.clone()));
                }
            }
            _ => {}
        }
    });

    decls
}

/// Infer the SMT-LIB2 sort for a formula expression.
///
/// Returns the sort that the top-level expression evaluates to:
/// - Boolean connectives (And, Or, Not, Implies) and comparisons -> `Sort::Bool`
/// - Integer arithmetic (Add, Sub, Mul, Div, Rem, Neg) -> `Sort::Int`
/// - Integer/UInt/Bool literals -> their natural sort
/// - Bitvector operations -> `Sort::BitVec(width)`
/// - Variables -> their declared sort
/// - Quantifiers -> `Sort::Bool`
/// - Select -> element sort (if array sort known), else `Sort::Int`
/// - Store -> array sort (if known), else `Sort::Int`
/// - Ite -> sort of the then-branch
///
/// Defaults to `Sort::Int` for ambiguous cases.
#[must_use]
pub fn infer_sort(formula: &Formula) -> Sort {
    match formula {
        // Literals
        Formula::Bool(_) => Sort::Bool,
        Formula::Int(_) | Formula::UInt(_) => Sort::Int,
        Formula::BitVec { width, .. } => Sort::BitVec(*width),

        // Variables carry their own sort
        Formula::Var(_, sort) | Formula::SymVar(_, sort) => sort.clone(),

        // Boolean connectives and comparisons
        Formula::Not(_)
        | Formula::And(_)
        | Formula::Or(_)
        | Formula::Implies(_, _)
        | Formula::Eq(_, _)
        | Formula::Lt(_, _)
        | Formula::Le(_, _)
        | Formula::Gt(_, _)
        | Formula::Ge(_, _)
        | Formula::BvULt(_, _, _)
        | Formula::BvULe(_, _, _)
        | Formula::BvSLt(_, _, _)
        | Formula::BvSLe(_, _, _) => Sort::Bool,

        // Integer arithmetic
        Formula::Add(_, _)
        | Formula::Sub(_, _)
        | Formula::Mul(_, _)
        | Formula::Div(_, _)
        | Formula::Rem(_, _)
        | Formula::Neg(_) => Sort::Int,

        // Bitvector arithmetic -- width from the operation
        Formula::BvAdd(_, _, w)
        | Formula::BvSub(_, _, w)
        | Formula::BvMul(_, _, w)
        | Formula::BvUDiv(_, _, w)
        | Formula::BvSDiv(_, _, w)
        | Formula::BvURem(_, _, w)
        | Formula::BvSRem(_, _, w)
        | Formula::BvAnd(_, _, w)
        | Formula::BvOr(_, _, w)
        | Formula::BvXor(_, _, w)
        | Formula::BvNot(_, w)
        | Formula::BvShl(_, _, w)
        | Formula::BvLShr(_, _, w)
        | Formula::BvAShr(_, _, w) => Sort::BitVec(*w),

        // Bitvector conversions
        Formula::BvToInt(_, _, _) => Sort::Int,
        Formula::IntToBv(_, w) => Sort::BitVec(*w),
        Formula::BvExtract { high, low, .. } => Sort::BitVec(high - low + 1),
        Formula::BvConcat(a, b) => {
            let wa = match infer_sort(a) {
                Sort::BitVec(w) => w,
                _ => 0,
            };
            let wb = match infer_sort(b) {
                Sort::BitVec(w) => w,
                _ => 0,
            };
            Sort::BitVec(wa + wb)
        }
        Formula::BvZeroExt(inner, extra) => {
            let base = match infer_sort(inner) {
                Sort::BitVec(w) => w,
                _ => 0,
            };
            Sort::BitVec(base + extra)
        }
        Formula::BvSignExt(inner, extra) => {
            let base = match infer_sort(inner) {
                Sort::BitVec(w) => w,
                _ => 0,
            };
            Sort::BitVec(base + extra)
        }

        // Conditional -- sort of the then-branch
        Formula::Ite(_, then_br, _) => infer_sort(then_br),

        // Quantifiers always produce Bool
        Formula::Forall(_, _) | Formula::Exists(_, _) => Sort::Bool,

        // Array operations
        Formula::Select(arr, _) => {
            if let Sort::Array(_, elem) = infer_sort(arr) {
                *elem
            } else {
                Sort::Int
            }
        }
        Formula::Store(arr, _, _) => infer_sort(arr),

        // Conservative fallback for future #[non_exhaustive] variants.
        #[allow(unreachable_patterns)]
        _ => Sort::Int,
    }
}

/// Split an s-expression body into its top-level tokens/sub-expressions.
///
/// tRust #713: Canonical s-expression splitter shared by `SmtPrinter` and
/// `SmtLib2Printer`. Handles nested parentheses, whitespace tokenization,
/// and trailing tokens.
///
/// # Example
/// ```ignore
/// split_top_level("and (> x 0) (< y 10)")
/// // => ["and", "(> x 0)", "(< y 10)"]
/// ```
#[must_use]
pub fn split_top_level(input: &str) -> Vec<&str> {
    let mut parts = Vec::new();
    let mut depth = 0usize;
    let mut start: Option<usize> = None;
    for (i, ch) in input.char_indices() {
        match ch {
            ' ' | '\t' | '\n' if depth == 0 => {
                if let Some(s) = start {
                    let token = &input[s..i];
                    if !token.trim().is_empty() {
                        parts.push(token);
                    }
                    start = None;
                }
            }
            '(' => {
                if start.is_none() {
                    start = Some(i);
                }
                depth += 1;
            }
            ')' => {
                depth = depth.saturating_sub(1);
                if depth == 0
                    && let Some(s) = start
                {
                    parts.push(&input[s..=i]);
                    start = None;
                }
            }
            _ => {
                if start.is_none() {
                    start = Some(i);
                }
            }
        }
    }
    // Trailing token.
    if let Some(s) = start {
        let token = &input[s..];
        if !token.trim().is_empty() {
            parts.push(token);
        }
    }
    parts
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Formula, Sort};

    fn var(name: &str) -> Formula {
        Formula::Var(name.into(), Sort::Int)
    }

    fn bv_var(name: &str, w: u32) -> Formula {
        Formula::Var(name.into(), Sort::BitVec(w))
    }

    // --- select_logic ---

    #[test]
    fn test_select_logic_pure_int() {
        let f = Formula::Add(Box::new(var("x")), Box::new(Formula::Int(1)));
        assert_eq!(select_logic(&f), "QF_LIA");
    }

    #[test]
    fn test_select_logic_pure_bv() {
        let f = Formula::BvAdd(Box::new(bv_var("x", 32)), Box::new(bv_var("y", 32)), 32);
        assert_eq!(select_logic(&f), "QF_BV");
    }

    #[test]
    fn test_select_logic_quantified() {
        let f = Formula::Forall(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::Ge(Box::new(var("x")), Box::new(Formula::Int(0)))),
        );
        assert_eq!(select_logic(&f), "LIA");
    }

    #[test]
    fn test_select_logic_array_int() {
        let f = Formula::Select(
            Box::new(Formula::Var(
                "arr".into(),
                Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int)),
            )),
            Box::new(var("i")),
        );
        assert_eq!(select_logic(&f), "QF_ALIA");
    }

    #[test]
    fn test_select_logic_array_bv() {
        let f = Formula::Select(
            Box::new(Formula::Var(
                "mem".into(),
                Sort::Array(Box::new(Sort::BitVec(32)), Box::new(Sort::BitVec(8))),
            )),
            Box::new(bv_var("addr", 32)),
        );
        assert_eq!(select_logic(&f), "QF_ABV");
    }

    #[test]
    fn test_select_logic_array_bv_int_is_all() {
        let f = Formula::And(vec![
            Formula::Select(
                Box::new(Formula::Var(
                    "mem".into(),
                    Sort::Array(Box::new(Sort::BitVec(32)), Box::new(Sort::BitVec(8))),
                )),
                Box::new(bv_var("addr", 32)),
            ),
            Formula::Gt(Box::new(var("len")), Box::new(Formula::Int(0))),
        ]);
        assert_eq!(select_logic(&f), "ALL");
    }

    // --- collect_free_var_decls ---

    #[test]
    fn test_collect_free_var_decls_simple() {
        let f = Formula::Add(Box::new(var("x")), Box::new(var("y")));
        let decls: Vec<_> = collect_free_var_decls(&f).into_iter().collect();
        assert_eq!(decls.len(), 2);
        assert_eq!(decls[0].0, "x");
        assert_eq!(decls[1].0, "y");
    }

    #[test]
    fn test_collect_free_var_decls_excludes_bound() {
        let f = Formula::Forall(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::Add(Box::new(var("x")), Box::new(var("y")))),
        );
        let decls: Vec<_> = collect_free_var_decls(&f).into_iter().collect();
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].0, "y");
    }

    #[test]
    fn test_collect_free_var_decls_mixed_sorts() {
        let f = Formula::And(vec![
            Formula::Var("flag".into(), Sort::Bool),
            var("count"),
            bv_var("bits", 32),
        ]);
        let decls: Vec<_> = collect_free_var_decls(&f).into_iter().collect();
        assert_eq!(decls.len(), 3);
        assert_eq!(decls[0].0, "bits");
        assert_eq!(decls[1].0, "count");
        assert_eq!(decls[2].0, "flag");
    }

    // --- infer_sort ---

    #[test]
    fn test_infer_sort_literals() {
        assert_eq!(infer_sort(&Formula::Bool(true)), Sort::Bool);
        assert_eq!(infer_sort(&Formula::Int(42)), Sort::Int);
        assert_eq!(infer_sort(&Formula::UInt(100)), Sort::Int);
        assert_eq!(infer_sort(&Formula::BitVec { value: 255, width: 8 }), Sort::BitVec(8));
    }

    #[test]
    fn test_infer_sort_boolean_ops() {
        assert_eq!(infer_sort(&Formula::Not(Box::new(Formula::Bool(true)))), Sort::Bool);
        assert_eq!(infer_sort(&Formula::And(vec![var("a"), var("b")])), Sort::Bool);
        assert_eq!(infer_sort(&Formula::Eq(Box::new(var("x")), Box::new(var("y")))), Sort::Bool);
    }

    #[test]
    fn test_infer_sort_arithmetic() {
        assert_eq!(infer_sort(&Formula::Add(Box::new(var("x")), Box::new(var("y")))), Sort::Int);
    }

    #[test]
    fn test_infer_sort_bv_ops() {
        assert_eq!(
            infer_sort(&Formula::BvAdd(Box::new(bv_var("a", 32)), Box::new(bv_var("b", 32)), 32)),
            Sort::BitVec(32)
        );
    }

    #[test]
    fn test_infer_sort_ite_follows_then_branch() {
        let ite = Formula::Ite(
            Box::new(Formula::Bool(true)),
            Box::new(bv_var("x", 64)),
            Box::new(bv_var("y", 64)),
        );
        assert_eq!(infer_sort(&ite), Sort::BitVec(64));
    }

    #[test]
    fn test_infer_sort_quantifiers_are_bool() {
        let f = Formula::Forall(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::Ge(Box::new(var("x")), Box::new(Formula::Int(0)))),
        );
        assert_eq!(infer_sort(&f), Sort::Bool);
    }

    #[test]
    fn test_infer_sort_array_select() {
        let arr = Formula::Var(
            "arr".into(),
            Sort::Array(Box::new(Sort::Int), Box::new(Sort::BitVec(32))),
        );
        let sel = Formula::Select(Box::new(arr), Box::new(Formula::Int(0)));
        assert_eq!(infer_sort(&sel), Sort::BitVec(32));
    }

    // --- split_top_level ---

    #[test]
    fn test_split_top_level_simple_tokens() {
        assert_eq!(split_top_level("and a b c"), vec!["and", "a", "b", "c"]);
    }

    #[test]
    fn test_split_top_level_nested_parens() {
        assert_eq!(split_top_level("and (> x 0) (< y 10)"), vec!["and", "(> x 0)", "(< y 10)"]);
    }

    #[test]
    fn test_split_top_level_empty() {
        assert!(split_top_level("").is_empty());
    }

    #[test]
    fn test_split_top_level_single_atom() {
        assert_eq!(split_top_level("x"), vec!["x"]);
    }

    #[test]
    fn test_split_top_level_deeply_nested() {
        assert_eq!(split_top_level("+ (f (g x)) y"), vec!["+", "(f (g x))", "y"]);
    }
}
