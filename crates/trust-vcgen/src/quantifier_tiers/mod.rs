// trust-vcgen/quantifier_tiers/mod.rs: Tiered quantifier elimination (#145)
//
// Split into sub-modules for readability (#455):
//   types.rs         — Configuration, enums, errors, stats
//   eliminator.rs    — QuantifierEliminator, convenience API
//   finite_domain.rs — Tier 1: finite domain detection, unrolling, substitute
//   presburger.rs    — Tier 2: Presburger detection, Cooper's method, ArithmeticFragment
//   analysis.rs      — Pre-processing: QuantifierStats, skolemize, instantiate, simplify
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

mod analysis;
mod eliminator;
pub(crate) mod finite_domain;
mod presburger;
mod types;

// Re-export all public items for backward compatibility.

// --- types.rs ---
pub use types::{
    EliminationStats, QuantifierConfig, QuantifierError, QuantifierStats, QuantifierTier,
    SolverStrategy, TierClassification,
};

// --- eliminator.rs ---
pub use eliminator::{
    QuantifierEliminator, apply_tier_strategy, has_quantifiers, is_decidable_arithmetic,
};

// --- finite_domain.rs ---
pub(crate) use finite_domain::substitute;

// --- presburger.rs ---
pub use presburger::{ArithmeticFragment, classify_fragment};

// --- analysis.rs ---
pub use analysis::{
    analyze_quantifiers, classify_quantifiers, instantiate_universal, simplify_quantified,
    skolemize,
};

// Internal re-exports for tests — these were module-private in the original
// single-file layout and are used by the test module below.
#[cfg(test)]
use presburger::{cooper_eliminate_exists, cooper_eliminate_forall, free_vars, is_presburger};
#[cfg(test)]
use eliminator::worse_strategy;

#[cfg(test)]
mod tests {
    use trust_types::{Formula, Sort};

    use super::*;

    /// Helper: make a forall formula in the style the spec parser produces.
    /// `forall(i, lo..hi, body)` => `Forall([(i, Int)], Implies(And([Le(lo,i), Lt(i,hi)]), body))`
    fn make_bounded_forall(var: &str, lo: i128, hi: i128, body: Formula) -> Formula {
        let var_f = Formula::Var(var.to_string(), Sort::Int);
        let guard = Formula::And(vec![
            Formula::Le(Box::new(Formula::Int(lo)), Box::new(var_f.clone())),
            Formula::Lt(Box::new(var_f), Box::new(Formula::Int(hi))),
        ]);
        Formula::Forall(
            vec![(var.to_string(), Sort::Int)],
            Box::new(Formula::Implies(Box::new(guard), Box::new(body))),
        )
    }

    /// Helper: make a bounded exists.
    fn make_bounded_exists(var: &str, lo: i128, hi: i128, body: Formula) -> Formula {
        let var_f = Formula::Var(var.to_string(), Sort::Int);
        let range_guard = Formula::And(vec![
            Formula::Le(Box::new(Formula::Int(lo)), Box::new(var_f.clone())),
            Formula::Lt(Box::new(var_f), Box::new(Formula::Int(hi))),
        ]);
        Formula::Exists(
            vec![(var.to_string(), Sort::Int)],
            Box::new(Formula::And(vec![range_guard, body])),
        )
    }

    // === Tier classification tests ===

    #[test]
    fn test_classify_bounded_forall_tier1() {
        let body_inner = Formula::Ge(
            Box::new(Formula::Var("i".to_string(), Sort::Int)),
            Box::new(Formula::Int(0)),
        );
        let f = make_bounded_forall("i", 0, 10, body_inner);
        let elim = QuantifierEliminator::new();
        if let Formula::Forall(bindings, body) = &f {
            let class = elim.classify(bindings, body);
            assert_eq!(class.tier, QuantifierTier::FiniteUnrolling);
            assert_eq!(class.domain.as_ref().map(|d| d.len()), Some(10));
        } else {
            panic!("expected Forall");
        }
    }

    #[test]
    fn test_classify_large_domain_falls_to_tier2() {
        let body_inner = Formula::Ge(
            Box::new(Formula::Var("i".to_string(), Sort::Int)),
            Box::new(Formula::Int(0)),
        );
        // Range 0..1000 exceeds default max_unroll=64
        let f = make_bounded_forall("i", 0, 1000, body_inner);
        let elim = QuantifierEliminator::new();
        if let Formula::Forall(bindings, body) = &f {
            let class = elim.classify(bindings, body);
            assert_eq!(class.tier, QuantifierTier::DecidableArithmetic);
        } else {
            panic!("expected Forall");
        }
    }

    #[test]
    fn test_classify_non_linear_is_full() {
        // forall x. x * x > 0  (non-linear — not Presburger)
        let var_x = Formula::Var("x".to_string(), Sort::Int);
        let body = Formula::Gt(
            Box::new(Formula::Mul(Box::new(var_x.clone()), Box::new(var_x))),
            Box::new(Formula::Int(0)),
        );
        let bindings = vec![("x".to_string(), Sort::Int)];
        let elim = QuantifierEliminator::new();
        let class = elim.classify(&bindings, &body);
        assert_eq!(class.tier, QuantifierTier::Full);
    }

    // === Tier 1 unrolling tests ===

    #[test]
    fn test_unroll_forall_small_range() {
        let body_inner = Formula::Ge(
            Box::new(Formula::Var("i".to_string(), Sort::Int)),
            Box::new(Formula::Int(0)),
        );
        let f = make_bounded_forall("i", 0, 3, body_inner);
        let mut elim = QuantifierEliminator::new();
        let result = elim.eliminate(&f);

        // Should produce And([..., ..., ...]) with 3 conjuncts.
        // Each conjunct is the substituted implication.
        match &result {
            Formula::And(conjuncts) => {
                assert_eq!(conjuncts.len(), 3, "0..3 should produce 3 conjuncts");
            }
            _ => panic!("expected And after unrolling, got: {result:?}"),
        }
        assert_eq!(elim.stats().tier1_eliminated, 1);
    }

    #[test]
    fn test_unroll_exists_small_range() {
        let body_inner = Formula::Eq(
            Box::new(Formula::Var("j".to_string(), Sort::Int)),
            Box::new(Formula::Int(5)),
        );
        let f = make_bounded_exists("j", 0, 3, body_inner);
        let mut elim = QuantifierEliminator::new();
        let result = elim.eliminate(&f);

        // Should produce Or([..., ..., ...]) with 3 disjuncts.
        match &result {
            Formula::Or(disjuncts) => {
                assert_eq!(disjuncts.len(), 3, "0..3 should produce 3 disjuncts");
            }
            _ => panic!("expected Or after unrolling exists, got: {result:?}"),
        }
        assert_eq!(elim.stats().tier1_eliminated, 1);
    }

    #[test]
    fn test_unroll_single_value() {
        let body_inner = Formula::Bool(true);
        let f = make_bounded_forall("i", 5, 6, body_inner);
        let mut elim = QuantifierEliminator::new();
        let result = elim.eliminate(&f);

        // Single value — no And wrapper needed.
        assert!(
            !matches!(&result, Formula::Forall(..)),
            "should not remain quantified"
        );
        assert_eq!(elim.stats().tier1_eliminated, 1);
    }

    #[test]
    fn test_unroll_empty_range_not_tier1() {
        // lo >= hi means empty range — Tier 1 cannot unroll it.
        let body_inner = Formula::Bool(false);
        // Range 5..3 is empty, detection won't find a valid range for Tier 1.
        // With Tier 2 disabled, it falls to Full and stays intact.
        let config = QuantifierConfig { max_unroll: 64, enable_tier2: false };
        let f = make_bounded_forall("i", 5, 3, body_inner);
        let mut elim = QuantifierEliminator::with_config(config);
        let result = elim.eliminate(&f);
        assert_eq!(elim.stats().tier1_eliminated, 0, "Tier 1 should not fire on empty range");
        assert_eq!(elim.stats().left_intact, 1);
        assert!(matches!(result, Formula::Forall(..)));
    }

    #[test]
    fn test_unroll_respects_max_bound() {
        let config = QuantifierConfig { max_unroll: 5, enable_tier2: false };
        let body_inner = Formula::Bool(true);
        let f = make_bounded_forall("i", 0, 10, body_inner);
        let mut elim = QuantifierEliminator::with_config(config);
        let result = elim.eliminate(&f);

        // 10 > max_unroll=5, tier2 disabled => Full (left intact).
        assert_eq!(elim.stats().left_intact, 1);
        assert!(matches!(result, Formula::Forall(..)));
    }

    #[test]
    fn test_unroll_with_custom_large_bound() {
        let config = QuantifierConfig { max_unroll: 1024, enable_tier2: true };
        let body_inner = Formula::Bool(true);
        let f = make_bounded_forall("i", 0, 500, body_inner);
        let mut elim = QuantifierEliminator::with_config(config);
        let result = elim.eliminate(&f);

        match &result {
            Formula::And(conjuncts) => {
                assert_eq!(conjuncts.len(), 500);
            }
            _ => panic!("expected And with 500 conjuncts"),
        }
        assert_eq!(elim.stats().tier1_eliminated, 1);
    }

    // === Substitution tests ===

    #[test]
    fn test_substitute_var() {
        let f = Formula::Var("x".to_string(), Sort::Int);
        let result = substitute(&f, "x", &Formula::Int(42));
        assert!(matches!(result, Formula::Int(42)));
    }

    #[test]
    fn test_substitute_different_var_unchanged() {
        let f = Formula::Var("y".to_string(), Sort::Int);
        let result = substitute(&f, "x", &Formula::Int(42));
        assert!(matches!(result, Formula::Var(name, _) if name == "y"));
    }

    #[test]
    fn test_substitute_in_comparison() {
        let f = Formula::Lt(
            Box::new(Formula::Var("x".to_string(), Sort::Int)),
            Box::new(Formula::Int(10)),
        );
        let result = substitute(&f, "x", &Formula::Int(5));
        match result {
            Formula::Lt(a, b) => {
                assert!(matches!(*a, Formula::Int(5)));
                assert!(matches!(*b, Formula::Int(10)));
            }
            other => panic!("expected Lt, got: {other:?}"),
        }
    }

    #[test]
    fn test_substitute_respects_binding() {
        // forall x. x > 0  — substituting x should NOT affect the bound x
        let inner = Formula::Gt(
            Box::new(Formula::Var("x".to_string(), Sort::Int)),
            Box::new(Formula::Int(0)),
        );
        let f = Formula::Forall(vec![("x".to_string(), Sort::Int)], Box::new(inner));
        let result = substitute(&f, "x", &Formula::Int(99));
        // Should remain unchanged.
        assert!(matches!(result, Formula::Forall(..)));
    }

    #[test]
    fn test_substitute_in_arithmetic() {
        let f = Formula::Add(
            Box::new(Formula::Var("x".to_string(), Sort::Int)),
            Box::new(Formula::Var("y".to_string(), Sort::Int)),
        );
        let result = substitute(&f, "x", &Formula::Int(3));
        match result {
            Formula::Add(a, b) => {
                assert!(matches!(*a, Formula::Int(3)));
                assert!(matches!(*b, Formula::Var(name, _) if name == "y"));
            }
            other => panic!("expected Add, got: {other:?}"),
        }
    }

    // === Presburger detection tests ===

    #[test]
    fn test_is_presburger_linear() {
        // 2*x + y > 0 is Presburger
        let f = Formula::Gt(
            Box::new(Formula::Add(
                Box::new(Formula::Mul(
                    Box::new(Formula::Int(2)),
                    Box::new(Formula::Var("x".to_string(), Sort::Int)),
                )),
                Box::new(Formula::Var("y".to_string(), Sort::Int)),
            )),
            Box::new(Formula::Int(0)),
        );
        let bindings = vec![("x".to_string(), Sort::Int)];
        assert!(is_presburger(&bindings, &f));
    }

    #[test]
    fn test_is_not_presburger_nonlinear() {
        // x * x > 0 is NOT Presburger
        let x = Formula::Var("x".to_string(), Sort::Int);
        let f = Formula::Gt(
            Box::new(Formula::Mul(Box::new(x.clone()), Box::new(x))),
            Box::new(Formula::Int(0)),
        );
        let bindings = vec![("x".to_string(), Sort::Int)];
        assert!(!is_presburger(&bindings, &f));
    }

    #[test]
    fn test_is_presburger_with_div_by_const() {
        // x / 2 > 0 IS Presburger (div by constant)
        let f = Formula::Gt(
            Box::new(Formula::Div(
                Box::new(Formula::Var("x".to_string(), Sort::Int)),
                Box::new(Formula::Int(2)),
            )),
            Box::new(Formula::Int(0)),
        );
        let bindings = vec![("x".to_string(), Sort::Int)];
        assert!(is_presburger(&bindings, &f));
    }

    #[test]
    fn test_is_not_presburger_with_select() {
        // Select(arr, x) > 0 is NOT Presburger
        let f = Formula::Gt(
            Box::new(Formula::Select(
                Box::new(Formula::Var("arr".to_string(), Sort::Array(
                    Box::new(Sort::Int),
                    Box::new(Sort::Int),
                ))),
                Box::new(Formula::Var("x".to_string(), Sort::Int)),
            )),
            Box::new(Formula::Int(0)),
        );
        let bindings = vec![("x".to_string(), Sort::Int)];
        assert!(!is_presburger(&bindings, &f));
    }

    #[test]
    fn test_is_presburger_with_remainder() {
        // x % 3 == 0 IS Presburger (divisibility constraint)
        let f = Formula::Eq(
            Box::new(Formula::Rem(
                Box::new(Formula::Var("x".to_string(), Sort::Int)),
                Box::new(Formula::Int(3)),
            )),
            Box::new(Formula::Int(0)),
        );
        let bindings = vec![("x".to_string(), Sort::Int)];
        assert!(is_presburger(&bindings, &f));
    }

    // === Fragment classification tests ===

    #[test]
    fn test_classify_presburger() {
        let f = Formula::Gt(
            Box::new(Formula::Add(
                Box::new(Formula::Var("x".to_string(), Sort::Int)),
                Box::new(Formula::Int(1)),
            )),
            Box::new(Formula::Int(0)),
        );
        assert_eq!(classify_fragment(&f), ArithmeticFragment::Presburger);
    }

    #[test]
    fn test_classify_bitvector() {
        let f = Formula::BvAdd(
            Box::new(Formula::Var("x".to_string(), Sort::BitVec(32))),
            Box::new(Formula::BitVec { value: 1, width: 32 }),
            32,
        );
        assert_eq!(classify_fragment(&f), ArithmeticFragment::Bitvector);
    }

    #[test]
    fn test_classify_array_linear() {
        let f = Formula::Eq(
            Box::new(Formula::Select(
                Box::new(Formula::Var(
                    "arr".to_string(),
                    Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int)),
                )),
                Box::new(Formula::Add(
                    Box::new(Formula::Var("i".to_string(), Sort::Int)),
                    Box::new(Formula::Int(1)),
                )),
            )),
            Box::new(Formula::Int(0)),
        );
        assert_eq!(classify_fragment(&f), ArithmeticFragment::ArrayLinear);
    }

    #[test]
    fn test_classify_other() {
        // Non-linear: x * y
        let f = Formula::Gt(
            Box::new(Formula::Mul(
                Box::new(Formula::Var("x".to_string(), Sort::Int)),
                Box::new(Formula::Var("y".to_string(), Sort::Int)),
            )),
            Box::new(Formula::Int(0)),
        );
        assert_eq!(classify_fragment(&f), ArithmeticFragment::Other);
    }

    // === Cooper's method tests ===

    #[test]
    fn test_cooper_exists_simple() {
        // exists x. x >= 0 && x < 5 && x == 3
        let var_x = Formula::Var("x".to_string(), Sort::Int);
        let body = Formula::And(vec![
            Formula::Ge(Box::new(var_x.clone()), Box::new(Formula::Int(0))),
            Formula::Lt(Box::new(var_x.clone()), Box::new(Formula::Int(5))),
            Formula::Eq(Box::new(var_x), Box::new(Formula::Int(3))),
        ]);
        let bindings = vec![("x".to_string(), Sort::Int)];
        let result = cooper_eliminate_exists(&bindings, &body);
        assert!(result.is_ok(), "Cooper should handle simple exists");
    }

    #[test]
    fn test_cooper_forall_variable_not_in_body() {
        // forall x. true => y > 0  (x not in body)
        let body = Formula::Implies(
            Box::new(Formula::Bool(true)),
            Box::new(Formula::Gt(
                Box::new(Formula::Var("y".to_string(), Sort::Int)),
                Box::new(Formula::Int(0)),
            )),
        );
        let bindings = vec![("x".to_string(), Sort::Int)];
        let result = cooper_eliminate_forall(&bindings, &body);
        // Should succeed since x doesn't appear.
        assert!(result.is_ok());
    }

    #[test]
    fn test_cooper_multi_var_fails() {
        let body = Formula::Bool(true);
        let bindings = vec![
            ("x".to_string(), Sort::Int),
            ("y".to_string(), Sort::Int),
        ];
        let result = cooper_eliminate_forall(&bindings, &body);
        assert!(result.is_err());
    }

    // === Recursive elimination tests ===

    #[test]
    fn test_eliminate_nested_quantifiers() {
        // forall i in 0..2. forall j in 0..2. i + j >= 0
        let inner_body = Formula::Ge(
            Box::new(Formula::Add(
                Box::new(Formula::Var("i".to_string(), Sort::Int)),
                Box::new(Formula::Var("j".to_string(), Sort::Int)),
            )),
            Box::new(Formula::Int(0)),
        );
        let inner = make_bounded_forall("j", 0, 2, inner_body);
        let outer = make_bounded_forall("i", 0, 2, inner);

        let mut elim = QuantifierEliminator::new();
        let result = elim.eliminate(&outer);

        // Both should be unrolled.
        assert!(!matches!(result, Formula::Forall(..)));
        assert!(elim.stats().tier1_eliminated >= 2);
    }

    #[test]
    fn test_eliminate_non_quantified_passthrough() {
        let f = Formula::And(vec![
            Formula::Gt(
                Box::new(Formula::Var("x".to_string(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            Formula::Lt(
                Box::new(Formula::Var("y".to_string(), Sort::Int)),
                Box::new(Formula::Int(10)),
            ),
        ]);
        let mut elim = QuantifierEliminator::new();
        let result = elim.eliminate(&f);
        // Non-quantified formulas pass through.
        assert!(matches!(result, Formula::And(_)));
        assert_eq!(elim.stats().tier1_eliminated, 0);
        assert_eq!(elim.stats().tier2_eliminated, 0);
    }

    #[test]
    fn test_eliminate_in_implies() {
        // (forall i in 0..3. i >= 0) => x > 0
        let inner = make_bounded_forall(
            "i",
            0,
            3,
            Formula::Ge(
                Box::new(Formula::Var("i".to_string(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
        );
        let f = Formula::Implies(
            Box::new(inner),
            Box::new(Formula::Gt(
                Box::new(Formula::Var("x".to_string(), Sort::Int)),
                Box::new(Formula::Int(0)),
            )),
        );
        let mut elim = QuantifierEliminator::new();
        let result = elim.eliminate(&f);
        assert!(matches!(result, Formula::Implies(..)));
        assert_eq!(elim.stats().tier1_eliminated, 1);
    }

    // === Free variables test ===

    #[test]
    fn test_free_vars() {
        let f = Formula::And(vec![
            Formula::Var("x".to_string(), Sort::Int),
            Formula::Forall(
                vec![("y".to_string(), Sort::Int)],
                Box::new(Formula::Var("y".to_string(), Sort::Int)),
            ),
            Formula::Var("z".to_string(), Sort::Bool),
        ]);
        let fv = free_vars(&f);
        assert!(fv.contains("x"));
        assert!(fv.contains("z"));
        assert!(!fv.contains("y"), "y is bound by forall");
    }

    #[test]
    fn test_free_vars_nested() {
        // exists x. forall y. x + y > z
        let body = Formula::Gt(
            Box::new(Formula::Add(
                Box::new(Formula::Var("x".to_string(), Sort::Int)),
                Box::new(Formula::Var("y".to_string(), Sort::Int)),
            )),
            Box::new(Formula::Var("z".to_string(), Sort::Int)),
        );
        let inner = Formula::Forall(vec![("y".to_string(), Sort::Int)], Box::new(body));
        let outer = Formula::Exists(vec![("x".to_string(), Sort::Int)], Box::new(inner));
        let fv = free_vars(&outer);
        assert!(fv.contains("z"));
        assert!(!fv.contains("x"));
        assert!(!fv.contains("y"));
    }

    // === Default / config tests ===

    #[test]
    fn test_default_config() {
        let config = QuantifierConfig::default();
        assert_eq!(config.max_unroll, 64);
        assert!(config.enable_tier2);
    }

    #[test]
    fn test_eliminator_default() {
        let elim = QuantifierEliminator::default();
        assert_eq!(elim.stats().tier1_eliminated, 0);
        assert_eq!(elim.stats().tier2_eliminated, 0);
        assert_eq!(elim.stats().left_intact, 0);
    }

    #[test]
    fn test_tier2_disabled() {
        let config = QuantifierConfig { max_unroll: 5, enable_tier2: false };
        let body_inner = Formula::Ge(
            Box::new(Formula::Var("i".to_string(), Sort::Int)),
            Box::new(Formula::Int(0)),
        );
        // Range 0..100 exceeds max_unroll=5, tier2 disabled => Full
        let f = make_bounded_forall("i", 0, 100, body_inner);
        let elim = QuantifierEliminator::with_config(config);
        if let Formula::Forall(bindings, body) = &f {
            let class = elim.classify(bindings, body);
            assert_eq!(class.tier, QuantifierTier::Full);
        }
    }

    // === Sorted array bounds check reduces to Presburger (acceptance criterion) ===

    #[test]
    fn test_sorted_array_bounds_presburger() {
        // forall i. 0 <= i && i < n => i >= 0
        // This is a Presburger formula (no arrays, linear integer arithmetic)
        let i = Formula::Var("i".to_string(), Sort::Int);
        let n = Formula::Var("n".to_string(), Sort::Int);
        let guard = Formula::And(vec![
            Formula::Le(Box::new(Formula::Int(0)), Box::new(i.clone())),
            Formula::Lt(Box::new(i.clone()), Box::new(n)),
        ]);
        let body = Formula::Ge(Box::new(i), Box::new(Formula::Int(0)));
        let formula = Formula::Forall(
            vec![("i".to_string(), Sort::Int)],
            Box::new(Formula::Implies(Box::new(guard), Box::new(body))),
        );

        let fragment = classify_fragment(&formula);
        assert!(
            matches!(fragment, ArithmeticFragment::Presburger),
            "sorted array bounds check should be Presburger, got: {fragment:?}"
        );
    }

    // === is_decidable_arithmetic tests ===

    #[test]
    fn test_is_decidable_arithmetic_presburger() {
        // 2*x + 1 > 0 — Presburger, decidable
        let f = Formula::Gt(
            Box::new(Formula::Add(
                Box::new(Formula::Mul(
                    Box::new(Formula::Int(2)),
                    Box::new(Formula::Var("x".to_string(), Sort::Int)),
                )),
                Box::new(Formula::Int(1)),
            )),
            Box::new(Formula::Int(0)),
        );
        assert!(is_decidable_arithmetic(&f));
    }

    #[test]
    fn test_is_decidable_arithmetic_bitvector() {
        let f = Formula::BvAdd(
            Box::new(Formula::Var("x".to_string(), Sort::BitVec(32))),
            Box::new(Formula::BitVec { value: 1, width: 32 }),
            32,
        );
        assert!(is_decidable_arithmetic(&f));
    }

    #[test]
    fn test_is_decidable_arithmetic_nonlinear_not_decidable() {
        // x * y — non-linear, not decidable
        let f = Formula::Gt(
            Box::new(Formula::Mul(
                Box::new(Formula::Var("x".to_string(), Sort::Int)),
                Box::new(Formula::Var("y".to_string(), Sort::Int)),
            )),
            Box::new(Formula::Int(0)),
        );
        assert!(!is_decidable_arithmetic(&f));
    }

    #[test]
    fn test_is_decidable_arithmetic_array_linear() {
        let f = Formula::Eq(
            Box::new(Formula::Select(
                Box::new(Formula::Var(
                    "arr".to_string(),
                    Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int)),
                )),
                Box::new(Formula::Var("i".to_string(), Sort::Int)),
            )),
            Box::new(Formula::Int(0)),
        );
        assert!(is_decidable_arithmetic(&f));
    }

    // === has_quantifiers tests ===

    #[test]
    fn test_has_quantifiers_none() {
        let f = Formula::Gt(
            Box::new(Formula::Var("x".to_string(), Sort::Int)),
            Box::new(Formula::Int(0)),
        );
        assert!(!has_quantifiers(&f));
    }

    #[test]
    fn test_has_quantifiers_forall() {
        let f = Formula::Forall(
            vec![("x".to_string(), Sort::Int)],
            Box::new(Formula::Bool(true)),
        );
        assert!(has_quantifiers(&f));
    }

    #[test]
    fn test_has_quantifiers_nested() {
        // And(x > 0, forall y. y > 0)
        let f = Formula::And(vec![
            Formula::Gt(
                Box::new(Formula::Var("x".to_string(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            Formula::Forall(
                vec![("y".to_string(), Sort::Int)],
                Box::new(Formula::Gt(
                    Box::new(Formula::Var("y".to_string(), Sort::Int)),
                    Box::new(Formula::Int(0)),
                )),
            ),
        ]);
        assert!(has_quantifiers(&f));
    }

    #[test]
    fn test_has_quantifiers_exists() {
        let f = Formula::Exists(
            vec![("x".to_string(), Sort::Int)],
            Box::new(Formula::Eq(
                Box::new(Formula::Var("x".to_string(), Sort::Int)),
                Box::new(Formula::Int(42)),
            )),
        );
        assert!(has_quantifiers(&f));
    }

    // === apply_tier_strategy tests ===

    #[test]
    fn test_strategy_quantifier_free() {
        let f = Formula::Gt(
            Box::new(Formula::Var("x".to_string(), Sort::Int)),
            Box::new(Formula::Int(0)),
        );
        let config = QuantifierConfig::default();
        assert_eq!(apply_tier_strategy(&f, &config), SolverStrategy::QuantifierFree);
    }

    #[test]
    fn test_strategy_unroll_small_bounded() {
        // forall i in 0..5. i >= 0 — small finite domain => Unroll
        let body_inner = Formula::Ge(
            Box::new(Formula::Var("i".to_string(), Sort::Int)),
            Box::new(Formula::Int(0)),
        );
        let f = make_bounded_forall("i", 0, 5, body_inner);
        let config = QuantifierConfig::default();
        assert_eq!(apply_tier_strategy(&f, &config), SolverStrategy::Unroll);
    }

    #[test]
    fn test_strategy_decidable_large_bounded() {
        // forall i in 0..1000. i >= 0 — too large to unroll, but Presburger
        let body_inner = Formula::Ge(
            Box::new(Formula::Var("i".to_string(), Sort::Int)),
            Box::new(Formula::Int(0)),
        );
        let f = make_bounded_forall("i", 0, 1000, body_inner);
        let config = QuantifierConfig::default();
        assert_eq!(apply_tier_strategy(&f, &config), SolverStrategy::DecidableTheory);
    }

    #[test]
    fn test_strategy_full_quantifier_nonlinear() {
        // forall x. x * x > 0 — non-linear, not Presburger
        let var_x = Formula::Var("x".to_string(), Sort::Int);
        let body = Formula::Gt(
            Box::new(Formula::Mul(Box::new(var_x.clone()), Box::new(var_x))),
            Box::new(Formula::Int(0)),
        );
        let f = Formula::Forall(vec![("x".to_string(), Sort::Int)], Box::new(body));
        let config = QuantifierConfig::default();
        assert_eq!(apply_tier_strategy(&f, &config), SolverStrategy::FullQuantifier);
    }

    #[test]
    fn test_strategy_nested_quantifier_in_and() {
        // And(x > 0, forall i in 0..3. i >= 0)
        // The overall strategy should be Unroll (from the quantifier).
        let inner = make_bounded_forall(
            "i",
            0,
            3,
            Formula::Ge(
                Box::new(Formula::Var("i".to_string(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
        );
        let f = Formula::And(vec![
            Formula::Gt(
                Box::new(Formula::Var("x".to_string(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            inner,
        ]);
        let config = QuantifierConfig::default();
        assert_eq!(apply_tier_strategy(&f, &config), SolverStrategy::Unroll);
    }

    #[test]
    fn test_strategy_mixed_tiers_takes_worst() {
        // And(forall i in 0..3. i >= 0, forall x. x*x > 0)
        // Tier 1 (Unroll) vs Tier Full => Full wins
        let tier1 = make_bounded_forall(
            "i",
            0,
            3,
            Formula::Ge(
                Box::new(Formula::Var("i".to_string(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
        );
        let var_x = Formula::Var("x".to_string(), Sort::Int);
        let tier_full = Formula::Forall(
            vec![("x".to_string(), Sort::Int)],
            Box::new(Formula::Gt(
                Box::new(Formula::Mul(Box::new(var_x.clone()), Box::new(var_x))),
                Box::new(Formula::Int(0)),
            )),
        );
        let f = Formula::And(vec![tier1, tier_full]);
        let config = QuantifierConfig::default();
        assert_eq!(apply_tier_strategy(&f, &config), SolverStrategy::FullQuantifier);
    }

    // === Tier 1 edge case: Ge/Gt bounds ===

    #[test]
    fn test_unroll_with_ge_upper_bound() {
        // forall i. i >= 0 && i <= 2 => body
        // Le(i, 2) means hi = 2 + 1 = 3 (exclusive), so domain = [0, 1, 2]
        let var_i = Formula::Var("i".to_string(), Sort::Int);
        let guard = Formula::And(vec![
            Formula::Ge(Box::new(var_i.clone()), Box::new(Formula::Int(0))),
            Formula::Le(Box::new(var_i.clone()), Box::new(Formula::Int(2))),
        ]);
        let body = Formula::Gt(Box::new(var_i), Box::new(Formula::Int(-1)));
        let f = Formula::Forall(
            vec![("i".to_string(), Sort::Int)],
            Box::new(Formula::Implies(Box::new(guard), Box::new(body))),
        );
        let mut elim = QuantifierEliminator::new();
        let result = elim.eliminate(&f);
        assert_eq!(elim.stats().tier1_eliminated, 1);
        match &result {
            Formula::And(conjuncts) => assert_eq!(conjuncts.len(), 3),
            _ => panic!("expected And with 3 conjuncts, got: {result:?}"),
        }
    }

    #[test]
    fn test_unroll_with_gt_lower_bound() {
        // forall i. i > 0 && i < 4 => body
        // Gt(i, 0) means lo = 0 + 1 = 1 (strict), Lt(i, 4) means hi = 4
        // Domain = [1, 2, 3]
        let var_i = Formula::Var("i".to_string(), Sort::Int);
        let guard = Formula::And(vec![
            Formula::Gt(Box::new(var_i.clone()), Box::new(Formula::Int(0))),
            Formula::Lt(Box::new(var_i.clone()), Box::new(Formula::Int(4))),
        ]);
        let body = Formula::Gt(Box::new(var_i), Box::new(Formula::Int(0)));
        let f = Formula::Forall(
            vec![("i".to_string(), Sort::Int)],
            Box::new(Formula::Implies(Box::new(guard), Box::new(body))),
        );
        let mut elim = QuantifierEliminator::new();
        let result = elim.eliminate(&f);
        assert_eq!(elim.stats().tier1_eliminated, 1);
        match &result {
            Formula::And(conjuncts) => assert_eq!(conjuncts.len(), 3),
            _ => panic!("expected And with 3 conjuncts, got: {result:?}"),
        }
    }

    // === Tier 2 Cooper's method: additional edge cases ===

    #[test]
    fn test_cooper_exists_with_multiple_lower_bounds() {
        // exists x. x >= 0 && x >= 3 && x < 1000
        // Domain 0..1000 exceeds default max_unroll=64, so Tier 2 (Cooper) fires.
        // Two lower bounds: 0 and 3. Cooper generates substitutions for both.
        let var_x = Formula::Var("x".to_string(), Sort::Int);
        let body = Formula::And(vec![
            Formula::Ge(Box::new(var_x.clone()), Box::new(Formula::Int(0))),
            Formula::Ge(Box::new(var_x.clone()), Box::new(Formula::Int(3))),
            Formula::Lt(Box::new(var_x), Box::new(Formula::Int(1000))),
        ]);
        let f = Formula::Exists(
            vec![("x".to_string(), Sort::Int)],
            Box::new(body),
        );
        let mut elim = QuantifierEliminator::new();
        let result = elim.eliminate(&f);
        assert_eq!(elim.stats().tier2_eliminated, 1);
        // Should be an Or of substitutions (one per lower bound).
        assert!(matches!(result, Formula::Or(_)));
    }

    #[test]
    fn test_cooper_forall_tautology_x_eq_x() {
        // forall x. x == x
        let var_x = Formula::Var("x".to_string(), Sort::Int);
        let body = Formula::Eq(Box::new(var_x.clone()), Box::new(var_x));
        let f = Formula::Forall(
            vec![("x".to_string(), Sort::Int)],
            Box::new(body),
        );
        let mut elim = QuantifierEliminator::new();
        let result = elim.eliminate(&f);
        assert_eq!(elim.stats().tier2_eliminated, 1);
        assert!(matches!(result, Formula::Bool(true)));
    }

    // === Presburger edge cases ===

    #[test]
    fn test_is_presburger_nested_quantifiers() {
        // forall x. exists y. x + y > 0
        // Both quantifiers bind Int vars with linear body — Presburger.
        let body = Formula::Gt(
            Box::new(Formula::Add(
                Box::new(Formula::Var("x".to_string(), Sort::Int)),
                Box::new(Formula::Var("y".to_string(), Sort::Int)),
            )),
            Box::new(Formula::Int(0)),
        );
        let inner = Formula::Exists(
            vec![("y".to_string(), Sort::Int)],
            Box::new(body),
        );
        let bindings = vec![("x".to_string(), Sort::Int)];
        assert!(is_presburger(&bindings, &inner));
    }

    #[test]
    fn test_is_not_presburger_bool_bound_var() {
        // forall b: Bool. b  — Bool bound var, not Presburger
        let body = Formula::Var("b".to_string(), Sort::Bool);
        let bindings = vec![("b".to_string(), Sort::Bool)];
        assert!(!is_presburger(&bindings, &body));
    }

    #[test]
    fn test_is_presburger_ite_linear() {
        // ite(x > 0, x + 1, x - 1) > 0 — linear, with Ite
        let x = Formula::Var("x".to_string(), Sort::Int);
        let cond = Formula::Gt(Box::new(x.clone()), Box::new(Formula::Int(0)));
        let then_br = Formula::Add(Box::new(x.clone()), Box::new(Formula::Int(1)));
        let else_br = Formula::Sub(Box::new(x), Box::new(Formula::Int(1)));
        let body = Formula::Gt(
            Box::new(Formula::Ite(
                Box::new(cond),
                Box::new(then_br),
                Box::new(else_br),
            )),
            Box::new(Formula::Int(0)),
        );
        let bindings = vec![("x".to_string(), Sort::Int)];
        assert!(is_presburger(&bindings, &body));
    }

    // === Substitute edge cases ===

    #[test]
    fn test_substitute_in_ite() {
        let f = Formula::Ite(
            Box::new(Formula::Var("x".to_string(), Sort::Bool)),
            Box::new(Formula::Var("x".to_string(), Sort::Int)),
            Box::new(Formula::Int(0)),
        );
        let result = substitute(&f, "x", &Formula::Int(1));
        match result {
            Formula::Ite(c, t, _) => {
                assert!(matches!(*c, Formula::Int(1)));
                assert!(matches!(*t, Formula::Int(1)));
            }
            other => panic!("expected Ite, got: {other:?}"),
        }
    }

    #[test]
    fn test_substitute_in_select_store() {
        let arr = Formula::Var("a".to_string(), Sort::Array(
            Box::new(Sort::Int), Box::new(Sort::Int),
        ));
        let f = Formula::Select(
            Box::new(arr),
            Box::new(Formula::Var("i".to_string(), Sort::Int)),
        );
        let result = substitute(&f, "i", &Formula::Int(7));
        match result {
            Formula::Select(_, idx) => {
                assert!(matches!(*idx, Formula::Int(7)));
            }
            other => panic!("expected Select, got: {other:?}"),
        }
    }

    // === SolverStrategy enum tests ===

    #[test]
    fn test_solver_strategy_debug() {
        // Verify all variants are constructible and Debug works.
        let strategies = [
            SolverStrategy::QuantifierFree,
            SolverStrategy::Unroll,
            SolverStrategy::DecidableTheory,
            SolverStrategy::FullQuantifier,
        ];
        for s in &strategies {
            let dbg = format!("{s:?}");
            assert!(!dbg.is_empty());
        }
    }

    #[test]
    fn test_worse_strategy_ordering() {
        assert_eq!(
            worse_strategy(SolverStrategy::QuantifierFree, SolverStrategy::Unroll),
            SolverStrategy::Unroll,
        );
        assert_eq!(
            worse_strategy(SolverStrategy::Unroll, SolverStrategy::DecidableTheory),
            SolverStrategy::DecidableTheory,
        );
        assert_eq!(
            worse_strategy(SolverStrategy::DecidableTheory, SolverStrategy::FullQuantifier),
            SolverStrategy::FullQuantifier,
        );
        assert_eq!(
            worse_strategy(SolverStrategy::FullQuantifier, SolverStrategy::QuantifierFree),
            SolverStrategy::FullQuantifier,
        );
    }

    // === QuantifierTier variant test ===

    #[test]
    fn test_quantifier_tier_quantifier_free() {
        // Verify the new QuantifierFree variant exists and compares correctly.
        assert_ne!(QuantifierTier::QuantifierFree, QuantifierTier::FiniteUnrolling);
        assert_ne!(QuantifierTier::QuantifierFree, QuantifierTier::DecidableArithmetic);
        assert_ne!(QuantifierTier::QuantifierFree, QuantifierTier::Full);
    }

    // =======================================================================
    // Pre-processing pass tests (#183)
    // =======================================================================

    // === QuantifierStats / analyze_quantifiers tests ===

    #[test]
    fn test_analyze_quantifiers_no_quantifiers() {
        let f = Formula::Gt(
            Box::new(Formula::Var("x".to_string(), Sort::Int)),
            Box::new(Formula::Int(0)),
        );
        let stats = analyze_quantifiers(&f);
        assert_eq!(stats.num_forall, 0);
        assert_eq!(stats.num_exists, 0);
        assert_eq!(stats.max_nesting_depth, 0);
        assert!(!stats.has_alternation);
    }

    #[test]
    fn test_analyze_quantifiers_single_forall() {
        let f = Formula::Forall(
            vec![("x".to_string(), Sort::Int)],
            Box::new(Formula::Bool(true)),
        );
        let stats = analyze_quantifiers(&f);
        assert_eq!(stats.num_forall, 1);
        assert_eq!(stats.num_exists, 0);
        assert_eq!(stats.max_nesting_depth, 1);
        assert!(!stats.has_alternation);
    }

    #[test]
    fn test_analyze_quantifiers_single_exists() {
        let f = Formula::Exists(
            vec![("x".to_string(), Sort::Int)],
            Box::new(Formula::Bool(true)),
        );
        let stats = analyze_quantifiers(&f);
        assert_eq!(stats.num_forall, 0);
        assert_eq!(stats.num_exists, 1);
        assert_eq!(stats.max_nesting_depth, 1);
        assert!(!stats.has_alternation);
    }

    #[test]
    fn test_analyze_quantifiers_nested_same_kind() {
        // forall x. forall y. true
        let f = Formula::Forall(
            vec![("x".to_string(), Sort::Int)],
            Box::new(Formula::Forall(
                vec![("y".to_string(), Sort::Int)],
                Box::new(Formula::Bool(true)),
            )),
        );
        let stats = analyze_quantifiers(&f);
        assert_eq!(stats.num_forall, 2);
        assert_eq!(stats.num_exists, 0);
        assert_eq!(stats.max_nesting_depth, 2);
        assert!(!stats.has_alternation);
    }

    #[test]
    fn test_analyze_quantifiers_alternation_forall_exists() {
        // forall x. exists y. x + y > 0
        let body = Formula::Gt(
            Box::new(Formula::Add(
                Box::new(Formula::Var("x".to_string(), Sort::Int)),
                Box::new(Formula::Var("y".to_string(), Sort::Int)),
            )),
            Box::new(Formula::Int(0)),
        );
        let f = Formula::Forall(
            vec![("x".to_string(), Sort::Int)],
            Box::new(Formula::Exists(
                vec![("y".to_string(), Sort::Int)],
                Box::new(body),
            )),
        );
        let stats = analyze_quantifiers(&f);
        assert_eq!(stats.num_forall, 1);
        assert_eq!(stats.num_exists, 1);
        assert_eq!(stats.max_nesting_depth, 2);
        assert!(stats.has_alternation);
    }

    #[test]
    fn test_analyze_quantifiers_alternation_exists_forall() {
        // exists x. forall y. x > y
        let body = Formula::Gt(
            Box::new(Formula::Var("x".to_string(), Sort::Int)),
            Box::new(Formula::Var("y".to_string(), Sort::Int)),
        );
        let f = Formula::Exists(
            vec![("x".to_string(), Sort::Int)],
            Box::new(Formula::Forall(
                vec![("y".to_string(), Sort::Int)],
                Box::new(body),
            )),
        );
        let stats = analyze_quantifiers(&f);
        assert!(stats.has_alternation);
        assert_eq!(stats.max_nesting_depth, 2);
    }

    #[test]
    fn test_analyze_quantifiers_sibling_quantifiers() {
        // And(forall x. P(x), exists y. Q(y)) — siblings, no alternation
        let f = Formula::And(vec![
            Formula::Forall(
                vec![("x".to_string(), Sort::Int)],
                Box::new(Formula::Bool(true)),
            ),
            Formula::Exists(
                vec![("y".to_string(), Sort::Int)],
                Box::new(Formula::Bool(false)),
            ),
        ]);
        let stats = analyze_quantifiers(&f);
        assert_eq!(stats.num_forall, 1);
        assert_eq!(stats.num_exists, 1);
        assert_eq!(stats.max_nesting_depth, 1);
        assert!(!stats.has_alternation);
    }

    #[test]
    fn test_analyze_quantifiers_default() {
        let stats = QuantifierStats::default();
        assert_eq!(stats.num_forall, 0);
        assert_eq!(stats.num_exists, 0);
        assert_eq!(stats.max_nesting_depth, 0);
        assert!(!stats.has_alternation);
    }

    // === classify_quantifiers tests ===

    #[test]
    fn test_classify_quantifiers_ground() {
        let f = Formula::Gt(
            Box::new(Formula::Var("x".to_string(), Sort::Int)),
            Box::new(Formula::Int(0)),
        );
        assert_eq!(classify_quantifiers(&f), QuantifierTier::QuantifierFree);
    }

    #[test]
    fn test_classify_quantifiers_bounded_forall() {
        let body_inner = Formula::Ge(
            Box::new(Formula::Var("i".to_string(), Sort::Int)),
            Box::new(Formula::Int(0)),
        );
        let f = make_bounded_forall("i", 0, 5, body_inner);
        assert_eq!(classify_quantifiers(&f), QuantifierTier::FiniteUnrolling);
    }

    #[test]
    fn test_classify_quantifiers_linear() {
        let body_inner = Formula::Ge(
            Box::new(Formula::Var("i".to_string(), Sort::Int)),
            Box::new(Formula::Int(0)),
        );
        // Range too large to unroll, but Presburger
        let f = make_bounded_forall("i", 0, 1000, body_inner);
        assert_eq!(classify_quantifiers(&f), QuantifierTier::DecidableArithmetic);
    }

    #[test]
    fn test_classify_quantifiers_nonlinear() {
        let x = Formula::Var("x".to_string(), Sort::Int);
        let body = Formula::Gt(
            Box::new(Formula::Mul(Box::new(x.clone()), Box::new(x))),
            Box::new(Formula::Int(0)),
        );
        let f = Formula::Forall(vec![("x".to_string(), Sort::Int)], Box::new(body));
        assert_eq!(classify_quantifiers(&f), QuantifierTier::Full);
    }

    // === skolemize tests ===

    #[test]
    fn test_skolemize_no_exists() {
        let f = Formula::Forall(
            vec![("x".to_string(), Sort::Int)],
            Box::new(Formula::Gt(
                Box::new(Formula::Var("x".to_string(), Sort::Int)),
                Box::new(Formula::Int(0)),
            )),
        );
        let result = skolemize(&f);
        // No existentials — should be unchanged.
        assert!(matches!(result, Formula::Forall(..)));
    }

    #[test]
    fn test_skolemize_simple_exists() {
        // exists x. x > 0  =>  skolem_x_N > 0
        let f = Formula::Exists(
            vec![("x".to_string(), Sort::Int)],
            Box::new(Formula::Gt(
                Box::new(Formula::Var("x".to_string(), Sort::Int)),
                Box::new(Formula::Int(0)),
            )),
        );
        let result = skolemize(&f);
        // Should not be Exists anymore.
        assert!(
            !matches!(result, Formula::Exists(..)),
            "exists should be eliminated, got: {result:?}"
        );
        // Should be Gt(Var(skolem_x_N, Int), Int(0))
        match &result {
            Formula::Gt(a, _) => {
                if let Formula::Var(name, sort) = a.as_ref() {
                    assert!(name.starts_with("skolem_x_"), "expected Skolem var, got: {name}");
                    assert_eq!(*sort, Sort::Int);
                } else {
                    panic!("expected Var in skolemized formula, got: {a:?}");
                }
            }
            other => panic!("expected Gt, got: {other:?}"),
        }
    }

    #[test]
    fn test_skolemize_exists_under_forall() {
        // forall y. exists x. x > y
        // => forall y. skolem_x_N(y) > y
        let body = Formula::Gt(
            Box::new(Formula::Var("x".to_string(), Sort::Int)),
            Box::new(Formula::Var("y".to_string(), Sort::Int)),
        );
        let f = Formula::Forall(
            vec![("y".to_string(), Sort::Int)],
            Box::new(Formula::Exists(
                vec![("x".to_string(), Sort::Int)],
                Box::new(body),
            )),
        );
        let result = skolemize(&f);
        // Should still have Forall, but no Exists.
        assert!(matches!(result, Formula::Forall(..)));
        let mut has_exists = false;
        result.visit(&mut |node| {
            if matches!(node, Formula::Exists(..)) {
                has_exists = true;
            }
        });
        assert!(!has_exists, "exists should be eliminated after skolemization");
        // The Skolem variable name should contain the universal parameter.
        let mut skolem_var = None;
        result.visit(&mut |node| {
            if let Formula::Var(name, _) = node
                && name.starts_with("skolem_x_")
            {
                skolem_var = Some(name.clone());
            }
        });
        let sv = skolem_var.expect("should have a Skolem variable");
        assert!(sv.contains("(y)"), "Skolem var should depend on universal y, got: {sv}");
    }

    #[test]
    fn test_skolemize_multiple_exists_bindings() {
        // exists x, y. x + y > 0  => skolem_x + skolem_y > 0
        let body = Formula::Gt(
            Box::new(Formula::Add(
                Box::new(Formula::Var("x".to_string(), Sort::Int)),
                Box::new(Formula::Var("y".to_string(), Sort::Int)),
            )),
            Box::new(Formula::Int(0)),
        );
        let f = Formula::Exists(
            vec![("x".to_string(), Sort::Int), ("y".to_string(), Sort::Int)],
            Box::new(body),
        );
        let result = skolemize(&f);
        assert!(!matches!(result, Formula::Exists(..)));
        let mut skolem_count = 0;
        result.visit(&mut |node| {
            if let Formula::Var(name, _) = node
                && name.starts_with("skolem_")
            {
                skolem_count += 1;
            }
        });
        assert_eq!(skolem_count, 2, "should have 2 Skolem variables (one for x, one for y)");
    }

    #[test]
    fn test_skolemize_no_quantifiers() {
        let f = Formula::Gt(
            Box::new(Formula::Var("x".to_string(), Sort::Int)),
            Box::new(Formula::Int(0)),
        );
        let result = skolemize(&f);
        assert_eq!(result, f);
    }

    // === instantiate_universal tests ===

    #[test]
    fn test_instantiate_universal_simple() {
        // forall x. x > 0, instantiate with [Int(5)]
        let f = Formula::Forall(
            vec![("x".to_string(), Sort::Int)],
            Box::new(Formula::Gt(
                Box::new(Formula::Var("x".to_string(), Sort::Int)),
                Box::new(Formula::Int(0)),
            )),
        );
        let result = instantiate_universal(&f, &[Formula::Int(5)]);
        match &result {
            Formula::Gt(a, b) => {
                assert_eq!(**a, Formula::Int(5));
                assert_eq!(**b, Formula::Int(0));
            }
            other => panic!("expected Gt, got: {other:?}"),
        }
    }

    #[test]
    fn test_instantiate_universal_multi_binding() {
        // forall x, y. x + y > 0, instantiate with [Int(3), Int(4)]
        let f = Formula::Forall(
            vec![("x".to_string(), Sort::Int), ("y".to_string(), Sort::Int)],
            Box::new(Formula::Gt(
                Box::new(Formula::Add(
                    Box::new(Formula::Var("x".to_string(), Sort::Int)),
                    Box::new(Formula::Var("y".to_string(), Sort::Int)),
                )),
                Box::new(Formula::Int(0)),
            )),
        );
        let result = instantiate_universal(&f, &[Formula::Int(3), Formula::Int(4)]);
        // Should be 3 + 4 > 0
        match &result {
            Formula::Gt(a, _) => {
                match a.as_ref() {
                    Formula::Add(l, r) => {
                        assert_eq!(**l, Formula::Int(3));
                        assert_eq!(**r, Formula::Int(4));
                    }
                    other => panic!("expected Add, got: {other:?}"),
                }
            }
            other => panic!("expected Gt, got: {other:?}"),
        }
    }

    #[test]
    fn test_instantiate_universal_partial() {
        // forall x, y. body, instantiate with only [Int(1)]
        // x gets replaced, y stays bound
        let f = Formula::Forall(
            vec![("x".to_string(), Sort::Int), ("y".to_string(), Sort::Int)],
            Box::new(Formula::Add(
                Box::new(Formula::Var("x".to_string(), Sort::Int)),
                Box::new(Formula::Var("y".to_string(), Sort::Int)),
            )),
        );
        let result = instantiate_universal(&f, &[Formula::Int(7)]);
        // Should be forall y. 7 + y
        match &result {
            Formula::Forall(bindings, body) => {
                assert_eq!(bindings.len(), 1);
                assert_eq!(bindings[0].0, "y");
                match body.as_ref() {
                    Formula::Add(a, b) => {
                        assert_eq!(**a, Formula::Int(7));
                        assert!(matches!(b.as_ref(), Formula::Var(n, _) if n == "y"));
                    }
                    other => panic!("expected Add, got: {other:?}"),
                }
            }
            other => panic!("expected Forall, got: {other:?}"),
        }
    }

    #[test]
    fn test_instantiate_universal_empty_terms() {
        let f = Formula::Forall(
            vec![("x".to_string(), Sort::Int)],
            Box::new(Formula::Bool(true)),
        );
        let result = instantiate_universal(&f, &[]);
        assert!(matches!(result, Formula::Forall(..)));
    }

    #[test]
    fn test_instantiate_universal_non_forall_passthrough() {
        let f = Formula::Gt(
            Box::new(Formula::Var("x".to_string(), Sort::Int)),
            Box::new(Formula::Int(0)),
        );
        let result = instantiate_universal(&f, &[Formula::Int(5)]);
        assert_eq!(result, f);
    }

    // === simplify_quantified tests ===

    #[test]
    fn test_simplify_vacuous_forall() {
        // forall x. true  =>  true (x not free in body)
        let f = Formula::Forall(
            vec![("x".to_string(), Sort::Int)],
            Box::new(Formula::Bool(true)),
        );
        let result = simplify_quantified(&f);
        assert_eq!(result, Formula::Bool(true));
    }

    #[test]
    fn test_simplify_vacuous_exists() {
        // exists x. false  =>  false
        let f = Formula::Exists(
            vec![("x".to_string(), Sort::Int)],
            Box::new(Formula::Bool(false)),
        );
        let result = simplify_quantified(&f);
        assert_eq!(result, Formula::Bool(false));
    }

    #[test]
    fn test_simplify_vacuous_partial() {
        // forall x, y. y > 0  =>  forall y. y > 0  (x is vacuous, y is not)
        let f = Formula::Forall(
            vec![("x".to_string(), Sort::Int), ("y".to_string(), Sort::Int)],
            Box::new(Formula::Gt(
                Box::new(Formula::Var("y".to_string(), Sort::Int)),
                Box::new(Formula::Int(0)),
            )),
        );
        let result = simplify_quantified(&f);
        match &result {
            Formula::Forall(bindings, body) => {
                assert_eq!(bindings.len(), 1);
                assert_eq!(bindings[0].0, "y");
                assert!(matches!(body.as_ref(), Formula::Gt(..)));
            }
            other => panic!("expected Forall with single binding, got: {other:?}"),
        }
    }

    #[test]
    fn test_simplify_merge_nested_forall() {
        // forall x. forall y. x + y > 0  =>  forall x, y. x + y > 0
        let body = Formula::Gt(
            Box::new(Formula::Add(
                Box::new(Formula::Var("x".to_string(), Sort::Int)),
                Box::new(Formula::Var("y".to_string(), Sort::Int)),
            )),
            Box::new(Formula::Int(0)),
        );
        let f = Formula::Forall(
            vec![("x".to_string(), Sort::Int)],
            Box::new(Formula::Forall(
                vec![("y".to_string(), Sort::Int)],
                Box::new(body),
            )),
        );
        let result = simplify_quantified(&f);
        match &result {
            Formula::Forall(bindings, _) => {
                assert_eq!(bindings.len(), 2, "should merge into single forall");
                assert_eq!(bindings[0].0, "x");
                assert_eq!(bindings[1].0, "y");
            }
            other => panic!("expected merged Forall, got: {other:?}"),
        }
    }

    #[test]
    fn test_simplify_merge_nested_exists() {
        // exists x. exists y. x == y  =>  exists x, y. x == y
        let body = Formula::Eq(
            Box::new(Formula::Var("x".to_string(), Sort::Int)),
            Box::new(Formula::Var("y".to_string(), Sort::Int)),
        );
        let f = Formula::Exists(
            vec![("x".to_string(), Sort::Int)],
            Box::new(Formula::Exists(
                vec![("y".to_string(), Sort::Int)],
                Box::new(body),
            )),
        );
        let result = simplify_quantified(&f);
        match &result {
            Formula::Exists(bindings, _) => {
                assert_eq!(bindings.len(), 2, "should merge into single exists");
            }
            other => panic!("expected merged Exists, got: {other:?}"),
        }
    }

    #[test]
    fn test_simplify_no_merge_different_kinds() {
        // forall x. exists y. body — should NOT merge
        let body = Formula::Gt(
            Box::new(Formula::Var("x".to_string(), Sort::Int)),
            Box::new(Formula::Var("y".to_string(), Sort::Int)),
        );
        let f = Formula::Forall(
            vec![("x".to_string(), Sort::Int)],
            Box::new(Formula::Exists(
                vec![("y".to_string(), Sort::Int)],
                Box::new(body),
            )),
        );
        let result = simplify_quantified(&f);
        // Should remain forall x. exists y. ...
        match &result {
            Formula::Forall(outer_bindings, inner) => {
                assert_eq!(outer_bindings.len(), 1);
                assert!(matches!(inner.as_ref(), Formula::Exists(..)));
            }
            other => panic!("expected Forall(Exists), got: {other:?}"),
        }
    }

    #[test]
    fn test_simplify_empty_bindings() {
        // forall(). P => P
        let f = Formula::Forall(
            vec![],
            Box::new(Formula::Bool(true)),
        );
        let result = simplify_quantified(&f);
        assert_eq!(result, Formula::Bool(true));
    }

    #[test]
    fn test_simplify_non_quantified_passthrough() {
        let f = Formula::Gt(
            Box::new(Formula::Var("x".to_string(), Sort::Int)),
            Box::new(Formula::Int(0)),
        );
        let result = simplify_quantified(&f);
        assert_eq!(result, f);
    }

    #[test]
    fn test_simplify_deep_nested_merge() {
        // forall x. forall y. forall z. x + y + z > 0
        // => forall x, y, z. x + y + z > 0
        let body = Formula::Gt(
            Box::new(Formula::Add(
                Box::new(Formula::Add(
                    Box::new(Formula::Var("x".to_string(), Sort::Int)),
                    Box::new(Formula::Var("y".to_string(), Sort::Int)),
                )),
                Box::new(Formula::Var("z".to_string(), Sort::Int)),
            )),
            Box::new(Formula::Int(0)),
        );
        let f = Formula::Forall(
            vec![("x".to_string(), Sort::Int)],
            Box::new(Formula::Forall(
                vec![("y".to_string(), Sort::Int)],
                Box::new(Formula::Forall(
                    vec![("z".to_string(), Sort::Int)],
                    Box::new(body),
                )),
            )),
        );
        let result = simplify_quantified(&f);
        match &result {
            Formula::Forall(bindings, _) => {
                assert_eq!(bindings.len(), 3);
                assert_eq!(bindings[0].0, "x");
                assert_eq!(bindings[1].0, "y");
                assert_eq!(bindings[2].0, "z");
            }
            other => panic!("expected Forall with 3 bindings, got: {other:?}"),
        }
    }

    #[test]
    fn test_simplify_vacuous_plus_merge() {
        // forall unused. forall x. forall y. x + y > 0
        // Step 1: merge inner forall x. forall y => forall x, y
        // Step 2: remove vacuous `unused` => forall x, y
        let body = Formula::Gt(
            Box::new(Formula::Add(
                Box::new(Formula::Var("x".to_string(), Sort::Int)),
                Box::new(Formula::Var("y".to_string(), Sort::Int)),
            )),
            Box::new(Formula::Int(0)),
        );
        let f = Formula::Forall(
            vec![("unused".to_string(), Sort::Int)],
            Box::new(Formula::Forall(
                vec![("x".to_string(), Sort::Int)],
                Box::new(Formula::Forall(
                    vec![("y".to_string(), Sort::Int)],
                    Box::new(body),
                )),
            )),
        );
        let result = simplify_quantified(&f);
        match &result {
            Formula::Forall(bindings, _) => {
                let names: Vec<&str> = bindings.iter().map(|(n, _)| n.as_str()).collect();
                assert!(!names.contains(&"unused"), "vacuous `unused` should be removed");
                assert!(names.contains(&"x"));
                assert!(names.contains(&"y"));
            }
            other => panic!("expected Forall, got: {other:?}"),
        }
    }
}
