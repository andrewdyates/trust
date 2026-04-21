// trust-types/formula_arena/tests.rs: Unit tests for FormulaArena
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use super::*;
use crate::formula::{Formula, Sort};

fn var_f(name: &str) -> Formula {
    Formula::Var(name.into(), Sort::Int)
}

fn bv_var_f(name: &str, w: u32) -> Formula {
    Formula::Var(name.into(), Sort::BitVec(w))
}

#[test]
fn test_intern_and_roundtrip_leaf() {
    let mut arena = FormulaArena::new();
    let cases = vec![
        Formula::Bool(true),
        Formula::Bool(false),
        Formula::Int(42),
        Formula::Int(-1),
        Formula::UInt(100),
        Formula::BitVec { value: 0xff, width: 8 },
        var_f("x"),
        bv_var_f("y", 32),
    ];
    for f in cases {
        let r = arena.intern(&f);
        assert_eq!(arena.to_formula(r), f);
    }
}

#[test]
fn test_intern_and_roundtrip_unary() {
    let mut arena = FormulaArena::new();
    let cases = vec![
        Formula::Not(Box::new(Formula::Bool(true))),
        Formula::Neg(Box::new(Formula::Int(5))),
        Formula::BvNot(Box::new(bv_var_f("a", 32)), 32),
        Formula::BvZeroExt(Box::new(bv_var_f("a", 16)), 16),
        Formula::BvSignExt(Box::new(bv_var_f("a", 16)), 16),
        Formula::IntToBv(Box::new(Formula::Int(7)), 8),
        Formula::BvToInt(Box::new(bv_var_f("a", 32)), 32, true),
        Formula::BvExtract { inner: Box::new(bv_var_f("a", 32)), high: 15, low: 0 },
    ];
    for f in cases {
        let r = arena.intern(&f);
        assert_eq!(arena.to_formula(r), f);
    }
}

#[test]
fn test_intern_and_roundtrip_binary() {
    let mut arena = FormulaArena::new();
    let f = Formula::Add(Box::new(var_f("x")), Box::new(Formula::Int(1)));
    let r = arena.intern(&f);
    assert_eq!(arena.to_formula(r), f);
}

#[test]
fn test_intern_and_roundtrip_binary_with_width() {
    let mut arena = FormulaArena::new();
    let f = Formula::BvAdd(Box::new(bv_var_f("a", 32)), Box::new(bv_var_f("b", 32)), 32);
    let r = arena.intern(&f);
    assert_eq!(arena.to_formula(r), f);
}

#[test]
fn test_intern_and_roundtrip_nary() {
    let mut arena = FormulaArena::new();
    let f = Formula::And(vec![var_f("a"), var_f("b"), var_f("c")]);
    let r = arena.intern(&f);
    assert_eq!(arena.to_formula(r), f);

    let f2 = Formula::Or(vec![Formula::Bool(true), Formula::Bool(false)]);
    let r2 = arena.intern(&f2);
    assert_eq!(arena.to_formula(r2), f2);
}

#[test]
fn test_intern_and_roundtrip_ite() {
    let mut arena = FormulaArena::new();
    let f =
        Formula::Ite(Box::new(Formula::Bool(true)), Box::new(var_f("x")), Box::new(var_f("y")));
    let r = arena.intern(&f);
    assert_eq!(arena.to_formula(r), f);
}

#[test]
fn test_intern_and_roundtrip_quantifier() {
    let mut arena = FormulaArena::new();
    let f = Formula::Forall(
        vec![("x".into(), Sort::Int)],
        Box::new(Formula::Gt(Box::new(var_f("x")), Box::new(Formula::Int(0)))),
    );
    let r = arena.intern(&f);
    assert_eq!(arena.to_formula(r), f);
}

#[test]
fn test_intern_and_roundtrip_store_select() {
    let mut arena = FormulaArena::new();
    let f = Formula::Select(
        Box::new(Formula::Store(
            Box::new(var_f("arr")),
            Box::new(Formula::Int(0)),
            Box::new(Formula::Int(42)),
        )),
        Box::new(Formula::Int(0)),
    );
    let r = arena.intern(&f);
    assert_eq!(arena.to_formula(r), f);
}

#[test]
fn test_intern_and_roundtrip_complex() {
    let mut arena = FormulaArena::new();
    // forall x, y. (x + y > 0) && (bvadd(a, b, 32) != 0)
    let f = Formula::And(vec![
        Formula::Forall(
            vec![("x".into(), Sort::Int), ("y".into(), Sort::Int)],
            Box::new(Formula::Gt(
                Box::new(Formula::Add(Box::new(var_f("x")), Box::new(var_f("y")))),
                Box::new(Formula::Int(0)),
            )),
        ),
        Formula::Not(Box::new(Formula::Eq(
            Box::new(Formula::BvAdd(
                Box::new(bv_var_f("a", 32)),
                Box::new(bv_var_f("b", 32)),
                32,
            )),
            Box::new(Formula::BitVec { value: 0, width: 32 }),
        ))),
    ]);
    let r = arena.intern(&f);
    assert_eq!(arena.to_formula(r), f);
}

#[test]
fn test_arena_children() {
    let mut arena = FormulaArena::new();
    let x = arena.var("x", Sort::Int);
    let one = arena.int(1);
    let add = arena.add(x, one);
    let children = arena.children(add);
    assert_eq!(children.len(), 2);
    assert_eq!(children[0], x);
    assert_eq!(children[1], one);
}

#[test]
fn test_arena_children_leaf() {
    let mut arena = FormulaArena::new();
    let leaf = arena.bool(true);
    assert!(arena.children(leaf).is_empty());
}

#[test]
fn test_arena_children_nary() {
    let mut arena = FormulaArena::new();
    let a = arena.var("a", Sort::Int);
    let b = arena.var("b", Sort::Int);
    let c = arena.var("c", Sort::Int);
    let and = arena.and(&[a, b, c]);
    assert_eq!(arena.children(and).len(), 3);
}

#[test]
fn test_arena_size() {
    let mut arena = FormulaArena::new();
    let f = Formula::And(vec![
        Formula::Not(Box::new(var_f("x"))),
        Formula::Add(Box::new(var_f("y")), Box::new(Formula::Int(1))),
    ]);
    let r = arena.intern(&f);
    // And(Not(Var), Add(Var, Int)) = 6 nodes
    assert_eq!(arena.size(r), 6);
}

#[test]
fn test_arena_depth() {
    let mut arena = FormulaArena::new();
    let leaf = arena.int(42);
    assert_eq!(arena.depth(leaf), 0);

    let f =
        Formula::Not(Box::new(Formula::Add(Box::new(var_f("x")), Box::new(Formula::Int(1)))));
    let r = arena.intern(&f);
    // Not -> Add -> {Var, Int} = depth 2
    assert_eq!(arena.depth(r), 2);
}

#[test]
fn test_arena_visit_counts_all_nodes() {
    let mut arena = FormulaArena::new();
    let f = Formula::And(vec![
        Formula::Not(Box::new(var_f("x"))),
        Formula::Add(Box::new(var_f("y")), Box::new(Formula::Int(1))),
    ]);
    let r = arena.intern(&f);
    let mut count = 0;
    arena.visit(r, &mut |_, _| count += 1);
    assert_eq!(count, 6);
}

#[test]
fn test_arena_builder_api() {
    let mut arena = FormulaArena::new();
    let x = arena.var("x", Sort::Int);
    let one = arena.int(1);
    let sum = arena.add(x, one);
    let zero = arena.int(0);
    let cond = arena.gt(sum, zero);
    let root = arena.not(cond);

    // Roundtrip through Formula
    let owned = arena.to_formula(root);
    let expected = Formula::Not(Box::new(Formula::Gt(
        Box::new(Formula::Add(Box::new(var_f("x")), Box::new(Formula::Int(1)))),
        Box::new(Formula::Int(0)),
    )));
    assert_eq!(owned, expected);
}

#[test]
fn test_arena_len_and_is_empty() {
    let mut arena = FormulaArena::new();
    assert!(arena.is_empty());
    assert_eq!(arena.len(), 0);

    arena.bool(true);
    assert!(!arena.is_empty());
    assert_eq!(arena.len(), 1);

    arena.int(42);
    assert_eq!(arena.len(), 2);
}

#[test]
fn test_arena_with_capacity() {
    let arena = FormulaArena::with_capacity(100, 50);
    assert!(arena.is_empty());
}

#[test]
fn test_arena_default() {
    let arena = FormulaArena::default();
    assert!(arena.is_empty());
}

#[test]
fn test_arena_smtlib() {
    let mut arena = FormulaArena::new();
    let f = Formula::Add(Box::new(var_f("x")), Box::new(Formula::Int(1)));
    let r = arena.intern(&f);
    assert_eq!(arena.to_smtlib(r), "(+ x 1)");
}

#[test]
fn test_arena_multiple_formulas_share_arena() {
    let mut arena = FormulaArena::new();

    let f1 = Formula::Add(Box::new(var_f("x")), Box::new(Formula::Int(1)));
    let r1 = arena.intern(&f1);

    let f2 = Formula::Mul(Box::new(var_f("y")), Box::new(Formula::Int(2)));
    let r2 = arena.intern(&f2);

    // Both formulas live in the same arena
    assert_eq!(arena.to_formula(r1), f1);
    assert_eq!(arena.to_formula(r2), f2);
    // 3 nodes per formula = 6 total
    assert_eq!(arena.len(), 6);
}

#[test]
fn test_arena_all_bv_comparison_variants_roundtrip() {
    let mut arena = FormulaArena::new();
    let a = bv_var_f("a", 32);
    let b = bv_var_f("b", 32);

    let variants = vec![
        Formula::BvULt(Box::new(a.clone()), Box::new(b.clone()), 32),
        Formula::BvULe(Box::new(a.clone()), Box::new(b.clone()), 32),
        Formula::BvSLt(Box::new(a.clone()), Box::new(b.clone()), 32),
        Formula::BvSLe(Box::new(a.clone()), Box::new(b.clone()), 32),
        Formula::BvConcat(Box::new(a.clone()), Box::new(b.clone())),
    ];

    for f in variants {
        let r = arena.intern(&f);
        assert_eq!(arena.to_formula(r), f);
    }
}

#[test]
fn test_arena_all_bv_arithmetic_variants_roundtrip() {
    let mut arena = FormulaArena::new();
    let a = bv_var_f("a", 16);
    let b = bv_var_f("b", 16);

    let variants = vec![
        Formula::BvSub(Box::new(a.clone()), Box::new(b.clone()), 16),
        Formula::BvMul(Box::new(a.clone()), Box::new(b.clone()), 16),
        Formula::BvUDiv(Box::new(a.clone()), Box::new(b.clone()), 16),
        Formula::BvSDiv(Box::new(a.clone()), Box::new(b.clone()), 16),
        Formula::BvURem(Box::new(a.clone()), Box::new(b.clone()), 16),
        Formula::BvSRem(Box::new(a.clone()), Box::new(b.clone()), 16),
        Formula::BvAnd(Box::new(a.clone()), Box::new(b.clone()), 16),
        Formula::BvOr(Box::new(a.clone()), Box::new(b.clone()), 16),
        Formula::BvXor(Box::new(a.clone()), Box::new(b.clone()), 16),
        Formula::BvShl(Box::new(a.clone()), Box::new(b.clone()), 16),
        Formula::BvLShr(Box::new(a.clone()), Box::new(b.clone()), 16),
        Formula::BvAShr(Box::new(a.clone()), Box::new(b.clone()), 16),
    ];

    for f in variants {
        let r = arena.intern(&f);
        assert_eq!(arena.to_formula(r), f);
    }
}

#[test]
fn test_arena_all_comparison_variants_roundtrip() {
    let mut arena = FormulaArena::new();
    let variants = vec![
        Formula::Eq(Box::new(var_f("x")), Box::new(var_f("y"))),
        Formula::Lt(Box::new(var_f("x")), Box::new(var_f("y"))),
        Formula::Le(Box::new(var_f("x")), Box::new(var_f("y"))),
        Formula::Gt(Box::new(var_f("x")), Box::new(var_f("y"))),
        Formula::Ge(Box::new(var_f("x")), Box::new(var_f("y"))),
        Formula::Implies(Box::new(Formula::Bool(true)), Box::new(Formula::Bool(false))),
        Formula::Sub(Box::new(var_f("x")), Box::new(Formula::Int(1))),
        Formula::Mul(Box::new(var_f("x")), Box::new(Formula::Int(2))),
        Formula::Div(Box::new(var_f("x")), Box::new(Formula::Int(3))),
        Formula::Rem(Box::new(var_f("x")), Box::new(Formula::Int(4))),
    ];

    for f in variants {
        let r = arena.intern(&f);
        assert_eq!(arena.to_formula(r), f);
    }
}

#[test]
fn test_arena_exists_roundtrip() {
    let mut arena = FormulaArena::new();
    let f = Formula::Exists(
        vec![("x".into(), Sort::Int)],
        Box::new(Formula::Gt(Box::new(var_f("x")), Box::new(Formula::Int(0)))),
    );
    let r = arena.intern(&f);
    assert_eq!(arena.to_formula(r), f);
}

#[test]
fn test_formula_ref_index() {
    let r = FormulaRef(42);
    assert_eq!(r.index(), 42);
}

// -----------------------------------------------------------------------
// Tests for substitute, map, structural_eq, topological_order
// -----------------------------------------------------------------------

#[test]
fn test_substitute_simple_var_replacement() {
    let mut arena = FormulaArena::new();
    // Build: x + 1
    let x = arena.var("x", Sort::Int);
    let one = arena.int(1);
    let sum = arena.add(x, one);
    // Substitute x -> 42
    let fortytwo = arena.int(42);
    let result = arena.substitute(sum, "x", fortytwo);
    // Should be: 42 + 1
    let f = arena.to_formula(result);
    let expected = Formula::Add(Box::new(Formula::Int(42)), Box::new(Formula::Int(1)));
    assert_eq!(f, expected);
}

#[test]
fn test_substitute_quantifier_shadowing() {
    let mut arena = FormulaArena::new();
    // Build: forall x. (x > 0)  -- x is bound, should NOT be substituted
    let x = arena.var("x", Sort::Int);
    let zero = arena.int(0);
    let gt = arena.gt(x, zero);
    let forall = arena.forall(vec![("x".into(), Sort::Int)], gt);
    // Substitute x -> 99 -- should have no effect (x is bound)
    let ninetynine = arena.int(99);
    let result = arena.substitute(forall, "x", ninetynine);
    assert_eq!(result, forall, "Bound variable should not be substituted");
}

#[test]
fn test_substitute_free_var_inside_quantifier() {
    let mut arena = FormulaArena::new();
    // Build: forall y. (x + y > 0)  -- x is free, y is bound
    let x = arena.var("x", Sort::Int);
    let y = arena.var("y", Sort::Int);
    let sum = arena.add(x, y);
    let zero = arena.int(0);
    let gt = arena.gt(sum, zero);
    let forall = arena.forall(vec![("y".into(), Sort::Int)], gt);
    // Substitute x -> 5
    let five = arena.int(5);
    let result = arena.substitute(forall, "x", five);
    let f = arena.to_formula(result);
    let expected = Formula::Forall(
        vec![("y".into(), Sort::Int)],
        Box::new(Formula::Gt(
            Box::new(Formula::Add(Box::new(Formula::Int(5)), Box::new(var_f("y")))),
            Box::new(Formula::Int(0)),
        )),
    );
    assert_eq!(f, expected);
}

#[test]
fn test_map_negate_all_ints() {
    let mut arena = FormulaArena::new();
    // Build: x + 1
    let x = arena.var("x", Sort::Int);
    let one = arena.int(1);
    let sum = arena.add(x, one);
    // Map: negate all Int literals
    let result = arena.map(sum, &mut |arena, r| {
        if let FormulaNode::Int(v) = arena.get(r) {
            let negated = -(*v);
            arena.int(negated)
        } else {
            r
        }
    });
    let f = arena.to_formula(result);
    let expected = Formula::Add(Box::new(var_f("x")), Box::new(Formula::Int(-1)));
    assert_eq!(f, expected);
}

#[test]
fn test_map_identity_preserves_sharing() {
    let mut arena = FormulaArena::new();
    let x = arena.var("x", Sort::Int);
    let one = arena.int(1);
    let sum = arena.add(x, one);
    // Identity map should return the same ref
    let result = arena.map(sum, &mut |_arena, r| r);
    assert_eq!(result, sum, "Identity map should preserve the original ref");
}

#[test]
fn test_structural_eq_same_structure_different_refs() {
    let mut arena = FormulaArena::new();
    // Build x + 1 twice (different refs, same structure)
    let x1 = arena.var("x", Sort::Int);
    let one1 = arena.int(1);
    let sum1 = arena.add(x1, one1);

    let x2 = arena.var("x", Sort::Int);
    let one2 = arena.int(1);
    let sum2 = arena.add(x2, one2);

    assert_ne!(sum1, sum2, "Different refs");
    assert!(arena.structural_eq(sum1, sum2), "Same structure");
}

#[test]
fn test_structural_eq_different_structure() {
    let mut arena = FormulaArena::new();
    let x = arena.var("x", Sort::Int);
    let one = arena.int(1);
    let two = arena.int(2);
    let sum1 = arena.add(x, one);

    let x2 = arena.var("x", Sort::Int);
    let sum2 = arena.add(x2, two);

    assert!(!arena.structural_eq(sum1, sum2), "Different structure");
}

#[test]
fn test_structural_eq_symmetry() {
    let mut arena = FormulaArena::new();
    let a = arena.var("a", Sort::Int);
    let b = arena.var("a", Sort::Int);
    let one1 = arena.int(1);
    let one2 = arena.int(1);
    let s1 = arena.add(a, one1);
    let s2 = arena.add(b, one2);
    assert!(arena.structural_eq(s1, s2));
    assert!(arena.structural_eq(s2, s1), "structural_eq must be symmetric");
}

#[test]
fn test_topological_order_leaves_before_parents() {
    let mut arena = FormulaArena::new();
    let x = arena.var("x", Sort::Int);
    let one = arena.int(1);
    let sum = arena.add(x, one);
    let order = arena.topological_order(sum);
    // Children (x, 1) must come before parent (x+1)
    assert_eq!(order.len(), 3);
    let pos_x = order.iter().position(|r| *r == x).expect("x in order");
    let pos_one = order.iter().position(|r| *r == one).expect("1 in order");
    let pos_sum = order.iter().position(|r| *r == sum).expect("sum in order");
    assert!(pos_x < pos_sum, "x must come before sum");
    assert!(pos_one < pos_sum, "1 must come before sum");
}

#[test]
fn test_topological_order_deduplicates_shared_nodes() {
    let mut arena = FormulaArena::new();
    // Build x + x (sharing x)
    let x = arena.var("x", Sort::Int);
    let sum = arena.add(x, x);
    let order = arena.topological_order(sum);
    // x appears once, sum appears once = 2 entries
    assert_eq!(order.len(), 2);
    assert_eq!(order[0], x);
    assert_eq!(order[1], sum);
}

#[test]
fn test_topological_order_complex_dag() {
    let mut arena = FormulaArena::new();
    // Build: (x + 1) > (x + 1), sharing the same x+1 ref
    let x = arena.var("x", Sort::Int);
    let one = arena.int(1);
    let sum = arena.add(x, one);
    let gt = arena.gt(sum, sum); // both children are the same ref
    let order = arena.topological_order(gt);
    // x, 1, sum, gt = 4 unique nodes
    assert_eq!(order.len(), 4);
    // gt must be last
    assert_eq!(*order.last().expect("non-empty"), gt);
}

#[test]
fn test_arena_allocation_benchmark() {
    // Build a moderately large formula (100 nodes) and verify arena
    // allocates them contiguously.
    let mut arena = FormulaArena::new();
    let mut refs = Vec::new();
    for i in 0..50 {
        let v = arena.var(format!("x{i}"), Sort::Int);
        let lit = arena.int(i as i128);
        let node = arena.add(v, lit);
        refs.push(node);
    }
    // 50 * 3 = 150 nodes
    assert_eq!(arena.len(), 150);

    // All refs are sequential
    for (i, r) in refs.iter().enumerate() {
        // Each group is (var, int, add) at indices 3*i, 3*i+1, 3*i+2
        assert_eq!(r.index(), 3 * i + 2);
    }
}
