// trust-cegar: Tests for spurious counterexample refinement
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{AssertMessage, BlockId, ConstValue, CounterexampleValue, Operand, SourceSpan, Terminator};
use trust_types::{BasicBlock, Counterexample, Formula};

use crate::interpolation::UnsatCore;
use crate::predicate::{AbstractState, CmpOp, Predicate};

use super::checker::{CexCheckResult, CounterexampleChecker};
use super::helpers::{
    build_cex_path_formula, cex_contradicts_predicate, cex_lookup_int, cex_value_to_formula,
    collect_core_labels, is_trivially_unsat,
};
use super::inner_loop::{InnerLoopConfig, InnerLoopOutcome, SpuriousRefinementLoop};
use super::refinement::{interpolant_refine, predicate_refine, rust_semantic_refine, trace_refine};
use super::strategy::InnerRefinementStrategy;

fn make_cex(assignments: Vec<(&str, CounterexampleValue)>) -> Counterexample {
    Counterexample::new(
        assignments
            .into_iter()
            .map(|(n, v)| (n.to_string(), v))
            .collect(),
    )
}

fn span() -> SourceSpan {
    SourceSpan::default()
}

fn simple_blocks() -> Vec<BasicBlock> {
    vec![
        BasicBlock {
            id: BlockId(0),
            stmts: vec![],
            terminator: Terminator::Goto(BlockId(1)),
        },
        BasicBlock {
            id: BlockId(1),
            stmts: vec![],
            terminator: Terminator::Return,
        },
    ]
}

fn blocks_with_false_assert() -> Vec<BasicBlock> {
    vec![BasicBlock {
        id: BlockId(0),
        stmts: vec![],
        terminator: Terminator::Assert {
            cond: Operand::Constant(ConstValue::Bool(false)),
            expected: true,
            msg: AssertMessage::BoundsCheck,
            target: BlockId(1),
            span: span(),
        },
    }]
}

// -----------------------------------------------------------------------
// InnerRefinementStrategy tests
// -----------------------------------------------------------------------

#[test]
fn test_inner_refinement_strategy_display() {
    assert_eq!(
        format!("{}", InnerRefinementStrategy::PredicateRefinement),
        "predicate"
    );
    assert_eq!(
        format!("{}", InnerRefinementStrategy::TraceRefinement),
        "trace"
    );
    assert_eq!(
        format!("{}", InnerRefinementStrategy::InterpolantBased),
        "interpolant"
    );
}

#[test]
fn test_inner_refinement_strategy_equality() {
    assert_eq!(
        InnerRefinementStrategy::PredicateRefinement,
        InnerRefinementStrategy::PredicateRefinement
    );
    assert_ne!(
        InnerRefinementStrategy::PredicateRefinement,
        InnerRefinementStrategy::TraceRefinement
    );
}

// -----------------------------------------------------------------------
// CounterexampleChecker tests
// -----------------------------------------------------------------------

#[test]
fn test_checker_unknown_with_no_abstract_states() {
    // No abstract states and no trivially-unsat path formula:
    // syntactic analysis is inconclusive, so result is Unknown.
    let checker = CounterexampleChecker::new(vec![]);
    let cex = make_cex(vec![("x", CounterexampleValue::Int(5))]);
    let result = checker.check(&cex, &simple_blocks());
    assert!(matches!(result, CexCheckResult::Unknown));
}

#[test]
fn test_checker_spurious_via_predicate_contradiction() {
    let mut state = AbstractState::top();
    state.add(Predicate::comparison("x", CmpOp::Ge, "0"));
    let checker = CounterexampleChecker::new(vec![state]);

    // x = -1 contradicts x >= 0
    let cex = make_cex(vec![("x", CounterexampleValue::Int(-1))]);
    let result = checker.check(&cex, &simple_blocks());
    assert!(matches!(result, CexCheckResult::Spurious { .. }));
}

#[test]
fn test_checker_spurious_via_path_formula() {
    let checker = CounterexampleChecker::new(vec![]);
    let cex = make_cex(vec![("x", CounterexampleValue::Int(5))]);
    let result = checker.check(&cex, &blocks_with_false_assert());
    assert!(matches!(result, CexCheckResult::Spurious { .. }));
}

#[test]
fn test_checker_unknown_with_consistent_state() {
    let mut state = AbstractState::top();
    state.add(Predicate::comparison("x", CmpOp::Ge, "0"));
    let checker = CounterexampleChecker::new(vec![state]);

    // x = 5 is consistent with x >= 0, but without an SMT solver
    // we cannot confirm feasibility -- result is Unknown.
    let cex = make_cex(vec![("x", CounterexampleValue::Int(5))]);
    let result = checker.check(&cex, &simple_blocks());
    assert!(matches!(result, CexCheckResult::Unknown));
}

#[test]
fn test_checker_update_states() {
    let mut checker = CounterexampleChecker::new(vec![]);
    let cex = make_cex(vec![("x", CounterexampleValue::Int(-1))]);

    // Initially unknown (no predicates to contradict, no SMT solver).
    assert!(matches!(
        checker.check(&cex, &simple_blocks()),
        CexCheckResult::Unknown
    ));

    // After update, spurious.
    let mut state = AbstractState::top();
    state.add(Predicate::comparison("x", CmpOp::Ge, "0"));
    checker.update_states(vec![state]);
    assert!(matches!(
        checker.check(&cex, &simple_blocks()),
        CexCheckResult::Spurious { .. }
    ));
}

#[test]
fn test_checker_range_predicate_contradiction() {
    let mut state = AbstractState::top();
    state.add(Predicate::range("idx", 0, 100));
    let checker = CounterexampleChecker::new(vec![state]);

    // idx = 200 contradicts 0 <= idx <= 100
    let cex = make_cex(vec![("idx", CounterexampleValue::Int(200))]);
    let result = checker.check(&cex, &simple_blocks());
    assert!(matches!(result, CexCheckResult::Spurious { .. }));
}

#[test]
fn test_checker_spurious_provides_split_formulas() {
    let mut state = AbstractState::top();
    state.add(Predicate::comparison("x", CmpOp::Ge, "0"));
    let checker = CounterexampleChecker::new(vec![state]);

    let cex = make_cex(vec![("x", CounterexampleValue::Int(-1))]);
    let result = checker.check(&cex, &simple_blocks());

    if let CexCheckResult::Spurious { path_a, path_b, .. } = result {
        // Should have some formulas in the split.
        assert!(
            !path_a.is_empty() || !path_b.is_empty(),
            "split formulas should not both be empty"
        );
    } else {
        panic!("expected Spurious result");
    }
}

// -----------------------------------------------------------------------
// Predicate refinement tests
// -----------------------------------------------------------------------

#[test]
fn test_predicate_refine_int_values() {
    let cex = make_cex(vec![("x", CounterexampleValue::Int(-5))]);
    let preds = predicate_refine(&cex, &[]);
    let pred_strs: Vec<String> = preds.iter().map(ToString::to_string).collect();
    assert!(pred_strs.contains(&"x >= 0".to_string()));
    assert!(pred_strs.contains(&"x < 0".to_string()));
    assert!(pred_strs.contains(&"x == -5".to_string()));
}

#[test]
fn test_predicate_refine_uint_values() {
    let cex = make_cex(vec![("n", CounterexampleValue::Uint(0))]);
    let preds = predicate_refine(&cex, &[]);
    let pred_strs: Vec<String> = preds.iter().map(ToString::to_string).collect();
    assert!(pred_strs.contains(&"n == 0".to_string()));
}

#[test]
fn test_predicate_refine_bool_values() {
    let cex = make_cex(vec![("flag", CounterexampleValue::Bool(true))]);
    let preds = predicate_refine(&cex, &[]);
    let pred_strs: Vec<String> = preds.iter().map(ToString::to_string).collect();
    assert!(pred_strs.contains(&"flag == 1".to_string()));
}

#[test]
fn test_predicate_refine_pairwise_comparisons() {
    let cex = make_cex(vec![
        ("a", CounterexampleValue::Int(1)),
        ("b", CounterexampleValue::Int(10)),
    ]);
    let preds = predicate_refine(&cex, &[]);
    let pred_strs: Vec<String> = preds.iter().map(ToString::to_string).collect();
    assert!(pred_strs.contains(&"a < b".to_string()));
}

#[test]
fn test_predicate_refine_skips_existing() {
    let existing = vec![Predicate::comparison("x", CmpOp::Ge, "0")];
    let cex = make_cex(vec![("x", CounterexampleValue::Int(5))]);
    let preds = predicate_refine(&cex, &existing);
    assert!(!preds.contains(&Predicate::comparison("x", CmpOp::Ge, "0")));
}

// -----------------------------------------------------------------------
// Trace refinement tests
// -----------------------------------------------------------------------

#[test]
fn test_trace_refine_produces_predicates() {
    let cex = make_cex(vec![
        ("x", CounterexampleValue::Int(3)),
        ("y", CounterexampleValue::Int(7)),
    ]);
    let preds = trace_refine(&cex, &[]);
    assert!(!preds.is_empty());
    let pred_strs: Vec<String> = preds.iter().map(ToString::to_string).collect();
    // Should have ordering between consecutive trace variables.
    assert!(pred_strs.contains(&"x < y".to_string()));
}

#[test]
fn test_trace_refine_negative_value() {
    let cex = make_cex(vec![("x", CounterexampleValue::Int(-10))]);
    let preds = trace_refine(&cex, &[]);
    let pred_strs: Vec<String> = preds.iter().map(ToString::to_string).collect();
    assert!(pred_strs.contains(&"x < 0".to_string()));
    assert!(pred_strs.contains(&"x == -10".to_string()));
}

#[test]
fn test_trace_refine_skips_existing() {
    let existing = vec![Predicate::comparison("x", CmpOp::Eq, "5")];
    let cex = make_cex(vec![("x", CounterexampleValue::Int(5))]);
    let preds = trace_refine(&cex, &existing);
    assert!(!preds.contains(&Predicate::comparison("x", CmpOp::Eq, "5")));
}

// -----------------------------------------------------------------------
// Interpolant-based refinement tests
// -----------------------------------------------------------------------

#[test]
fn test_interpolant_refine_with_core() {
    let cex = make_cex(vec![("x", CounterexampleValue::Int(-1))]);
    let path_a = vec![(
        "a0".to_string(),
        Formula::Lt(
            Box::new(Formula::Var("x".into(), trust_types::Sort::Int)),
            Box::new(Formula::Int(10)),
        ),
    )];
    let path_b = vec![(
        "b0".to_string(),
        Formula::Ge(
            Box::new(Formula::Var("x".into(), trust_types::Sort::Int)),
            Box::new(Formula::Int(20)),
        ),
    )];
    let core = UnsatCore::new(vec!["a0".into(), "b0".into()]);

    let preds = interpolant_refine(&cex, &path_a, &path_b, &core, &[])
        .expect("should not error");
    assert!(!preds.is_empty());
    assert!(preds.contains(&Predicate::comparison("x", CmpOp::Lt, "10")));
}

#[test]
fn test_interpolant_refine_fallback_to_predicate() {
    let cex = make_cex(vec![("x", CounterexampleValue::Int(-5))]);
    // Empty paths and core -> falls back to predicate refinement.
    let preds =
        interpolant_refine(&cex, &[], &[], &UnsatCore::default(), &[])
            .expect("should not error");
    assert!(!preds.is_empty());
}

// -----------------------------------------------------------------------
// Inner loop tests
// -----------------------------------------------------------------------

#[test]
fn test_inner_loop_unknown_without_smt() {
    // No abstract states to contradict, no false asserts ->
    // syntactic analysis inconclusive, result is Unknown (not
    // RealCounterexample, which would cause a false alarm).
    let config = InnerLoopConfig {
        strategy: InnerRefinementStrategy::PredicateRefinement,
        ..InnerLoopConfig::default()
    };
    let mut loop_ = SpuriousRefinementLoop::new(vec![], config);
    let cex = make_cex(vec![("x", CounterexampleValue::Int(5))]);

    let outcome = loop_
        .process_counterexample(&cex, &simple_blocks())
        .expect("should not error");
    assert!(matches!(outcome, InnerLoopOutcome::Unknown));
    assert_eq!(loop_.stats().counterexamples_checked, 1);
}

#[test]
fn test_inner_loop_spurious_refined() {
    // Blocks with assert(false) make every CEX spurious.
    let config = InnerLoopConfig {
        strategy: InnerRefinementStrategy::PredicateRefinement,
        ..InnerLoopConfig::default()
    };
    let mut loop_ = SpuriousRefinementLoop::new(vec![], config);
    let cex = make_cex(vec![("x", CounterexampleValue::Int(5))]);

    let outcome = loop_
        .process_counterexample(&cex, &blocks_with_false_assert())
        .expect("should not error");

    match outcome {
        InnerLoopOutcome::Refined {
            new_predicates,
            inner_iterations,
            strategy_used,
        } => {
            assert!(!new_predicates.is_empty());
            assert!(inner_iterations >= 1);
            assert_eq!(strategy_used, InnerRefinementStrategy::PredicateRefinement);
        }
        other => panic!("expected Refined, got: {other:?}"),
    }
    assert_eq!(loop_.stats().spurious_count, 1);
}

#[test]
fn test_inner_loop_trace_refinement_strategy() {
    let config = InnerLoopConfig {
        strategy: InnerRefinementStrategy::TraceRefinement,
        ..InnerLoopConfig::default()
    };
    let mut loop_ = SpuriousRefinementLoop::new(vec![], config);
    let cex = make_cex(vec![
        ("x", CounterexampleValue::Int(3)),
        ("y", CounterexampleValue::Int(-7)),
    ]);

    let outcome = loop_
        .process_counterexample(&cex, &blocks_with_false_assert())
        .expect("should not error");

    match outcome {
        InnerLoopOutcome::Refined { strategy_used, .. } => {
            assert_eq!(strategy_used, InnerRefinementStrategy::TraceRefinement);
        }
        other => panic!("expected Refined, got: {other:?}"),
    }
}

#[test]
fn test_inner_loop_interpolant_strategy() {
    let config = InnerLoopConfig {
        strategy: InnerRefinementStrategy::InterpolantBased,
        ..InnerLoopConfig::default()
    };
    let mut loop_ = SpuriousRefinementLoop::new(vec![], config);
    let cex = make_cex(vec![("x", CounterexampleValue::Int(42))]);

    let outcome = loop_
        .process_counterexample(&cex, &blocks_with_false_assert())
        .expect("should not error");

    match outcome {
        InnerLoopOutcome::Refined { strategy_used, .. } => {
            assert_eq!(strategy_used, InnerRefinementStrategy::InterpolantBased);
        }
        other => panic!("expected Refined, got: {other:?}"),
    }
}

#[test]
fn test_inner_loop_max_predicates_limit() {
    let config = InnerLoopConfig {
        max_predicates: 2,
        ..InnerLoopConfig::default()
    };
    // Start with 2 predicates (already at limit).
    let initial = vec![
        Predicate::comparison("a", CmpOp::Ge, "0"),
        Predicate::comparison("b", CmpOp::Lt, "100"),
    ];
    let mut loop_ = SpuriousRefinementLoop::new(initial, config);
    let cex = make_cex(vec![("x", CounterexampleValue::Int(-1))]);

    // Blocks with assert(false) trigger spurious, but max_predicates
    // prevents further refinement.
    let outcome = loop_
        .process_counterexample(&cex, &blocks_with_false_assert())
        .expect("should not error");

    assert!(matches!(
        outcome,
        InnerLoopOutcome::InnerLimitExhausted { reason, .. }
            if reason == "max_predicates"
    ));
}

#[test]
fn test_inner_loop_config_default() {
    let config = InnerLoopConfig::default();
    assert_eq!(config.max_inner_iterations, 20);
    assert_eq!(config.strategy, InnerRefinementStrategy::InterpolantBased);
    assert!(config.detect_fixed_point);
    assert_eq!(config.max_predicates, 500);
}

#[test]
fn test_inner_loop_stats_accumulate() {
    let config = InnerLoopConfig::default();
    let mut loop_ = SpuriousRefinementLoop::new(vec![], config);

    // Process an unknown counterexample (no abstract states, no false asserts).
    let cex1 = make_cex(vec![("x", CounterexampleValue::Int(5))]);
    let _ = loop_.process_counterexample(&cex1, &simple_blocks());

    // Process a spurious counterexample.
    let cex2 = make_cex(vec![("y", CounterexampleValue::Int(10))]);
    let _ = loop_.process_counterexample(&cex2, &blocks_with_false_assert());

    assert_eq!(loop_.stats().counterexamples_checked, 2);
    // First CEX is Unknown (not feasible), so feasible_count stays 0.
    assert_eq!(loop_.stats().feasible_count, 0);
}

#[test]
fn test_inner_loop_predicates_grow() {
    let config = InnerLoopConfig {
        strategy: InnerRefinementStrategy::PredicateRefinement,
        ..InnerLoopConfig::default()
    };
    let mut loop_ = SpuriousRefinementLoop::new(vec![], config);

    let cex = make_cex(vec![("x", CounterexampleValue::Int(-5))]);
    let _ = loop_.process_counterexample(&cex, &blocks_with_false_assert());

    assert!(
        !loop_.predicates().is_empty(),
        "predicates should grow after refinement"
    );
}

// -----------------------------------------------------------------------
// Helper function tests
// -----------------------------------------------------------------------

#[test]
fn test_cex_contradicts_comparison() {
    let pred = Predicate::comparison("x", CmpOp::Ge, "0");
    let cex = make_cex(vec![("x", CounterexampleValue::Int(-1))]);
    assert!(cex_contradicts_predicate(&cex, &pred));

    let cex_ok = make_cex(vec![("x", CounterexampleValue::Int(5))]);
    assert!(!cex_contradicts_predicate(&cex_ok, &pred));
}

#[test]
fn test_cex_contradicts_range() {
    let pred = Predicate::range("idx", 0, 100);
    let cex = make_cex(vec![("idx", CounterexampleValue::Int(200))]);
    assert!(cex_contradicts_predicate(&cex, &pred));

    let cex_ok = make_cex(vec![("idx", CounterexampleValue::Int(50))]);
    assert!(!cex_contradicts_predicate(&cex_ok, &pred));
}

#[test]
fn test_cex_lookup_int_variable() {
    let cex = make_cex(vec![("x", CounterexampleValue::Int(42))]);
    assert_eq!(cex_lookup_int(&cex, "x"), Some(42));
    assert_eq!(cex_lookup_int(&cex, "y"), None);
}

#[test]
fn test_cex_lookup_int_literal() {
    let cex = make_cex(vec![]);
    assert_eq!(cex_lookup_int(&cex, "42"), Some(42));
    assert_eq!(cex_lookup_int(&cex, "-5"), Some(-5));
    assert_eq!(cex_lookup_int(&cex, "not_a_number"), None);
}

#[test]
fn test_cex_lookup_uint() {
    let cex = make_cex(vec![("n", CounterexampleValue::Uint(100))]);
    assert_eq!(cex_lookup_int(&cex, "n"), Some(100));
}

#[test]
fn test_cex_lookup_bool() {
    let cex = make_cex(vec![("flag", CounterexampleValue::Bool(true))]);
    assert_eq!(cex_lookup_int(&cex, "flag"), Some(1));
}

#[test]
fn test_is_trivially_unsat_false() {
    assert!(is_trivially_unsat(&Formula::Bool(false)));
}

#[test]
fn test_is_trivially_unsat_not_true() {
    assert!(is_trivially_unsat(&Formula::Not(Box::new(Formula::Bool(true)))));
}

#[test]
fn test_is_trivially_unsat_and_with_false() {
    let f = Formula::And(vec![
        Formula::Bool(true),
        Formula::Bool(false),
    ]);
    assert!(is_trivially_unsat(&f));
}

#[test]
fn test_is_trivially_unsat_contradiction() {
    let p = Formula::Var("x".into(), trust_types::Sort::Bool);
    let not_p = Formula::Not(Box::new(p.clone()));
    let f = Formula::And(vec![p, not_p]);
    assert!(is_trivially_unsat(&f));
}

#[test]
fn test_is_trivially_unsat_sat_formula() {
    assert!(!is_trivially_unsat(&Formula::Bool(true)));
    assert!(!is_trivially_unsat(&Formula::And(vec![
        Formula::Bool(true),
        Formula::Bool(true),
    ])));
}

#[test]
fn test_build_cex_path_formula_assignments() {
    let cex = make_cex(vec![
        ("x", CounterexampleValue::Int(42)),
        ("flag", CounterexampleValue::Bool(true)),
    ]);
    let formula = build_cex_path_formula(&cex, &[]);
    match &formula {
        Formula::And(conjuncts) => assert_eq!(conjuncts.len(), 2),
        _ => panic!("expected And formula"),
    }
}

#[test]
fn test_build_cex_path_formula_with_block_constraint() {
    let cex = make_cex(vec![("x", CounterexampleValue::Int(0))]);
    let formula = build_cex_path_formula(&cex, &blocks_with_false_assert());
    match &formula {
        Formula::And(conjuncts) => {
            assert!(conjuncts.contains(&Formula::Bool(false)));
        }
        _ => panic!("expected And formula"),
    }
}

#[test]
fn test_build_cex_path_formula_empty() {
    let cex = Counterexample::new(vec![]);
    let formula = build_cex_path_formula(&cex, &[]);
    assert_eq!(formula, Formula::Bool(true));
}

#[test]
fn test_cex_value_to_formula_int() {
    let f = cex_value_to_formula("x", &CounterexampleValue::Int(42));
    assert!(f.is_some());
}

#[test]
fn test_cex_value_to_formula_bool() {
    let f = cex_value_to_formula("flag", &CounterexampleValue::Bool(true));
    assert!(f.is_some());
}

#[test]
fn test_cex_value_to_formula_float_none() {
    let f = cex_value_to_formula("f", &CounterexampleValue::Float(3.125));
    assert!(f.is_none());
}

#[test]
fn test_inner_loop_outcome_debug() {
    let real = InnerLoopOutcome::RealCounterexample;
    assert!(format!("{real:?}").contains("RealCounterexample"));

    let unknown = InnerLoopOutcome::Unknown;
    assert!(format!("{unknown:?}").contains("Unknown"));

    let refined = InnerLoopOutcome::Refined {
        new_predicates: vec![],
        inner_iterations: 1,
        strategy_used: InnerRefinementStrategy::PredicateRefinement,
    };
    assert!(format!("{refined:?}").contains("Refined"));

    let fp = InnerLoopOutcome::FixedPoint { iterations: 3 };
    assert!(format!("{fp:?}").contains("FixedPoint"));

    let limit = InnerLoopOutcome::InnerLimitExhausted {
        reason: "max_inner_iterations".into(),
        iterations: 20,
    };
    assert!(format!("{limit:?}").contains("InnerLimitExhausted"));
}

#[test]
fn test_collect_core_labels() {
    let path_a = vec![("a0".to_string(), Formula::Bool(true))];
    let path_b = vec![("b0".to_string(), Formula::Bool(false))];
    let labels = collect_core_labels(&path_a, &path_b);
    assert_eq!(labels, vec!["a0".to_string(), "b0".to_string()]);
}

// -----------------------------------------------------------------------
// RustSemanticRefinement strategy tests
// -----------------------------------------------------------------------

#[test]
fn test_rust_semantic_strategy_display() {
    assert_eq!(
        format!("{}", InnerRefinementStrategy::RustSemanticRefinement),
        "rust-semantic"
    );
}

#[test]
fn test_rust_semantic_refine_no_domain_falls_back() {
    // No Rust domain: should fall back to generic predicate refinement.
    let cex = make_cex(vec![("x", CounterexampleValue::Int(-5))]);
    let preds = rust_semantic_refine(&cex, &[], None).expect("should not error");
    assert!(!preds.is_empty());
    // Should contain boundary predicates from fallback.
    let pred_strs: Vec<String> = preds.iter().map(ToString::to_string).collect();
    assert!(pred_strs.contains(&"x >= 0".to_string()));
}

#[test]
fn test_rust_semantic_refine_moved_variable() {
    use crate::rust_abstraction::OwnershipState;

    let mut domain = crate::rust_abstraction::RustAbstractionDomain::new();
    domain.ownership.set_state("x", OwnershipState::Moved);

    let cex = make_cex(vec![("x", CounterexampleValue::Int(42))]);
    let preds = rust_semantic_refine(&cex, &[], Some(&domain))
        .expect("should not error");
    assert!(preds.contains(&Predicate::Custom("x:moved".into())));
}

#[test]
fn test_rust_semantic_refine_type_violation() {
    let mut domain = crate::rust_abstraction::RustAbstractionDomain::new();
    domain.type_info.add_integer_range("x", 0, 255);

    let cex = make_cex(vec![("x", CounterexampleValue::Int(300))]);
    let preds = rust_semantic_refine(&cex, &[], Some(&domain))
        .expect("should not error");
    assert!(preds.contains(&Predicate::range("x", 0, 255)));
}

#[test]
fn test_rust_semantic_refine_non_null_violation() {
    let mut domain = crate::rust_abstraction::RustAbstractionDomain::new();
    domain.type_info.add_non_null_ref("ptr");

    // ptr = 0 violates non-null.
    let cex = make_cex(vec![("ptr", CounterexampleValue::Int(0))]);
    let preds = rust_semantic_refine(&cex, &[], Some(&domain))
        .expect("should not error");
    assert!(preds.contains(&Predicate::NonNull("ptr".into())));
}

#[test]
fn test_rust_semantic_refine_interval_violation() {
    let mut domain = crate::rust_abstraction::RustAbstractionDomain::new();
    domain.intervals.set_interval("x", 0, 100);

    // x = 200 is outside the interval.
    let cex = make_cex(vec![("x", CounterexampleValue::Int(200))]);
    let preds = rust_semantic_refine(&cex, &[], Some(&domain))
        .expect("should not error");
    assert!(preds.contains(&Predicate::range("x", 0, 100)));
}

#[test]
fn test_rust_semantic_refine_borrow_check_violation() {
    use crate::rust_abstraction::{BorrowCheckPredicate, OwnershipState};

    let mut domain = crate::rust_abstraction::RustAbstractionDomain::new();
    domain.ownership.set_state("x", OwnershipState::MutableBorrow);
    domain.ownership.set_state("y", OwnershipState::SharedBorrow);
    domain.add_borrow_check(BorrowCheckPredicate::NoMutWhileShared {
        place: "x".into(),
    });

    let cex = make_cex(vec![("z", CounterexampleValue::Int(0))]);
    let preds = rust_semantic_refine(&cex, &[], Some(&domain))
        .expect("should not error");
    assert!(preds.contains(&Predicate::Custom("x:no_mut_while_shared".into())));
}

#[test]
fn test_rust_semantic_refine_ownership_blocking_predicate() {
    use crate::rust_abstraction::OwnershipPredicate;

    let mut domain = crate::rust_abstraction::RustAbstractionDomain::new();
    domain.add_ownership_predicate(OwnershipPredicate::IsMoved("val".into()));

    let cex = make_cex(vec![("other", CounterexampleValue::Int(0))]);
    let preds = rust_semantic_refine(&cex, &[], Some(&domain))
        .expect("should not error");
    // The moved predicate should appear as a seed predicate.
    assert!(preds.contains(&Predicate::Custom("val:moved".into())));
}

#[test]
fn test_rust_semantic_refine_seeds_domain_predicates() {
    let mut domain = crate::rust_abstraction::RustAbstractionDomain::new();
    domain.type_info.add_integer_range("n", 0, 100);
    domain.type_info.add_non_null_ref("ptr");

    // CEX with unrelated variable, but domain predicates should be seeded.
    let cex = make_cex(vec![("other", CounterexampleValue::Int(5))]);
    let preds = rust_semantic_refine(&cex, &[], Some(&domain))
        .expect("should not error");
    assert!(preds.contains(&Predicate::range("n", 0, 100)));
    assert!(preds.contains(&Predicate::NonNull("ptr".into())));
}

#[test]
fn test_rust_semantic_refine_skips_existing() {
    let mut domain = crate::rust_abstraction::RustAbstractionDomain::new();
    domain.type_info.add_integer_range("x", 0, 255);

    let existing = vec![Predicate::range("x", 0, 255)];
    let cex = make_cex(vec![("x", CounterexampleValue::Int(300))]);
    let preds = rust_semantic_refine(&cex, &existing, Some(&domain))
        .expect("should not error");
    // Range predicate is already in existing: should not be re-added.
    assert!(!preds.contains(&Predicate::range("x", 0, 255)));
}

#[test]
fn test_rust_semantic_refine_uint_values() {
    let mut domain = crate::rust_abstraction::RustAbstractionDomain::new();
    domain.type_info.add_integer_range("n", 0, 65535);

    let cex = make_cex(vec![("n", CounterexampleValue::Uint(70000))]);
    let preds = rust_semantic_refine(&cex, &[], Some(&domain))
        .expect("should not error");
    assert!(preds.contains(&Predicate::range("n", 0, 65535)));
}

#[test]
fn test_rust_semantic_refine_bool_values() {
    let mut domain = crate::rust_abstraction::RustAbstractionDomain::new();
    domain.ownership.set_state("flag", crate::rust_abstraction::OwnershipState::Moved);

    let cex = make_cex(vec![("flag", CounterexampleValue::Bool(true))]);
    let preds = rust_semantic_refine(&cex, &[], Some(&domain))
        .expect("should not error");
    assert!(preds.contains(&Predicate::Custom("flag:moved".into())));
}

// -----------------------------------------------------------------------
// Inner loop with Rust domain tests
// -----------------------------------------------------------------------

#[test]
fn test_inner_loop_with_rust_domain_constructor() {
    let domain = crate::rust_abstraction::RustAbstractionDomain::new();
    let config = InnerLoopConfig {
        strategy: InnerRefinementStrategy::RustSemanticRefinement,
        ..InnerLoopConfig::default()
    };
    let loop_ = SpuriousRefinementLoop::with_rust_domain(
        vec![],
        config,
        domain.clone(),
    );
    assert!(loop_.rust_domain().is_some());
}

#[test]
fn test_inner_loop_set_rust_domain() {
    let config = InnerLoopConfig::default();
    let mut loop_ = SpuriousRefinementLoop::new(vec![], config);
    assert!(loop_.rust_domain().is_none());

    let domain = crate::rust_abstraction::RustAbstractionDomain::new();
    loop_.set_rust_domain(domain);
    assert!(loop_.rust_domain().is_some());
}

#[test]
fn test_inner_loop_rust_semantic_strategy_spurious() {
    let mut domain = crate::rust_abstraction::RustAbstractionDomain::new();
    domain.type_info.add_integer_range("x", 0, 255);

    let config = InnerLoopConfig {
        strategy: InnerRefinementStrategy::RustSemanticRefinement,
        ..InnerLoopConfig::default()
    };
    let mut loop_ = SpuriousRefinementLoop::with_rust_domain(
        vec![],
        config,
        domain,
    );

    // Blocks with assert(false) make every CEX spurious.
    let cex = make_cex(vec![("x", CounterexampleValue::Int(42))]);
    let outcome = loop_
        .process_counterexample(&cex, &blocks_with_false_assert())
        .expect("should not error");

    match outcome {
        InnerLoopOutcome::Refined { strategy_used, new_predicates, .. } => {
            assert_eq!(strategy_used, InnerRefinementStrategy::RustSemanticRefinement);
            assert!(!new_predicates.is_empty());
        }
        other => panic!("expected Refined, got: {other:?}"),
    }
}

#[test]
fn test_inner_loop_rust_semantic_strategy_unknown() {
    // No domain constraints, no false asserts -> Unknown (not
    // RealCounterexample, since syntactic analysis is inconclusive).
    let domain = crate::rust_abstraction::RustAbstractionDomain::new();
    let config = InnerLoopConfig {
        strategy: InnerRefinementStrategy::RustSemanticRefinement,
        ..InnerLoopConfig::default()
    };
    let mut loop_ = SpuriousRefinementLoop::with_rust_domain(
        vec![],
        config,
        domain,
    );

    let cex = make_cex(vec![("x", CounterexampleValue::Int(5))]);
    let outcome = loop_
        .process_counterexample(&cex, &simple_blocks())
        .expect("should not error");
    assert!(matches!(outcome, InnerLoopOutcome::Unknown));
}

#[test]
fn test_inner_loop_rust_semantic_no_domain_falls_back() {
    // RustSemanticRefinement without a domain should fall back to predicate refinement.
    let config = InnerLoopConfig {
        strategy: InnerRefinementStrategy::RustSemanticRefinement,
        ..InnerLoopConfig::default()
    };
    let mut loop_ = SpuriousRefinementLoop::new(vec![], config);

    let cex = make_cex(vec![("x", CounterexampleValue::Int(42))]);
    let outcome = loop_
        .process_counterexample(&cex, &blocks_with_false_assert())
        .expect("should not error");

    match outcome {
        InnerLoopOutcome::Refined { strategy_used, new_predicates, .. } => {
            assert_eq!(strategy_used, InnerRefinementStrategy::RustSemanticRefinement);
            assert!(!new_predicates.is_empty());
        }
        other => panic!("expected Refined, got: {other:?}"),
    }
}

#[test]
fn test_inner_loop_rust_semantic_with_discriminant() {
    let mut domain = crate::rust_abstraction::RustAbstractionDomain::new();
    domain.type_info.add_enum_discriminants("opt", [0, 1]); // Option: None=0, Some=1

    let config = InnerLoopConfig {
        strategy: InnerRefinementStrategy::RustSemanticRefinement,
        ..InnerLoopConfig::default()
    };
    let mut loop_ = SpuriousRefinementLoop::with_rust_domain(
        vec![],
        config,
        domain,
    );

    let cex = make_cex(vec![("opt", CounterexampleValue::Int(5))]);
    let outcome = loop_
        .process_counterexample(&cex, &blocks_with_false_assert())
        .expect("should not error");

    match outcome {
        InnerLoopOutcome::Refined { new_predicates, .. } => {
            // Should contain discriminant range predicate.
            assert!(new_predicates.contains(&Predicate::range("opt", 0, 1)));
        }
        other => panic!("expected Refined, got: {other:?}"),
    }
}

// -----------------------------------------------------------------------
// CEX feasibility: trivially feasible, trivially spurious, unknown (#773)
// -----------------------------------------------------------------------

#[test]
fn test_cex_trivially_spurious_via_predicate() {
    // Predicate x >= 0 contradicts x = -1: trivially spurious,
    // no SMT solver needed.
    let mut state = AbstractState::top();
    state.add(Predicate::comparison("x", CmpOp::Ge, "0"));
    let checker = CounterexampleChecker::new(vec![state]);

    let cex = make_cex(vec![("x", CounterexampleValue::Int(-1))]);
    let result = checker.check(&cex, &simple_blocks());
    assert!(matches!(result, CexCheckResult::Spurious { infeasibility_point: 0, .. }));
}

#[test]
fn test_cex_trivially_spurious_via_path_unsat() {
    // Path formula contains assert(false): trivially unsat.
    let checker = CounterexampleChecker::new(vec![]);
    let cex = make_cex(vec![("x", CounterexampleValue::Int(0))]);
    let result = checker.check(&cex, &blocks_with_false_assert());
    assert!(matches!(result, CexCheckResult::Spurious { .. }));
}

#[test]
fn test_cex_unknown_no_contradiction_no_unsat() {
    // No abstract state contradiction, no trivially-unsat path formula.
    // Syntactic analysis is inconclusive -> Unknown (not Feasible).
    let checker = CounterexampleChecker::new(vec![]);
    let cex = make_cex(vec![
        ("x", CounterexampleValue::Int(5)),
        ("y", CounterexampleValue::Int(10)),
    ]);
    let result = checker.check(&cex, &simple_blocks());
    assert!(
        matches!(result, CexCheckResult::Unknown),
        "inconclusive syntactic analysis must return Unknown, not Feasible"
    );
}

#[test]
fn test_cex_unknown_with_nontrivial_assert() {
    // Block with assert(local_0), where local_0 is unconstrained:
    // not trivially unsat, so the checker should return Unknown.
    let blocks = vec![BasicBlock {
        id: BlockId(0),
        stmts: vec![],
        terminator: Terminator::Assert {
            cond: Operand::Copy(trust_types::Place {
                local: 0,
                projections: vec![],
            }),
            expected: true,
            msg: AssertMessage::BoundsCheck,
            target: BlockId(1),
            span: span(),
        },
    }];
    let checker = CounterexampleChecker::new(vec![]);
    let cex = make_cex(vec![("x", CounterexampleValue::Int(1))]);
    let result = checker.check(&cex, &blocks);
    assert!(
        matches!(result, CexCheckResult::Unknown),
        "non-trivial assert should yield Unknown without SMT solver"
    );
}

#[test]
fn test_inner_loop_unknown_does_not_increment_feasible_count() {
    // Unknown CEXes should not be counted as feasible.
    let config = InnerLoopConfig::default();
    let mut loop_ = SpuriousRefinementLoop::new(vec![], config);

    let cex = make_cex(vec![("x", CounterexampleValue::Int(42))]);
    let outcome = loop_
        .process_counterexample(&cex, &simple_blocks())
        .expect("should not error");
    assert!(matches!(outcome, InnerLoopOutcome::Unknown));
    assert_eq!(loop_.stats().feasible_count, 0, "Unknown must not be counted as feasible");
}
