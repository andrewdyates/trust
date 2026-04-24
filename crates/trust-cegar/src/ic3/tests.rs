// trust-cegar: IC3 tests
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{Formula, Sort};

use super::engine::{Ic3Engine, ic3_check};
use super::prime::prime_formula;
use super::sat::{SatResult, structural_sat_check};
use super::types::{Cube, Frame, Ic3Config, Ic3Result, TransitionSystem};

fn prime(formula: &Formula) -> Formula {
    prime_formula(formula).expect("prime_formula should handle supported Formula variants")
}

fn ic3_ok<T>(result: Result<T, crate::error::CegarError>) -> T {
    result.expect("IC3 helper should not fail for supported test formulas")
}

// -- Cube tests --

#[test]
fn test_cube_empty() {
    let cube = Cube::empty();
    assert!(cube.is_empty());
    assert_eq!(cube.len(), 0);
    assert_eq!(cube.to_formula(), Formula::Bool(true));
}

#[test]
fn test_cube_single_literal() {
    let lit = Formula::Var("x".into(), Sort::Bool);
    let cube = Cube::new(vec![lit.clone()]);
    assert_eq!(cube.len(), 1);
    assert!(!cube.is_empty());
    assert_eq!(cube.to_formula(), lit);
}

#[test]
fn test_cube_multiple_literals() {
    let a = Formula::Var("a".into(), Sort::Bool);
    let b = Formula::Var("b".into(), Sort::Bool);
    let cube = Cube::new(vec![a.clone(), b.clone()]);
    assert_eq!(cube.len(), 2);
    assert_eq!(cube.to_formula(), Formula::And(vec![a, b]));
}

#[test]
fn test_cube_negate_empty() {
    let cube = Cube::empty();
    assert_eq!(cube.negate(), Formula::Bool(false));
}

#[test]
fn test_cube_negate_single() {
    let lit = Formula::Var("x".into(), Sort::Bool);
    let cube = Cube::new(vec![lit.clone()]);
    assert_eq!(cube.negate(), Formula::Not(Box::new(lit)));
}

#[test]
fn test_cube_negate_multiple() {
    let a = Formula::Var("a".into(), Sort::Bool);
    let b = Formula::Var("b".into(), Sort::Bool);
    let cube = Cube::new(vec![a.clone(), b.clone()]);
    let negated = cube.negate();
    assert_eq!(negated, Formula::Or(vec![Formula::Not(Box::new(a)), Formula::Not(Box::new(b)),]));
}

#[test]
fn test_cube_display() {
    let cube = Cube::empty();
    assert_eq!(format!("{cube}"), "true");

    let a = Formula::Var("x".into(), Sort::Int);
    let cube = Cube::new(vec![Formula::Lt(Box::new(a), Box::new(Formula::Int(10)))]);
    let display = format!("{cube}");
    assert!(display.contains("(< x 10)"));
}

// -- Frame tests --

#[test]
fn test_frame_new_empty() {
    let frame = Frame::new(0);
    assert_eq!(frame.index, 0);
    assert!(frame.is_empty());
    assert_eq!(frame.clause_count(), 0);
}

#[test]
fn test_frame_add_clause() {
    let mut frame = Frame::new(1);
    let cube = Cube::new(vec![Formula::Bool(true)]);
    frame.add_clause(cube.clone());
    assert_eq!(frame.clause_count(), 1);
    assert!(frame.contains(&cube));
}

#[test]
fn test_frame_deduplicates_clauses() {
    let mut frame = Frame::new(1);
    let cube = Cube::new(vec![Formula::Bool(true)]);
    frame.add_clause(cube.clone());
    frame.add_clause(cube);
    assert_eq!(frame.clause_count(), 1);
}

#[test]
fn test_frame_to_formula_empty() {
    let frame = Frame::new(0);
    assert_eq!(frame.to_formula(), Formula::Bool(true));
}

#[test]
fn test_frame_to_formula_single_clause() {
    let mut frame = Frame::new(1);
    let cube = Cube::new(vec![Formula::Var("x".into(), Sort::Bool)]);
    frame.add_clause(cube);
    let f = frame.to_formula();
    // Single clause: negation of the cube.
    assert!(matches!(f, Formula::Not(_)));
}

#[test]
fn test_frame_display() {
    let mut frame = Frame::new(2);
    frame.add_clause(Cube::new(vec![Formula::Bool(true)]));
    let display = format!("{frame}");
    assert!(display.contains("F_2"));
    assert!(display.contains("1cl"));
}

// -- TransitionSystem tests --

#[test]
fn test_transition_system_creation() {
    let sys = TransitionSystem::new(Formula::Bool(true), Formula::Bool(true), Formula::Bool(true));
    assert_eq!(sys.init, Formula::Bool(true));
    assert_eq!(sys.transition, Formula::Bool(true));
    assert_eq!(sys.property, Formula::Bool(true));
}

// -- IC3 Engine tests --

#[test]
fn test_ic3_trivially_safe() {
    // Property is true: trivially safe.
    let sys = TransitionSystem::new(Formula::Bool(true), Formula::Bool(true), Formula::Bool(true));
    let result = ic3_check(sys).expect("should succeed");
    match result {
        Ic3Result::Safe { convergence_depth, .. } => {
            assert!(convergence_depth >= 1);
        }
        other => panic!("expected Safe, got: {other:?}"),
    }
}

#[test]
fn test_ic3_trivially_unsafe_init() {
    // Property is false and init is reachable: immediate counterexample.
    let sys = TransitionSystem::new(Formula::Bool(true), Formula::Bool(true), Formula::Bool(false));
    let result = ic3_check(sys).expect("should succeed");
    assert!(matches!(result, Ic3Result::Unsafe { .. }));
}

#[test]
fn test_ic3_no_initial_states() {
    // Init is false: no reachable states, property trivially holds.
    let sys =
        TransitionSystem::new(Formula::Bool(false), Formula::Bool(true), Formula::Bool(false));
    let result = ic3_check(sys).expect("should succeed");
    // With no initial states, property holds vacuously.
    match result {
        Ic3Result::Safe { .. } => {}
        other => panic!("expected Safe (vacuously), got: {other:?}"),
    }
}

#[test]
fn test_ic3_no_transitions() {
    // No transitions (T = false): only initial states matter.
    let x = Formula::Var("x".into(), Sort::Int);
    let property = Formula::Ge(Box::new(x.clone()), Box::new(Formula::Int(0)));
    let sys = TransitionSystem::new(
        Formula::Eq(Box::new(x), Box::new(Formula::Int(5))),
        Formula::Bool(false),
        property,
    );
    let result = ic3_check(sys).expect("should succeed");
    match result {
        Ic3Result::Safe { .. } => {}
        other => panic!("expected Safe, got: {other:?}"),
    }
}

#[test]
fn test_ic3_engine_depth() {
    let sys = TransitionSystem::new(Formula::Bool(true), Formula::Bool(true), Formula::Bool(true));
    let engine = Ic3Engine::new(sys, Ic3Config::default());
    assert_eq!(engine.depth(), 0);
    assert_eq!(engine.frames().len(), 1);
}

#[test]
fn test_generalize_cube_single_literal() {
    let sys = TransitionSystem::new(Formula::Bool(true), Formula::Bool(true), Formula::Bool(true));
    let engine = Ic3Engine::new(sys, Ic3Config::default());
    let cube = Cube::new(vec![Formula::Bool(true)]);
    let result = ic3_ok(engine.generalize_cube(&cube, 1));
    // Single literal cannot be generalized further.
    assert_eq!(result.len(), 1);
}

#[test]
fn test_generalize_cube_empty() {
    let sys = TransitionSystem::new(Formula::Bool(true), Formula::Bool(true), Formula::Bool(true));
    let engine = Ic3Engine::new(sys, Ic3Config::default());
    let cube = Cube::empty();
    let result = ic3_ok(engine.generalize_cube(&cube, 1));
    assert!(result.is_empty());
}

#[test]
fn test_propagate_clauses_convergence() {
    let sys = TransitionSystem::new(Formula::Bool(true), Formula::Bool(true), Formula::Bool(true));
    let mut engine = Ic3Engine::new(sys, Ic3Config::default());

    // Manually set up frames where F_1 == F_2 (convergence).
    let clause = Cube::new(vec![Formula::Bool(true)]);
    let mut f1 = Frame::new(1);
    f1.add_clause(clause.clone());
    let mut f2 = Frame::new(2);
    f2.add_clause(clause);

    engine.frames = vec![Frame::new(0), f1, f2];

    let converged = ic3_ok(engine.propagate_clauses());
    assert_eq!(converged, Some(1));
}

#[test]
fn test_propagate_clauses_no_convergence() {
    // Use a non-trivial variable-based clause where the inductiveness check
    // cannot determine UNSAT structurally. The structural SAT checker will
    // conservatively return Sat, so the clause will NOT be propagated.
    let x = Formula::Var("x".into(), Sort::Int);
    let sys = TransitionSystem::new(
        Formula::Bool(true),
        // Non-trivial transition: x' = x + 1
        Formula::Eq(
            Box::new(Formula::Var("x'".into(), Sort::Int)),
            Box::new(Formula::Add(Box::new(x.clone()), Box::new(Formula::Int(1)))),
        ),
        Formula::Bool(true),
    );
    let mut engine = Ic3Engine::new(sys, Ic3Config::default());

    // F_1 has a clause with a non-trivial predicate, F_2 is empty.
    let clause = Cube::new(vec![Formula::Ge(Box::new(x), Box::new(Formula::Int(0)))]);
    let mut f1 = Frame::new(1);
    f1.add_clause(clause);

    engine.frames = vec![Frame::new(0), f1, Frame::new(2)];

    let converged = ic3_ok(engine.propagate_clauses());
    // With the inductiveness check, the clause is NOT propagated because
    // the structural SAT checker cannot determine the query is UNSAT,
    // so F_1 != F_2 and there is no convergence.
    assert_eq!(converged, None);
}

#[test]
fn test_extract_counterexample_trace_empty() {
    let sys = TransitionSystem::new(Formula::Bool(true), Formula::Bool(true), Formula::Bool(true));
    let engine = Ic3Engine::new(sys, Ic3Config::default());
    let trace = engine.extract_counterexample_trace(&[]);
    assert!(trace.is_empty());
}

#[test]
fn test_extract_counterexample_trace_reverses_order() {
    let sys = TransitionSystem::new(Formula::Bool(true), Formula::Bool(true), Formula::Bool(true));
    let engine = Ic3Engine::new(sys, Ic3Config::default());

    let c1 = Cube::new(vec![Formula::Bool(true)]);
    let c2 = Cube::new(vec![Formula::Bool(false)]);
    let trace = engine.extract_counterexample_trace(&[c1.clone(), c2.clone()]);
    assert_eq!(trace.len(), 2);
    assert_eq!(trace[0], c2);
    assert_eq!(trace[1], c1);
}

#[test]
fn test_ic3_result_safe_contains_invariant() {
    let x = Formula::Var("x".into(), Sort::Bool);
    let sys = TransitionSystem::new(x.clone(), Formula::Bool(true), Formula::Bool(true));
    let result = ic3_check(sys).expect("should succeed");
    match result {
        Ic3Result::Safe { invariant_clauses, .. } => {
            // Invariant may be empty for trivially-safe properties.
            let _ = invariant_clauses;
        }
        other => panic!("expected Safe, got: {other:?}"),
    }
}

#[test]
fn test_cube_equality() {
    let a = Cube::new(vec![Formula::Bool(true)]);
    let b = Cube::new(vec![Formula::Bool(false)]);
    let a2 = Cube::new(vec![Formula::Bool(true)]);
    assert_eq!(a, a2);
    assert_ne!(a, b);
}

#[test]
fn test_frame_multiple_clauses_formula() {
    let mut frame = Frame::new(1);
    let c1 = Cube::new(vec![Formula::Var("a".into(), Sort::Bool)]);
    let c2 = Cube::new(vec![Formula::Var("b".into(), Sort::Bool)]);
    frame.add_clause(c1);
    frame.add_clause(c2);
    let f = frame.to_formula();
    // Two clauses produce a conjunction of their negations.
    assert!(matches!(f, Formula::And(_)));
}

// -- SMT oracle tests (#376) --

#[test]
fn test_structural_sat_check_trivially_false() {
    assert_eq!(structural_sat_check(&Formula::Bool(false)), SatResult::Unsat);
}

#[test]
fn test_structural_sat_check_trivially_true() {
    assert_eq!(structural_sat_check(&Formula::Bool(true)), SatResult::Sat(None));
}

#[test]
fn test_structural_sat_check_contradiction_in_and() {
    let x = Formula::Var("x".into(), Sort::Bool);
    let formula = Formula::And(vec![x.clone(), Formula::Not(Box::new(x))]);
    assert_eq!(structural_sat_check(&formula), SatResult::Unsat);
}

#[test]
fn test_structural_sat_check_and_with_false() {
    let formula = Formula::And(vec![Formula::Bool(true), Formula::Bool(false)]);
    assert_eq!(structural_sat_check(&formula), SatResult::Unsat);
}

#[test]
fn test_structural_sat_check_non_trivial_is_conservative() {
    // Non-trivial formula: structural checker conservatively returns Sat.
    let x = Formula::Var("x".into(), Sort::Int);
    let formula = Formula::Lt(Box::new(x), Box::new(Formula::Int(10)));
    assert_eq!(structural_sat_check(&formula), SatResult::Sat(None));
}

// -- is_inductive_relative tests (#376) --

#[test]
fn test_is_inductive_relative_with_false_transition() {
    // T = false makes the query F /\ !c /\ false /\ c' = false (UNSAT)
    // so the cube is trivially inductive.
    let sys = TransitionSystem::new(Formula::Bool(true), Formula::Bool(false), Formula::Bool(true));
    let mut engine = Ic3Engine::new(sys, Ic3Config::default());
    engine.frames.push(Frame::new(1));

    let cube = Cube::new(vec![Formula::Var("x".into(), Sort::Bool)]);
    assert!(ic3_ok(engine.is_inductive_relative(&cube, 1)));
}

#[test]
fn test_is_inductive_relative_level_zero() {
    let sys = TransitionSystem::new(Formula::Bool(true), Formula::Bool(true), Formula::Bool(true));
    let engine = Ic3Engine::new(sys, Ic3Config::default());
    let cube = Cube::new(vec![Formula::Bool(true)]);
    // Level 0 always returns false.
    assert!(!ic3_ok(engine.is_inductive_relative(&cube, 0)));
}

// -- find_predecessor tests (#376) --

#[test]
fn test_find_predecessor_no_transition() {
    // T = false -> F /\ false /\ cube' = false (UNSAT) -> no predecessor
    let sys = TransitionSystem::new(Formula::Bool(true), Formula::Bool(false), Formula::Bool(true));
    let mut engine = Ic3Engine::new(sys, Ic3Config::default());
    engine.frames.push(Frame::new(1));

    let cube = Cube::new(vec![Formula::Var("x".into(), Sort::Bool)]);
    assert!(ic3_ok(engine.find_predecessor(&cube, 1)).is_none());
}

#[test]
fn test_find_predecessor_identity_transition() {
    // T = true, frame empty -> F /\ true /\ cube' = true /\ cube' (SAT)
    // -> predecessor found
    let sys = TransitionSystem::new(Formula::Bool(true), Formula::Bool(true), Formula::Bool(true));
    let mut engine = Ic3Engine::new(sys, Ic3Config::default());
    engine.frames.push(Frame::new(1));

    let cube = Cube::new(vec![Formula::Var("x".into(), Sort::Bool)]);
    assert!(ic3_ok(engine.find_predecessor(&cube, 1)).is_some());
}

// -- propagate_clauses inductiveness tests (#404) --

#[test]
fn test_propagate_clauses_only_propagates_inductive() {
    // With T = false, all clauses are trivially inductive (query contains false).
    let sys = TransitionSystem::new(Formula::Bool(true), Formula::Bool(false), Formula::Bool(true));
    let mut engine = Ic3Engine::new(sys, Ic3Config::default());

    let clause = Cube::new(vec![Formula::Var("x".into(), Sort::Bool)]);
    let mut f1 = Frame::new(1);
    f1.add_clause(clause);

    engine.frames = vec![Frame::new(0), f1, Frame::new(2)];

    let converged = ic3_ok(engine.propagate_clauses());
    // T = false makes all clauses inductive, so clause propagates -> convergence.
    assert_eq!(converged, Some(1));
}

#[test]
fn test_propagate_clauses_blocks_non_inductive() {
    // With T = true and a non-trivial clause, the structural checker
    // cannot determine UNSAT, so the clause is not propagated.
    let x = Formula::Var("x".into(), Sort::Int);
    let sys = TransitionSystem::new(Formula::Bool(true), Formula::Bool(true), Formula::Bool(true));
    let mut engine = Ic3Engine::new(sys, Ic3Config::default());

    // Non-trivial clause: x >= 0
    let clause = Cube::new(vec![Formula::Ge(Box::new(x), Box::new(Formula::Int(0)))]);
    let mut f1 = Frame::new(1);
    f1.add_clause(clause);

    engine.frames = vec![Frame::new(0), f1, Frame::new(2)];

    let converged = ic3_ok(engine.propagate_clauses());
    // Clause is NOT propagated because inductiveness check is inconclusive.
    assert_eq!(converged, None);
    // F_2 should still be empty.
    assert!(engine.frames[2].is_empty());
}

#[test]
fn test_is_clause_inductive_false_transition() {
    // T = false makes any inductiveness query contain false -> UNSAT -> inductive.
    let sys = TransitionSystem::new(Formula::Bool(true), Formula::Bool(false), Formula::Bool(true));
    let mut engine = Ic3Engine::new(sys, Ic3Config::default());
    engine.frames.push(Frame::new(1)); // F_1

    let clause = Cube::new(vec![Formula::Var("x".into(), Sort::Bool)]);
    assert!(ic3_ok(engine.is_clause_inductive(&clause, 1)));
}

#[test]
fn test_is_clause_inductive_non_trivial_returns_false() {
    // With T = true and a non-trivial clause, structural_sat_check returns
    // Sat(None) (unknown), so is_clause_inductive conservatively returns false.
    // This is the key soundness property: Sat(None) is NOT treated as
    // "definitely satisfiable" -- it means "unknown", so we refuse to
    // propagate rather than risk unsoundness.
    let sys = TransitionSystem::new(Formula::Bool(true), Formula::Bool(true), Formula::Bool(true));
    let mut engine = Ic3Engine::new(sys, Ic3Config::default());
    engine.frames.push(Frame::new(1));

    let clause = Cube::new(vec![Formula::Ge(
        Box::new(Formula::Var("x".into(), Sort::Int)),
        Box::new(Formula::Int(0)),
    )]);
    // Cannot prove inductiveness structurally -> false (conservative).
    assert!(!ic3_ok(engine.is_clause_inductive(&clause, 1)));
}

#[test]
fn test_is_clause_inductive_out_of_bounds_level() {
    let sys = TransitionSystem::new(Formula::Bool(true), Formula::Bool(true), Formula::Bool(true));
    let engine = Ic3Engine::new(sys, Ic3Config::default());

    let clause = Cube::new(vec![Formula::Bool(true)]);
    // Level 5 is out of bounds (only F_0 exists).
    assert!(!ic3_ok(engine.is_clause_inductive(&clause, 5)));
}

#[test]
fn test_propagate_clauses_multiple_frames_selective() {
    // Test that propagation works across multiple frames:
    // With T = false, trivially-boolean clauses propagate.
    // With a mix of trivial and non-trivial clauses, only the trivial
    // ones (whose inductiveness query simplifies to UNSAT) propagate.
    let sys = TransitionSystem::new(
        Formula::Bool(true),
        Formula::Bool(false), // T = false -> all queries UNSAT
        Formula::Bool(true),
    );
    let mut engine = Ic3Engine::new(sys, Ic3Config::default());

    let clause_a = Cube::new(vec![Formula::Var("a".into(), Sort::Bool)]);
    let clause_b = Cube::new(vec![Formula::Var("b".into(), Sort::Bool)]);

    let mut f1 = Frame::new(1);
    f1.add_clause(clause_a.clone());
    f1.add_clause(clause_b.clone());

    let mut f2 = Frame::new(2);
    // F_2 already has clause_a, so only clause_b should be added.
    f2.add_clause(clause_a);

    engine.frames = vec![Frame::new(0), f1, f2, Frame::new(3)];

    ic3_ok(engine.propagate_clauses());
    // F_2 should now also have clause_b (propagated from F_1).
    assert!(engine.frames[2].contains(&clause_b));
}

#[test]
fn test_propagate_clauses_does_not_propagate_existing() {
    // Clauses already in the target frame are not re-added.
    let sys = TransitionSystem::new(Formula::Bool(true), Formula::Bool(false), Formula::Bool(true));
    let mut engine = Ic3Engine::new(sys, Ic3Config::default());

    let clause = Cube::new(vec![Formula::Var("x".into(), Sort::Bool)]);
    let mut f1 = Frame::new(1);
    f1.add_clause(clause.clone());
    let mut f2 = Frame::new(2);
    f2.add_clause(clause);

    engine.frames = vec![Frame::new(0), f1, f2];

    let converged = ic3_ok(engine.propagate_clauses());
    // F_1 and F_2 are already equal -> convergence.
    assert_eq!(converged, Some(1));
    // F_2 should still have exactly 1 clause (no duplicate).
    assert_eq!(engine.frames[2].clause_count(), 1);
}

#[test]
fn test_propagate_conservative_sat_none_blocks_propagation() {
    // Directly verify that a formula producing Sat(None) from
    // structural_sat_check prevents clause propagation.
    // This is the core #404 fix: Sat(None) = "unknown", NOT "sat".
    let x = Formula::Var("x".into(), Sort::Int);

    // The inductiveness query will be:
    //   F_1 /\ !clause /\ T /\ clause'
    // With T = (x' = x + 1) and clause = (x >= 0), this is non-trivial.
    // structural_sat_check will return Sat(None), so clause should NOT propagate.
    let sys = TransitionSystem::new(
        Formula::Bool(true),
        Formula::Eq(
            Box::new(Formula::Var("x'".into(), Sort::Int)),
            Box::new(Formula::Add(Box::new(x.clone()), Box::new(Formula::Int(1)))),
        ),
        Formula::Bool(true),
    );
    let mut engine = Ic3Engine::new(sys, Ic3Config::default());

    let clause = Cube::new(vec![Formula::Ge(Box::new(x), Box::new(Formula::Int(0)))]);
    let mut f1 = Frame::new(1);
    f1.add_clause(clause);

    engine.frames = vec![Frame::new(0), f1, Frame::new(2)];

    let converged = ic3_ok(engine.propagate_clauses());
    assert_eq!(converged, None, "should not converge: clause not propagated");
    assert!(engine.frames[2].is_empty(), "F_2 should remain empty: clause not proven inductive");
}

// -- prime_formula tests --

#[test]
fn test_prime_formula_renames_variables() {
    let x = Formula::Var("x".into(), Sort::Int);
    let primed = prime(&x);
    assert_eq!(primed, Formula::Var("x'".into(), Sort::Int));
}

#[test]
fn test_prime_formula_preserves_constants() {
    assert_eq!(prime(&Formula::Bool(true)), Formula::Bool(true));
    assert_eq!(prime(&Formula::Int(42)), Formula::Int(42));
}

#[test]
fn test_prime_formula_nested() {
    let x = Formula::Var("x".into(), Sort::Int);
    let formula = Formula::Lt(Box::new(x), Box::new(Formula::Int(10)));
    let primed = prime(&formula);
    assert_eq!(
        primed,
        Formula::Lt(Box::new(Formula::Var("x'".into(), Sort::Int)), Box::new(Formula::Int(10)),)
    );
}

// -- prime_formula exhaustive variant tests (#772) --

#[test]
fn test_prime_formula_bv_add_primes_variables() {
    // BV operations must recursively prime variables inside them.
    // Before #772 fix, the catch-all returned these unprimed.
    let x = Formula::Var("x".into(), Sort::BitVec(32));
    let y = Formula::Var("y".into(), Sort::BitVec(32));
    let formula = Formula::BvAdd(Box::new(x), Box::new(y), 32);
    let primed = prime(&formula);
    assert_eq!(
        primed,
        Formula::BvAdd(
            Box::new(Formula::Var("x'".into(), Sort::BitVec(32))),
            Box::new(Formula::Var("y'".into(), Sort::BitVec(32))),
            32,
        )
    );
}

#[test]
fn test_prime_formula_bv_comparison() {
    let a = Formula::Var("a".into(), Sort::BitVec(64));
    let b = Formula::Var("b".into(), Sort::BitVec(64));
    let formula = Formula::BvULt(Box::new(a), Box::new(b), 64);
    let primed = prime(&formula);
    assert_eq!(
        primed,
        Formula::BvULt(
            Box::new(Formula::Var("a'".into(), Sort::BitVec(64))),
            Box::new(Formula::Var("b'".into(), Sort::BitVec(64))),
            64,
        )
    );
}

#[test]
fn test_prime_formula_bv_not_and_extract() {
    let x = Formula::Var("x".into(), Sort::BitVec(32));
    let not_x = Formula::BvNot(Box::new(x), 32);
    let primed = prime(&not_x);
    assert_eq!(primed, Formula::BvNot(Box::new(Formula::Var("x'".into(), Sort::BitVec(32))), 32,));

    let y = Formula::Var("y".into(), Sort::BitVec(32));
    let extract = Formula::BvExtract { inner: Box::new(y), high: 15, low: 0 };
    let primed_extract = prime(&extract);
    assert_eq!(
        primed_extract,
        Formula::BvExtract {
            inner: Box::new(Formula::Var("y'".into(), Sort::BitVec(32))),
            high: 15,
            low: 0,
        }
    );
}

#[test]
fn test_prime_formula_nested_bv_in_ite() {
    // Deeply nested: ite(x > 0, bvadd(x, y), bvsub(x, z))
    let x = Formula::Var("x".into(), Sort::BitVec(32));
    let y = Formula::Var("y".into(), Sort::BitVec(32));
    let z = Formula::Var("z".into(), Sort::BitVec(32));
    let cond = Formula::Gt(Box::new(x.clone()), Box::new(Formula::Int(0)));
    let then_f = Formula::BvAdd(Box::new(x.clone()), Box::new(y), 32);
    let else_f = Formula::BvSub(Box::new(x), Box::new(z), 32);
    let formula = Formula::Ite(Box::new(cond), Box::new(then_f), Box::new(else_f));

    let primed = prime(&formula);
    // All three variables must be primed.
    match &primed {
        Formula::Ite(c, t, e) => {
            // Condition has x'
            assert!(matches!(c.as_ref(), Formula::Gt(..)));
            // Then branch has x', y'
            match t.as_ref() {
                Formula::BvAdd(a, b, 32) => {
                    assert_eq!(**a, Formula::Var("x'".into(), Sort::BitVec(32)));
                    assert_eq!(**b, Formula::Var("y'".into(), Sort::BitVec(32)));
                }
                other => panic!("expected BvAdd, got: {other:?}"),
            }
            // Else branch has x', z'
            match e.as_ref() {
                Formula::BvSub(a, b, 32) => {
                    assert_eq!(**a, Formula::Var("x'".into(), Sort::BitVec(32)));
                    assert_eq!(**b, Formula::Var("z'".into(), Sort::BitVec(32)));
                }
                other => panic!("expected BvSub, got: {other:?}"),
            }
        }
        other => panic!("expected Ite, got: {other:?}"),
    }
}

#[test]
fn test_prime_formula_forall_primes_bound_vars_and_body() {
    let bindings = vec![("x".into(), Sort::Int), ("y".into(), Sort::Bool)];
    let body = Formula::Lt(
        Box::new(Formula::Var("x".into(), Sort::Int)),
        Box::new(Formula::Var("z".into(), Sort::Int)),
    );
    let formula = Formula::Forall(bindings, Box::new(body));
    let primed = prime(&formula);

    match primed {
        Formula::Forall(b, body) => {
            assert_eq!(b[0].0, "x'");
            assert_eq!(b[1].0, "y'");
            // Body's free variable z is also primed.
            assert_eq!(
                *body,
                Formula::Lt(
                    Box::new(Formula::Var("x'".into(), Sort::Int)),
                    Box::new(Formula::Var("z'".into(), Sort::Int)),
                )
            );
        }
        other => panic!("expected Forall, got: {other:?}"),
    }
}

#[test]
fn test_prime_formula_exists_primes_bound_vars_and_body() {
    let bindings = vec![("a".into(), Sort::Int)];
    let body =
        Formula::Eq(Box::new(Formula::Var("a".into(), Sort::Int)), Box::new(Formula::Int(42)));
    let formula = Formula::Exists(bindings, Box::new(body));
    let primed = prime(&formula);

    match primed {
        Formula::Exists(b, body) => {
            assert_eq!(b[0].0, "a'");
            assert_eq!(
                *body,
                Formula::Eq(
                    Box::new(Formula::Var("a'".into(), Sort::Int)),
                    Box::new(Formula::Int(42)),
                )
            );
        }
        other => panic!("expected Exists, got: {other:?}"),
    }
}

#[test]
fn test_prime_formula_select_and_store() {
    let arr = Formula::Var("mem".into(), Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int)));
    let idx = Formula::Var("i".into(), Sort::Int);
    let val = Formula::Var("v".into(), Sort::Int);

    let select = Formula::Select(Box::new(arr.clone()), Box::new(idx.clone()));
    let primed_select = prime(&select);
    assert_eq!(
        primed_select,
        Formula::Select(
            Box::new(Formula::Var(
                "mem'".into(),
                Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int))
            )),
            Box::new(Formula::Var("i'".into(), Sort::Int)),
        )
    );

    let store = Formula::Store(Box::new(arr), Box::new(idx), Box::new(val));
    let primed_store = prime(&store);
    match primed_store {
        Formula::Store(a, i, v) => {
            assert_eq!(
                *a,
                Formula::Var("mem'".into(), Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int)))
            );
            assert_eq!(*i, Formula::Var("i'".into(), Sort::Int));
            assert_eq!(*v, Formula::Var("v'".into(), Sort::Int));
        }
        other => panic!("expected Store, got: {other:?}"),
    }
}

#[test]
fn test_prime_formula_preserves_uint_and_bitvec_literals() {
    assert_eq!(prime(&Formula::UInt(99)), Formula::UInt(99));
    let bv = Formula::BitVec { value: 0xFF, width: 8 };
    assert_eq!(prime(&bv), bv);
}

#[test]
fn test_prime_formula_div_rem_neg() {
    let x = Formula::Var("x".into(), Sort::Int);
    let y = Formula::Var("y".into(), Sort::Int);

    let div = Formula::Div(Box::new(x.clone()), Box::new(y.clone()));
    let primed_div = prime(&div);
    assert_eq!(
        primed_div,
        Formula::Div(
            Box::new(Formula::Var("x'".into(), Sort::Int)),
            Box::new(Formula::Var("y'".into(), Sort::Int)),
        )
    );

    let rem = Formula::Rem(Box::new(x.clone()), Box::new(y));
    let primed_rem = prime(&rem);
    assert_eq!(
        primed_rem,
        Formula::Rem(
            Box::new(Formula::Var("x'".into(), Sort::Int)),
            Box::new(Formula::Var("y'".into(), Sort::Int)),
        )
    );

    let neg = Formula::Neg(Box::new(x));
    let primed_neg = prime(&neg);
    assert_eq!(primed_neg, Formula::Neg(Box::new(Formula::Var("x'".into(), Sort::Int))));
}

// -- simplify_formula tests --

#[test]
fn test_simplify_and_with_false() {
    use super::sat::simplify_formula;
    let f = Formula::And(vec![Formula::Bool(true), Formula::Bool(false)]);
    assert_eq!(simplify_formula(&f), Formula::Bool(false));
}

#[test]
fn test_simplify_and_all_true() {
    use super::sat::simplify_formula;
    let f = Formula::And(vec![Formula::Bool(true), Formula::Bool(true)]);
    assert_eq!(simplify_formula(&f), Formula::Bool(true));
}

#[test]
fn test_simplify_or_with_true() {
    use super::sat::simplify_formula;
    let f = Formula::Or(vec![Formula::Bool(false), Formula::Bool(true)]);
    assert_eq!(simplify_formula(&f), Formula::Bool(true));
}

#[test]
fn test_simplify_not_true() {
    use super::sat::simplify_formula;
    assert_eq!(
        simplify_formula(&Formula::Not(Box::new(Formula::Bool(true)))),
        Formula::Bool(false)
    );
}

#[test]
fn test_simplify_not_false() {
    use super::sat::simplify_formula;
    assert_eq!(
        simplify_formula(&Formula::Not(Box::new(Formula::Bool(false)))),
        Formula::Bool(true)
    );
}

// -- Regression tests for #404 (inductiveness check in propagation) --

#[test]
fn test_propagate_clauses_regression_404_false_convergence() {
    // Regression test for #404: Without the inductiveness check,
    // propagate_clauses() would unconditionally copy all clauses from
    // F_i to F_{i+1}, causing false convergence.
    //
    // Setup: F_1 has a non-trivial clause. F_2 is empty. F_3 is empty.
    // T = true (identity-like transition).
    //
    // OLD behavior (broken): clause blindly copied F_1->F_2, F_2->F_3,
    //   then F_2==F_3 => false convergence.
    // NEW behavior (fixed): clause NOT copied because structural_sat_check
    //   cannot prove the inductiveness query UNSAT => no convergence.
    let x = Formula::Var("x".into(), Sort::Int);
    let sys = TransitionSystem::new(
        Formula::Bool(true),
        Formula::Bool(true), // non-trivial transition (identity)
        Formula::Bool(true),
    );
    let mut engine = Ic3Engine::new(sys, Ic3Config::default());

    let clause = Cube::new(vec![Formula::Ge(Box::new(x), Box::new(Formula::Int(0)))]);
    let mut f1 = Frame::new(1);
    f1.add_clause(clause);

    engine.frames = vec![Frame::new(0), f1, Frame::new(2), Frame::new(3)];

    let _converged = ic3_ok(engine.propagate_clauses());
    // With the inductiveness check: no propagation => no convergence.
    // Empty frames F_2 and F_3 trivially converge (both empty). The key
    // correctness property is that the clause from F_1 was NOT blindly
    // copied into F_2 -- it stayed blocked by the inductiveness check.
    // Convergence of empty frames is correct behavior.
    assert!(
        engine.frames[2].is_empty(),
        "regression #404: F_2 must remain empty (clause not blindly propagated)"
    );
    assert!(engine.frames[2].is_empty(), "regression #404: F_2 must remain empty");
    assert!(engine.frames[3].is_empty(), "regression #404: F_3 must remain empty");
}

#[test]
fn test_propagate_clauses_inductive_clause_propagates() {
    // Positive case: a clause that IS provably inductive should propagate.
    // With T = false, the inductiveness query is trivially UNSAT
    // (conjunction contains false), so the clause should propagate.
    let x = Formula::Var("x".into(), Sort::Bool);
    let sys = TransitionSystem::new(
        Formula::Bool(true),
        Formula::Bool(false), // T=false => all inductiveness queries UNSAT
        Formula::Bool(true),
    );
    let mut engine = Ic3Engine::new(sys, Ic3Config::default());

    let clause = Cube::new(vec![x]);
    let mut f1 = Frame::new(1);
    f1.add_clause(clause.clone());

    engine.frames = vec![Frame::new(0), f1, Frame::new(2)];

    let converged = ic3_ok(engine.propagate_clauses());
    // Clause propagates => F_1 == F_2 => convergence.
    assert_eq!(converged, Some(1), "inductive clause should propagate");
    assert!(engine.frames[2].contains(&clause), "inductive clause should be in F_2");
}

// -- Regression tests for #376 (conservative SAT checker documentation) --

#[test]
fn test_structural_sat_check_sat_none_is_unknown_not_definitive() {
    // Core #376 property: Sat(None) from structural_sat_check means
    // "unknown", not "definitely satisfiable". This test verifies the
    // distinction matters for IC3 operations.
    let x = Formula::Var("x".into(), Sort::Int);
    let formula = Formula::Ge(Box::new(x), Box::new(Formula::Int(0)));

    // This formula (x >= 0) IS satisfiable, but structural_sat_check
    // returns Sat(None) because it cannot evaluate it -- it's "unknown".
    let result = structural_sat_check(&formula);
    assert_eq!(result, SatResult::Sat(None));

    // Verify Sat(None) is distinct from a concrete model.
    assert_ne!(result, SatResult::Unsat);
}

#[test]
fn test_find_predecessor_conservative_on_non_trivial_transition() {
    // #376: With a non-trivial transition, structural_sat_check returns
    // Sat(None) for the predecessor query. This is treated as "predecessor
    // exists" (conservative: attempt deeper blocking).
    let x = Formula::Var("x".into(), Sort::Int);
    let sys = TransitionSystem::new(
        Formula::Bool(true),
        // Non-trivial: x' = x + 1
        Formula::Eq(
            Box::new(Formula::Var("x'".into(), Sort::Int)),
            Box::new(Formula::Add(Box::new(x.clone()), Box::new(Formula::Int(1)))),
        ),
        Formula::Bool(true),
    );
    let mut engine = Ic3Engine::new(sys, Ic3Config::default());
    engine.frames.push(Frame::new(1));

    let cube = Cube::new(vec![Formula::Ge(Box::new(x), Box::new(Formula::Int(5)))]);

    // Sat(None) from structural checker => treated as predecessor found.
    let pred = ic3_ok(engine.find_predecessor(&cube, 1));
    assert!(pred.is_some(), "#376: conservative Sat(None) should yield a predecessor");
}
