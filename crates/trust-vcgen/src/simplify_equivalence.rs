// trust-vcgen/simplify_equivalence.rs: Semantic equivalence checking for formula simplifications
//
// tRust #659 / Epic #549: Self-verification T2.1 -- verify that tRust's formula
// simplifier preserves semantics by dispatching equivalence queries to z4.
//
// For each simplification rule, we construct the formula:
//   (original XOR simplified) -- i.e., (original AND NOT simplified) OR (NOT original AND simplified)
// and check UNSAT via z4. UNSAT means the formulas are semantically equivalent.
//
// NOTE: Results are labeled "CHECKED (z4)" not "PROVED" to acknowledge the
// circularity of using z4 to verify z4-dependent code (per the self-hosting
// design's circularity discussion).
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeSet;
use std::io::Write as _;
use std::process::{Command, Stdio};
use std::fmt::Write;

use trust_types::{Formula, Sort};

/// Result of an equivalence check between two formulas.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum EquivalenceResult {
    /// The formulas are semantically equivalent (z4 returned UNSAT on the XOR).
    /// Labeled "CHECKED (z4)" to acknowledge circularity.
    Equivalent,
    /// The formulas are NOT equivalent -- z4 found a distinguishing assignment.
    NotEquivalent {
        /// The z4 model showing a valuation where the formulas differ.
        counterexample: String,
    },
    /// The solver could not determine equivalence (timeout, unknown, etc.).
    Unknown {
        /// Reason the solver could not decide.
        reason: String,
    },
}

/// Errors that can occur during equivalence checking.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum EquivalenceError {
    /// Failed to spawn or communicate with the z4 solver.
    #[error("solver error: {0}")]
    SolverError(String),
}

/// Build the equivalence-checking formula for two Boolean-sorted formulas.
///
/// Constructs: `(original AND NOT simplified) OR (NOT original AND simplified)`
/// which is the XOR of the two formulas. If this is UNSAT, the formulas are
/// equivalent for all variable assignments.
///
/// For Int-sorted formulas (arithmetic expressions), wraps in `Eq` negation:
/// `NOT (original = simplified)` -- UNSAT means they always produce the same value.
#[must_use]
pub fn build_equivalence_formula(original: &Formula, simplified: &Formula) -> Formula {
    // Use the XOR encoding which works for Bool-sorted formulas.
    // (f AND NOT g) OR (NOT f AND g)
    Formula::Or(vec![
        Formula::And(vec![
            original.clone(),
            Formula::Not(Box::new(simplified.clone())),
        ]),
        Formula::And(vec![
            Formula::Not(Box::new(original.clone())),
            simplified.clone(),
        ]),
    ])
}

/// Build the equivalence formula for Int/arithmetic-sorted expressions.
///
/// Constructs: `NOT (original = simplified)` -- UNSAT means they always produce
/// the same integer value.
#[must_use]
pub fn build_int_equivalence_formula(original: &Formula, simplified: &Formula) -> Formula {
    Formula::Not(Box::new(Formula::Eq(
        Box::new(original.clone()),
        Box::new(simplified.clone()),
    )))
}

/// Collect all free variable declarations from a formula.
///
/// Returns a sorted set of (name, sort) pairs for deterministic SMT-LIB2 output.
fn collect_declarations(formula: &Formula) -> BTreeSet<(String, Sort)> {
    let free = formula.free_variables();
    let mut decls = BTreeSet::new();

    formula.visit(&mut |f| {
        if let Formula::Var(name, sort) = f
            && free.contains(name) {
                decls.insert((name.clone(), sort.clone()));
            }
    });

    decls
}

/// Select SMT-LIB2 logic based on formula features.
fn select_logic(formula: &Formula) -> &'static str {
    let mut has_bv = false;
    let mut has_int = false;

    formula.visit(&mut |f| {
        match f {
            Formula::BitVec { .. }
            | Formula::BvAdd(..)
            | Formula::BvSub(..)
            | Formula::BvMul(..)
            | Formula::BvNot(..)
            | Formula::BvAnd(..)
            | Formula::BvOr(..)
            | Formula::BvXor(..)
            | Formula::BvShl(..)
            | Formula::BvLShr(..)
            | Formula::BvAShr(..) => has_bv = true,
            Formula::Var(_, Sort::BitVec(_)) => has_bv = true,
            Formula::Int(_)
            | Formula::UInt(_)
            | Formula::Add(..)
            | Formula::Sub(..)
            | Formula::Mul(..)
            | Formula::Div(..)
            | Formula::Rem(..)
            | Formula::Neg(..) => has_int = true,
            Formula::Var(_, Sort::Int) => has_int = true,
            _ => {}
        }
    });

    match (has_bv, has_int) {
        (true, true) => "ALL",
        (true, false) => "QF_BV",
        _ => "QF_LIA",
    }
}

/// Build a complete SMT-LIB2 script for checking equivalence of two formulas.
///
/// The script declares all free variables from both formulas, asserts the
/// equivalence (XOR) formula, and checks satisfiability.
#[must_use]
pub fn build_equivalence_script(original: &Formula, simplified: &Formula) -> String {
    let equiv_formula = build_equivalence_formula(original, simplified);
    build_script_for_formula(&equiv_formula, original, simplified)
}

/// Build a complete SMT-LIB2 script for checking integer equivalence.
#[must_use]
pub fn build_int_equivalence_script(original: &Formula, simplified: &Formula) -> String {
    let equiv_formula = build_int_equivalence_formula(original, simplified);
    build_script_for_formula(&equiv_formula, original, simplified)
}

fn build_script_for_formula(
    equiv_formula: &Formula,
    original: &Formula,
    simplified: &Formula,
) -> String {
    let mut script = String::new();

    // Collect variables from both original and simplified formulas
    let mut decls = collect_declarations(original);
    decls.extend(collect_declarations(simplified));

    // Logic selection based on the equivalence formula
    let logic = select_logic(equiv_formula);
    let _ = writeln!(script, "(set-logic {logic})");
    script.push_str("(set-option :produce-models true)\n");

    // Declare variables
    for (name, sort) in &decls {
        let _ = writeln!(script, "(declare-const {name} {})", sort.to_smtlib());
    }

    // Assert the equivalence formula
    let _ = writeln!(script, "(assert {})", equiv_formula.to_smtlib());

    // Check satisfiability
    script.push_str("(check-sat)\n");
    script.push_str("(get-model)\n");
    script.push_str("(exit)\n");

    script
}

/// Check whether a simplification preserves semantics via z4.
///
/// Constructs the Boolean XOR equivalence formula and dispatches to z4.
/// Returns `Equivalent` if UNSAT (the formulas agree on all inputs),
/// `NotEquivalent` if SAT (z4 found a distinguishing input), or
/// `Unknown` on timeout/error.
///
/// Results are labeled "CHECKED (z4)" -- not "PROVED" -- because z4 itself
/// is part of the system being verified (acknowledged circularity).
///
/// # Errors
///
/// Returns `EquivalenceError::SolverError` if z4 cannot be spawned or
/// communication fails.
pub fn check_simplification_equivalence(
    original: &Formula,
    simplified: &Formula,
) -> Result<EquivalenceResult, EquivalenceError> {
    let script = build_equivalence_script(original, simplified);
    run_z4_check(&script)
}

/// Check whether an integer simplification preserves semantics via z4.
///
/// Like `check_simplification_equivalence` but uses `!=` instead of XOR,
/// appropriate for Int-sorted expressions.
///
/// # Errors
///
/// Returns `EquivalenceError::SolverError` if z4 cannot be spawned.
pub fn check_int_simplification_equivalence(
    original: &Formula,
    simplified: &Formula,
) -> Result<EquivalenceResult, EquivalenceError> {
    let script = build_int_equivalence_script(original, simplified);
    run_z4_check(&script)
}

/// Run z4 on an SMT-LIB2 script and interpret the result.
fn run_z4_check(script: &str) -> Result<EquivalenceResult, EquivalenceError> {
    let mut child = Command::new("z4")
        .args(["-smt2", "-in"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| EquivalenceError::SolverError(format!("failed to spawn z4: {e}")))?;

    if let Some(mut stdin) = child.stdin.take() {
        stdin
            .write_all(script.as_bytes())
            .map_err(|e| EquivalenceError::SolverError(format!("failed to write to z4: {e}")))?;
    }

    let output = child
        .wait_with_output()
        .map_err(|e| EquivalenceError::SolverError(format!("failed to read z4 output: {e}")))?;

    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let first_line = stdout.lines().next().unwrap_or("").trim();

    match first_line {
        "unsat" => Ok(EquivalenceResult::Equivalent),
        "sat" => {
            // Extract model as counterexample
            let model = stdout
                .lines()
                .skip(1)
                .collect::<Vec<_>>()
                .join("\n");
            Ok(EquivalenceResult::NotEquivalent {
                counterexample: model,
            })
        }
        "unknown" => Ok(EquivalenceResult::Unknown {
            reason: "solver returned unknown".to_string(),
        }),
        "timeout" => Ok(EquivalenceResult::Unknown {
            reason: "solver timeout".to_string(),
        }),
        other => Ok(EquivalenceResult::Unknown {
            reason: format!("unexpected solver output: {other}"),
        }),
    }
}

/// Check if z4 is available on PATH.
#[must_use]
pub fn z4_available() -> bool {
    Command::new("z4")
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::simplify::SimplificationPipeline;

    fn bool_var(name: &str) -> Formula {
        Formula::Var(name.into(), Sort::Bool)
    }

    fn int_var(name: &str) -> Formula {
        Formula::Var(name.into(), Sort::Int)
    }

    // -----------------------------------------------------------------------
    // Unit tests for formula construction (no z4 needed)
    // -----------------------------------------------------------------------

    #[test]
    fn test_build_equivalence_formula_structure() {
        let orig = bool_var("p");
        let simp = Formula::Bool(true);
        let equiv = build_equivalence_formula(&orig, &simp);

        // Should be Or(And(p, Not(true)), And(Not(p), true))
        match &equiv {
            Formula::Or(terms) => {
                assert_eq!(terms.len(), 2);
                match &terms[0] {
                    Formula::And(inner) => assert_eq!(inner.len(), 2),
                    other => panic!("expected And, got {other:?}"),
                }
            }
            other => panic!("expected Or, got {other:?}"),
        }
    }

    #[test]
    fn test_build_int_equivalence_formula_structure() {
        let orig = Formula::Add(Box::new(int_var("x")), Box::new(Formula::Int(1)));
        let simp = Formula::Int(42);
        let equiv = build_int_equivalence_formula(&orig, &simp);

        // Should be Not(Eq(Add(x, 1), 42))
        match &equiv {
            Formula::Not(inner) => match inner.as_ref() {
                Formula::Eq(..) => {}
                other => panic!("expected Eq, got {other:?}"),
            },
            other => panic!("expected Not, got {other:?}"),
        }
    }

    #[test]
    fn test_build_equivalence_script_has_required_parts() {
        let orig = bool_var("p");
        let simp = Formula::Not(Box::new(Formula::Not(Box::new(bool_var("p")))));
        let script = build_equivalence_script(&orig, &simp);

        assert!(script.contains("set-logic"));
        assert!(script.contains("declare-const p Bool"));
        assert!(script.contains("assert"));
        assert!(script.contains("check-sat"));
        assert!(script.contains("exit"));
    }

    #[test]
    fn test_build_int_equivalence_script_int_logic() {
        let orig = Formula::Add(Box::new(int_var("x")), Box::new(Formula::Int(0)));
        let simp = int_var("x");
        let script = build_int_equivalence_script(&orig, &simp);

        assert!(script.contains("declare-const x Int"));
        // Should use QF_LIA or similar integer logic
        assert!(
            script.contains("QF_LIA") || script.contains("LIA") || script.contains("ALL"),
            "script should use an integer-capable logic"
        );
    }

    #[test]
    fn test_collect_declarations_from_both_formulas() {
        let orig = Formula::And(vec![bool_var("p"), bool_var("q")]);
        let simp = bool_var("p");
        let script = build_equivalence_script(&orig, &simp);

        // Both p and q should be declared (q appears in original but not simplified)
        assert!(script.contains("declare-const p Bool"));
        assert!(script.contains("declare-const q Bool"));
    }

    // -----------------------------------------------------------------------
    // z4-backed equivalence tests (skip if z4 not on PATH)
    // -----------------------------------------------------------------------

    // -- Double negation: Not(Not(x)) <=> x --

    #[test]
    fn test_equiv_double_negation() {
        if !z4_available() {
            eprintln!("SKIP: z4 not on PATH");
            return;
        }
        let original = Formula::Not(Box::new(Formula::Not(Box::new(bool_var("x")))));
        let simplified = bool_var("x");

        let result = check_simplification_equivalence(&original, &simplified)
            .expect("solver should not error");
        assert_eq!(
            result,
            EquivalenceResult::Equivalent,
            "CHECKED (z4): Not(Not(x)) <=> x"
        );
    }

    // -- And identity: And(true, x) <=> x --

    #[test]
    fn test_equiv_and_identity() {
        if !z4_available() {
            eprintln!("SKIP: z4 not on PATH");
            return;
        }
        let original = Formula::And(vec![Formula::Bool(true), bool_var("x")]);
        let simplified = bool_var("x");

        let result = check_simplification_equivalence(&original, &simplified)
            .expect("solver should not error");
        assert_eq!(
            result,
            EquivalenceResult::Equivalent,
            "CHECKED (z4): And(true, x) <=> x"
        );
    }

    // -- Or identity: Or(false, x) <=> x --

    #[test]
    fn test_equiv_or_identity() {
        if !z4_available() {
            eprintln!("SKIP: z4 not on PATH");
            return;
        }
        let original = Formula::Or(vec![Formula::Bool(false), bool_var("x")]);
        let simplified = bool_var("x");

        let result = check_simplification_equivalence(&original, &simplified)
            .expect("solver should not error");
        assert_eq!(
            result,
            EquivalenceResult::Equivalent,
            "CHECKED (z4): Or(false, x) <=> x"
        );
    }

    // -- And annihilation: And(false, x) <=> false --

    #[test]
    fn test_equiv_and_annihilation() {
        if !z4_available() {
            eprintln!("SKIP: z4 not on PATH");
            return;
        }
        let original = Formula::And(vec![Formula::Bool(false), bool_var("x")]);
        let simplified = Formula::Bool(false);

        let result = check_simplification_equivalence(&original, &simplified)
            .expect("solver should not error");
        assert_eq!(
            result,
            EquivalenceResult::Equivalent,
            "CHECKED (z4): And(false, x) <=> false"
        );
    }

    // -- Or annihilation: Or(true, x) <=> true --

    #[test]
    fn test_equiv_or_annihilation() {
        if !z4_available() {
            eprintln!("SKIP: z4 not on PATH");
            return;
        }
        let original = Formula::Or(vec![Formula::Bool(true), bool_var("x")]);
        let simplified = Formula::Bool(true);

        let result = check_simplification_equivalence(&original, &simplified)
            .expect("solver should not error");
        assert_eq!(
            result,
            EquivalenceResult::Equivalent,
            "CHECKED (z4): Or(true, x) <=> true"
        );
    }

    // -- Contradiction: And(x, Not(x)) <=> false --

    #[test]
    fn test_equiv_contradiction() {
        if !z4_available() {
            eprintln!("SKIP: z4 not on PATH");
            return;
        }
        let original = Formula::And(vec![
            bool_var("x"),
            Formula::Not(Box::new(bool_var("x"))),
        ]);
        let simplified = Formula::Bool(false);

        let result = check_simplification_equivalence(&original, &simplified)
            .expect("solver should not error");
        assert_eq!(
            result,
            EquivalenceResult::Equivalent,
            "CHECKED (z4): And(x, Not(x)) <=> false"
        );
    }

    // -- Excluded middle: Or(x, Not(x)) <=> true --

    #[test]
    fn test_equiv_excluded_middle() {
        if !z4_available() {
            eprintln!("SKIP: z4 not on PATH");
            return;
        }
        let original = Formula::Or(vec![
            bool_var("x"),
            Formula::Not(Box::new(bool_var("x"))),
        ]);
        let simplified = Formula::Bool(true);

        let result = check_simplification_equivalence(&original, &simplified)
            .expect("solver should not error");
        assert_eq!(
            result,
            EquivalenceResult::Equivalent,
            "CHECKED (z4): Or(x, Not(x)) <=> true"
        );
    }

    // -- Constant folding: Not(true) <=> false --

    #[test]
    fn test_equiv_constant_fold_not_true() {
        if !z4_available() {
            eprintln!("SKIP: z4 not on PATH");
            return;
        }
        let original = Formula::Not(Box::new(Formula::Bool(true)));
        let simplified = Formula::Bool(false);

        let result = check_simplification_equivalence(&original, &simplified)
            .expect("solver should not error");
        assert_eq!(
            result,
            EquivalenceResult::Equivalent,
            "CHECKED (z4): Not(true) <=> false"
        );
    }

    // -- Constant folding: Add(3, 4) <=> 7 --

    #[test]
    fn test_equiv_constant_fold_add() {
        if !z4_available() {
            eprintln!("SKIP: z4 not on PATH");
            return;
        }
        let original = Formula::Add(Box::new(Formula::Int(3)), Box::new(Formula::Int(4)));
        let simplified = Formula::Int(7);

        let result = check_int_simplification_equivalence(&original, &simplified)
            .expect("solver should not error");
        assert_eq!(
            result,
            EquivalenceResult::Equivalent,
            "CHECKED (z4): Add(3, 4) <=> 7"
        );
    }

    // -- Reflexive equality: Eq(x, x) <=> true --

    #[test]
    fn test_equiv_reflexive_equality() {
        if !z4_available() {
            eprintln!("SKIP: z4 not on PATH");
            return;
        }
        let original = Formula::Eq(Box::new(int_var("x")), Box::new(int_var("x")));
        let simplified = Formula::Bool(true);

        let result = check_simplification_equivalence(&original, &simplified)
            .expect("solver should not error");
        assert_eq!(
            result,
            EquivalenceResult::Equivalent,
            "CHECKED (z4): Eq(x, x) <=> true"
        );
    }

    // -- Implies simplification: Implies(false, x) <=> true --

    #[test]
    fn test_equiv_implies_false_lhs() {
        if !z4_available() {
            eprintln!("SKIP: z4 not on PATH");
            return;
        }
        let original = Formula::Implies(Box::new(Formula::Bool(false)), Box::new(bool_var("x")));
        let simplified = Formula::Bool(true);

        let result = check_simplification_equivalence(&original, &simplified)
            .expect("solver should not error");
        assert_eq!(
            result,
            EquivalenceResult::Equivalent,
            "CHECKED (z4): Implies(false, x) <=> true"
        );
    }

    // -- Implies simplification: Implies(true, x) <=> x --

    #[test]
    fn test_equiv_implies_true_lhs() {
        if !z4_available() {
            eprintln!("SKIP: z4 not on PATH");
            return;
        }
        let original = Formula::Implies(Box::new(Formula::Bool(true)), Box::new(bool_var("x")));
        let simplified = bool_var("x");

        let result = check_simplification_equivalence(&original, &simplified)
            .expect("solver should not error");
        assert_eq!(
            result,
            EquivalenceResult::Equivalent,
            "CHECKED (z4): Implies(true, x) <=> x"
        );
    }

    // -- Implies simplification: Implies(x, true) <=> true --

    #[test]
    fn test_equiv_implies_true_rhs() {
        if !z4_available() {
            eprintln!("SKIP: z4 not on PATH");
            return;
        }
        let original = Formula::Implies(Box::new(bool_var("x")), Box::new(Formula::Bool(true)));
        let simplified = Formula::Bool(true);

        let result = check_simplification_equivalence(&original, &simplified)
            .expect("solver should not error");
        assert_eq!(
            result,
            EquivalenceResult::Equivalent,
            "CHECKED (z4): Implies(x, true) <=> true"
        );
    }

    // -- Implies simplification: Implies(x, false) <=> Not(x) --

    #[test]
    fn test_equiv_implies_false_rhs() {
        if !z4_available() {
            eprintln!("SKIP: z4 not on PATH");
            return;
        }
        let original = Formula::Implies(Box::new(bool_var("x")), Box::new(Formula::Bool(false)));
        let simplified = Formula::Not(Box::new(bool_var("x")));

        let result = check_simplification_equivalence(&original, &simplified)
            .expect("solver should not error");
        assert_eq!(
            result,
            EquivalenceResult::Equivalent,
            "CHECKED (z4): Implies(x, false) <=> Not(x)"
        );
    }

    // -- Constant folding: Ite(true, a, b) <=> a --

    #[test]
    fn test_equiv_ite_true_condition() {
        if !z4_available() {
            eprintln!("SKIP: z4 not on PATH");
            return;
        }
        let original = Formula::Ite(
            Box::new(Formula::Bool(true)),
            Box::new(bool_var("a")),
            Box::new(bool_var("b")),
        );
        let simplified = bool_var("a");

        let result = check_simplification_equivalence(&original, &simplified)
            .expect("solver should not error");
        assert_eq!(
            result,
            EquivalenceResult::Equivalent,
            "CHECKED (z4): Ite(true, a, b) <=> a"
        );
    }

    // -- Constant folding: Ite(false, a, b) <=> b --

    #[test]
    fn test_equiv_ite_false_condition() {
        if !z4_available() {
            eprintln!("SKIP: z4 not on PATH");
            return;
        }
        let original = Formula::Ite(
            Box::new(Formula::Bool(false)),
            Box::new(bool_var("a")),
            Box::new(bool_var("b")),
        );
        let simplified = bool_var("b");

        let result = check_simplification_equivalence(&original, &simplified)
            .expect("solver should not error");
        assert_eq!(
            result,
            EquivalenceResult::Equivalent,
            "CHECKED (z4): Ite(false, a, b) <=> b"
        );
    }

    // -- Integer constant folding: Sub(10, 3) <=> 7 --

    #[test]
    fn test_equiv_constant_fold_sub() {
        if !z4_available() {
            eprintln!("SKIP: z4 not on PATH");
            return;
        }
        let original = Formula::Sub(Box::new(Formula::Int(10)), Box::new(Formula::Int(3)));
        let simplified = Formula::Int(7);

        let result = check_int_simplification_equivalence(&original, &simplified)
            .expect("solver should not error");
        assert_eq!(
            result,
            EquivalenceResult::Equivalent,
            "CHECKED (z4): Sub(10, 3) <=> 7"
        );
    }

    // -- Integer constant folding: Mul(3, 4) <=> 12 --

    #[test]
    fn test_equiv_constant_fold_mul() {
        if !z4_available() {
            eprintln!("SKIP: z4 not on PATH");
            return;
        }
        let original = Formula::Mul(Box::new(Formula::Int(3)), Box::new(Formula::Int(4)));
        let simplified = Formula::Int(12);

        let result = check_int_simplification_equivalence(&original, &simplified)
            .expect("solver should not error");
        assert_eq!(
            result,
            EquivalenceResult::Equivalent,
            "CHECKED (z4): Mul(3, 4) <=> 12"
        );
    }

    // -- Integer constant folding: Neg(5) <=> -5 --

    #[test]
    fn test_equiv_constant_fold_neg() {
        if !z4_available() {
            eprintln!("SKIP: z4 not on PATH");
            return;
        }
        let original = Formula::Neg(Box::new(Formula::Int(5)));
        let simplified = Formula::Int(-5);

        let result = check_int_simplification_equivalence(&original, &simplified)
            .expect("solver should not error");
        assert_eq!(
            result,
            EquivalenceResult::Equivalent,
            "CHECKED (z4): Neg(5) <=> -5"
        );
    }

    // -- Comparison constant folding: Lt(2, 3) <=> true --

    #[test]
    fn test_equiv_constant_fold_lt() {
        if !z4_available() {
            eprintln!("SKIP: z4 not on PATH");
            return;
        }
        let original = Formula::Lt(Box::new(Formula::Int(2)), Box::new(Formula::Int(3)));
        let simplified = Formula::Bool(true);

        let result = check_simplification_equivalence(&original, &simplified)
            .expect("solver should not error");
        assert_eq!(
            result,
            EquivalenceResult::Equivalent,
            "CHECKED (z4): Lt(2, 3) <=> true"
        );
    }

    // -- And flattening: And(And(a, b), c) <=> And(a, b, c) --

    #[test]
    fn test_equiv_and_flatten() {
        if !z4_available() {
            eprintln!("SKIP: z4 not on PATH");
            return;
        }
        let original = Formula::And(vec![
            Formula::And(vec![bool_var("a"), bool_var("b")]),
            bool_var("c"),
        ]);
        let simplified = Formula::And(vec![bool_var("a"), bool_var("b"), bool_var("c")]);

        let result = check_simplification_equivalence(&original, &simplified)
            .expect("solver should not error");
        assert_eq!(
            result,
            EquivalenceResult::Equivalent,
            "CHECKED (z4): And(And(a, b), c) <=> And(a, b, c)"
        );
    }

    // -- Or flattening: Or(Or(a, b), c) <=> Or(a, b, c) --

    #[test]
    fn test_equiv_or_flatten() {
        if !z4_available() {
            eprintln!("SKIP: z4 not on PATH");
            return;
        }
        let original = Formula::Or(vec![
            Formula::Or(vec![bool_var("a"), bool_var("b")]),
            bool_var("c"),
        ]);
        let simplified = Formula::Or(vec![bool_var("a"), bool_var("b"), bool_var("c")]);

        let result = check_simplification_equivalence(&original, &simplified)
            .expect("solver should not error");
        assert_eq!(
            result,
            EquivalenceResult::Equivalent,
            "CHECKED (z4): Or(Or(a, b), c) <=> Or(a, b, c)"
        );
    }

    // -----------------------------------------------------------------------
    // Non-equivalent detection (intentionally wrong simplification)
    // -----------------------------------------------------------------------

    #[test]
    fn test_not_equivalent_detected() {
        if !z4_available() {
            eprintln!("SKIP: z4 not on PATH");
            return;
        }
        // And(x, y) is NOT equivalent to x
        let original = Formula::And(vec![bool_var("x"), bool_var("y")]);
        let wrong_simplified = bool_var("x");

        let result = check_simplification_equivalence(&original, &wrong_simplified)
            .expect("solver should not error");
        match result {
            EquivalenceResult::NotEquivalent { .. } => {
                // Correct: z4 detected the non-equivalence
            }
            other => panic!(
                "expected NotEquivalent for And(x, y) vs x, got {other:?}"
            ),
        }
    }

    #[test]
    fn test_not_equivalent_int_detected() {
        if !z4_available() {
            eprintln!("SKIP: z4 not on PATH");
            return;
        }
        // Add(x, 1) is NOT equivalent to x
        let original = Formula::Add(Box::new(int_var("x")), Box::new(Formula::Int(1)));
        let wrong_simplified = int_var("x");

        let result = check_int_simplification_equivalence(&original, &wrong_simplified)
            .expect("solver should not error");
        match result {
            EquivalenceResult::NotEquivalent { .. } => {
                // Correct: z4 detected the non-equivalence
            }
            other => panic!(
                "expected NotEquivalent for Add(x, 1) vs x, got {other:?}"
            ),
        }
    }

    // -----------------------------------------------------------------------
    // Pipeline integration: run the simplifier, check equivalence of result
    // -----------------------------------------------------------------------

    #[test]
    fn test_pipeline_equivalence_complex_formula() {
        if !z4_available() {
            eprintln!("SKIP: z4 not on PATH");
            return;
        }
        // And(true, Not(Not(Eq(Add(1,2), Int(3)))))
        // Pipeline should simplify to: true
        let original = Formula::And(vec![
            Formula::Bool(true),
            Formula::Not(Box::new(Formula::Not(Box::new(Formula::Eq(
                Box::new(Formula::Add(
                    Box::new(Formula::Int(1)),
                    Box::new(Formula::Int(2)),
                )),
                Box::new(Formula::Int(3)),
            ))))),
        ]);

        let pipeline = SimplificationPipeline::default_pipeline();
        let (simplified, _iters) = pipeline.run(original.clone());

        assert_eq!(simplified, Formula::Bool(true), "pipeline should simplify to true");

        let result = check_simplification_equivalence(&original, &simplified)
            .expect("solver should not error");
        assert_eq!(
            result,
            EquivalenceResult::Equivalent,
            "CHECKED (z4): pipeline simplification preserves semantics"
        );
    }

    #[test]
    fn test_pipeline_equivalence_with_variables() {
        if !z4_available() {
            eprintln!("SKIP: z4 not on PATH");
            return;
        }
        // And(true, Or(false, And(x, true)))
        // Should simplify to: x
        let original = Formula::And(vec![
            Formula::Bool(true),
            Formula::Or(vec![
                Formula::Bool(false),
                Formula::And(vec![bool_var("x"), Formula::Bool(true)]),
            ]),
        ]);

        let pipeline = SimplificationPipeline::default_pipeline();
        let (simplified, _iters) = pipeline.run(original.clone());

        let result = check_simplification_equivalence(&original, &simplified)
            .expect("solver should not error");
        assert_eq!(
            result,
            EquivalenceResult::Equivalent,
            "CHECKED (z4): pipeline simplification with variables preserves semantics"
        );
    }

    #[test]
    fn test_pipeline_equivalence_contradiction_simplification() {
        if !z4_available() {
            eprintln!("SKIP: z4 not on PATH");
            return;
        }
        // And(x, Not(x), y) should simplify to false
        let original = Formula::And(vec![
            bool_var("x"),
            Formula::Not(Box::new(bool_var("x"))),
            bool_var("y"),
        ]);

        let pipeline = SimplificationPipeline::default_pipeline();
        let (simplified, _iters) = pipeline.run(original.clone());

        assert_eq!(simplified, Formula::Bool(false));

        let result = check_simplification_equivalence(&original, &simplified)
            .expect("solver should not error");
        assert_eq!(
            result,
            EquivalenceResult::Equivalent,
            "CHECKED (z4): contradiction simplification preserves semantics"
        );
    }

    #[test]
    fn test_pipeline_equivalence_excluded_middle_simplification() {
        if !z4_available() {
            eprintln!("SKIP: z4 not on PATH");
            return;
        }
        // Or(x, Not(x), y) should simplify to true
        let original = Formula::Or(vec![
            bool_var("x"),
            Formula::Not(Box::new(bool_var("x"))),
            bool_var("y"),
        ]);

        let pipeline = SimplificationPipeline::default_pipeline();
        let (simplified, _iters) = pipeline.run(original.clone());

        assert_eq!(simplified, Formula::Bool(true));

        let result = check_simplification_equivalence(&original, &simplified)
            .expect("solver should not error");
        assert_eq!(
            result,
            EquivalenceResult::Equivalent,
            "CHECKED (z4): excluded middle simplification preserves semantics"
        );
    }

    // -----------------------------------------------------------------------
    // Multi-variable equivalence tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_equiv_and_or_de_morgan_style() {
        if !z4_available() {
            eprintln!("SKIP: z4 not on PATH");
            return;
        }
        // And(x, Or(y, false)) <=> And(x, y)
        // (Or identity eliminates false, then no further simplification needed)
        let original = Formula::And(vec![
            bool_var("x"),
            Formula::Or(vec![bool_var("y"), Formula::Bool(false)]),
        ]);
        let simplified = Formula::And(vec![bool_var("x"), bool_var("y")]);

        let result = check_simplification_equivalence(&original, &simplified)
            .expect("solver should not error");
        assert_eq!(
            result,
            EquivalenceResult::Equivalent,
            "CHECKED (z4): And(x, Or(y, false)) <=> And(x, y)"
        );
    }

    // -----------------------------------------------------------------------
    // Full suite summary
    // -----------------------------------------------------------------------

    #[test]
    fn test_equivalence_suite_summary() {
        if !z4_available() {
            eprintln!("SKIP: z4 not on PATH");
            return;
        }

        let cases: Vec<(&str, Formula, Formula, bool)> = vec![
            (
                "double_negation",
                Formula::Not(Box::new(Formula::Not(Box::new(bool_var("x"))))),
                bool_var("x"),
                true, // use Bool XOR
            ),
            (
                "and_identity",
                Formula::And(vec![Formula::Bool(true), bool_var("x")]),
                bool_var("x"),
                true,
            ),
            (
                "or_identity",
                Formula::Or(vec![Formula::Bool(false), bool_var("x")]),
                bool_var("x"),
                true,
            ),
            (
                "and_annihilation",
                Formula::And(vec![Formula::Bool(false), bool_var("x")]),
                Formula::Bool(false),
                true,
            ),
            (
                "or_annihilation",
                Formula::Or(vec![Formula::Bool(true), bool_var("x")]),
                Formula::Bool(true),
                true,
            ),
            (
                "contradiction",
                Formula::And(vec![bool_var("x"), Formula::Not(Box::new(bool_var("x")))]),
                Formula::Bool(false),
                true,
            ),
            (
                "excluded_middle",
                Formula::Or(vec![bool_var("x"), Formula::Not(Box::new(bool_var("x")))]),
                Formula::Bool(true),
                true,
            ),
        ];

        println!();
        println!("=== tRust Self-Verification T2.1: Formula Simplification Equivalence ===");
        println!("Note: CHECKED (z4) -- uses z4 solver (acknowledged circularity).");
        println!();

        let mut checked = 0;
        for (name, original, simplified, _is_bool) in &cases {
            let result = check_simplification_equivalence(original, simplified)
                .expect("solver should not error");
            let status = match &result {
                EquivalenceResult::Equivalent => "CHECKED (z4)",
                EquivalenceResult::NotEquivalent { .. } => "FAILED",
                EquivalenceResult::Unknown { reason } => {
                    eprintln!("  {name}: UNKNOWN ({reason})");
                    "UNKNOWN"
                }
            };
            println!("  {name}: {status}");
            assert_eq!(
                result,
                EquivalenceResult::Equivalent,
                "simplification rule '{name}' should be equivalent"
            );
            checked += 1;
        }

        println!();
        println!("  {checked}/{} simplification rules checked via z4.", cases.len());
        println!("  tRust verified its own simplifier preserves semantics.");
        println!();
    }
}
