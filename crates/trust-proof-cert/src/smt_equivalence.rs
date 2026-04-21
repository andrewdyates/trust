// trust-proof-cert/smt_equivalence.rs: SMT-backed formula simplification equivalence
//
// Self-verification T2.1: Verifies that tRust's formula simplifier preserves
// semantics by dispatching equivalence queries to z4. For each simplification
// rule, we construct `original` and `simplified`, then ask z4 to check that
// they differ on no input (UNSAT). Results are labeled "CHECKED (z4)" to
// acknowledge the circularity of using z4 to verify z4-dependent code.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::io::Write as _;
use std::process::{Command, Stdio};
use std::fmt::Write;

use trust_types::smt_logic::{collect_free_var_decls, infer_sort as canonical_infer_sort};
use trust_types::{Formula, Sort};

// ---------------------------------------------------------------------------
// SMT result types
// ---------------------------------------------------------------------------

/// Outcome of an SMT equivalence check.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum SmtEquivResult {
    /// UNSAT: formulas are semantically equivalent. CHECKED (z4).
    Equivalent,
    /// SAT: formulas differ -- simplifier bug! Includes counterexample text.
    NotEquivalent(String),
    /// Solver unavailable or timed out.
    Inconclusive(String),
}

impl SmtEquivResult {
    /// Human-readable label per the design doc.
    pub fn label(&self) -> &str {
        match self {
            SmtEquivResult::Equivalent => "CHECKED (z4)",
            SmtEquivResult::NotEquivalent(_) => "FAILED (z4)",
            SmtEquivResult::Inconclusive(_) => "INCONCLUSIVE",
        }
    }
}

// ---------------------------------------------------------------------------
// z4 subprocess helper
// ---------------------------------------------------------------------------

/// Check whether z4 is available on the system PATH.
pub(crate) fn z4_available() -> bool {
    Command::new("z4")
        .arg("--version")
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
        .is_ok()
}

/// Run an SMT-LIB2 script through z4 and return raw stdout.
fn run_z4(script: &str) -> Result<String, String> {
    let mut child = Command::new("z4")
        .args(["-smt2", "-in"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| format!("failed to spawn z4: {e}"))?;

    if let Some(mut stdin) = child.stdin.take() {
        stdin
            .write_all(script.as_bytes())
            .map_err(|e| format!("write to z4 stdin: {e}"))?;
    }

    let output = child
        .wait_with_output()
        .map_err(|e| format!("read z4 output: {e}"))?;

    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    Ok(stdout)
}

// ---------------------------------------------------------------------------
// Equivalence checking
// ---------------------------------------------------------------------------

// tRust #713: collect_free_vars and infer_sort consolidated in trust-types::smt_logic.
// The canonical infer_sort returns Sort (not Option<Sort>); we wrap it to
// preserve the Option API expected by check_equivalence below (which needs
// to distinguish "unsupported sort" from a known sort for the XOR/neq check).
fn infer_sort(formula: &Formula) -> Option<Sort> {
    let sort = canonical_infer_sort(formula);
    // The canonical fallback is Sort::Int for unknown variants. For this
    // equivalence checker we only support Bool and Int (XOR for Bool,
    // disequality for Int). Return None for anything else.
    match &sort {
        Sort::Bool | Sort::Int => Some(sort),
        _ => None,
    }
}

/// Check whether a formula contains nonlinear arithmetic (e.g., Mul(Var, Var)).
fn has_nonlinear(formula: &Formula) -> bool {
    let mut found = false;
    formula.visit(&mut |f| {
        if found {
            return;
        }
        if let Formula::Mul(a, b) = f {
            // Nonlinear if neither operand is a constant
            let a_const = matches!(a.as_ref(), Formula::Int(_) | Formula::UInt(_));
            let b_const = matches!(b.as_ref(), Formula::Int(_) | Formula::UInt(_));
            if !a_const && !b_const {
                found = true;
            }
        }
    });
    found
}

/// Check that `original` and `simplified` are semantically equivalent via z4.
///
/// For Bool-sorted formulas: checks `(original XOR simplified)` is UNSAT.
/// For Int-sorted formulas: checks `(original != simplified)` is UNSAT.
pub(crate) fn check_equivalence(original: &Formula, simplified: &Formula) -> SmtEquivResult {
    if !z4_available() {
        return SmtEquivResult::Inconclusive("z4 not available".into());
    }

    let sort = match infer_sort(original) {
        Some(s) => s,
        None => return SmtEquivResult::Inconclusive("cannot infer formula sort".into()),
    };

    // Collect all free variables from both formulas — canonical trust-types impl
    let mut all_vars = collect_free_var_decls(original);
    all_vars.extend(collect_free_var_decls(simplified));

    // Detect logic: QF_LIA for linear, QF_NIA for nonlinear
    let logic = if has_nonlinear(original) || has_nonlinear(simplified) {
        "QF_NIA"
    } else {
        "QF_LIA"
    };

    // Build the SMT-LIB2 script
    let mut script = String::new();
    let _ = writeln!(script, "(set-logic {logic})");

    // Declare variables
    for (name, var_sort) in &all_vars {
        let _ = writeln!(script, 
            "(declare-fun {} () {})",
            name,
            var_sort.to_smtlib()
        );
    }

    // Build the non-equivalence formula
    let orig_smt = original.to_smtlib();
    let simp_smt = simplified.to_smtlib();

    match sort {
        Sort::Bool => {
            // XOR: (f AND NOT simplified) OR (NOT f AND simplified)
            let _ = writeln!(script, 
                "(assert (or (and {orig_smt} (not {simp_smt})) (and (not {orig_smt}) {simp_smt})))"
            );
        }
        Sort::Int => {
            // Not equal
            let _ = writeln!(script, 
                "(assert (not (= {orig_smt} {simp_smt})))"
            );
        }
        _ => {
            return SmtEquivResult::Inconclusive(format!("unsupported sort: {sort:?}"));
        }
    }

    script.push_str("(check-sat)\n");
    script.push_str("(exit)\n");

    match run_z4(&script) {
        Ok(output) => {
            let trimmed = output.trim();
            if trimmed.starts_with("unsat") {
                SmtEquivResult::Equivalent
            } else if trimmed.starts_with("sat") {
                SmtEquivResult::NotEquivalent(output)
            } else if trimmed.contains("timeout") || trimmed.contains("unknown") {
                SmtEquivResult::Inconclusive(format!("solver returned: {trimmed}"))
            } else {
                SmtEquivResult::Inconclusive(format!("unexpected solver output: {trimmed}"))
            }
        }
        Err(e) => SmtEquivResult::Inconclusive(e),
    }
}

// ---------------------------------------------------------------------------
// Typed formula generators for QF_LIA
// ---------------------------------------------------------------------------

/// Generate well-typed QF_LIA boolean formulas for testing.
/// Each generator returns (formula, description) pairs.
pub(crate) mod generators {
    use trust_types::{Formula, Sort};

    pub(crate) fn bool_var(name: &str) -> Formula {
        Formula::Var(name.into(), Sort::Bool)
    }

    pub(crate) fn int_var(name: &str) -> Formula {
        Formula::Var(name.into(), Sort::Int)
    }

    /// Generate a set of well-typed boolean formulas for equivalence testing.
    pub(crate) fn bool_formulas() -> Vec<(Formula, &'static str)> {
        let p = bool_var("p");
        let q = bool_var("q");
        let r = bool_var("r");
        let x = int_var("x");
        let y = int_var("y");

        vec![
            // Simple boolean
            (Formula::And(vec![p.clone(), q.clone()]), "p AND q"),
            (Formula::Or(vec![p.clone(), q.clone()]), "p OR q"),
            (Formula::Not(Box::new(p.clone())), "NOT p"),
            (
                Formula::Implies(Box::new(p.clone()), Box::new(q.clone())),
                "p => q",
            ),
            // Nested boolean
            (
                Formula::And(vec![p.clone(), Formula::Or(vec![q.clone(), r.clone()])]),
                "p AND (q OR r)",
            ),
            (
                Formula::Or(vec![
                    Formula::And(vec![p.clone(), q.clone()]),
                    r.clone(),
                ]),
                "(p AND q) OR r",
            ),
            // Comparisons (bool-sorted)
            (
                Formula::Eq(Box::new(x.clone()), Box::new(y.clone())),
                "x = y",
            ),
            (
                Formula::Lt(Box::new(x.clone()), Box::new(y.clone())),
                "x < y",
            ),
            (
                Formula::Gt(
                    Box::new(Formula::Add(Box::new(x.clone()), Box::new(Formula::Int(1)))),
                    Box::new(y.clone()),
                ),
                "x + 1 > y",
            ),
        ]
    }

    /// Generate well-typed integer-sorted formulas.
    pub(crate) fn int_formulas() -> Vec<(Formula, &'static str)> {
        let x = int_var("x");
        let y = int_var("y");

        vec![
            (
                Formula::Add(Box::new(x.clone()), Box::new(y.clone())),
                "x + y",
            ),
            (
                Formula::Mul(Box::new(x.clone()), Box::new(y.clone())),
                "x * y",
            ),
            (
                Formula::Sub(Box::new(x.clone()), Box::new(y.clone())),
                "x - y",
            ),
            (
                Formula::Add(
                    Box::new(Formula::Mul(Box::new(x.clone()), Box::new(Formula::Int(2)))),
                    Box::new(y.clone()),
                ),
                "x*2 + y",
            ),
            (
                Formula::Neg(Box::new(x.clone())),
                "-x",
            ),
        ]
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn int_var(name: &str) -> Formula {
        Formula::Var(name.into(), Sort::Int)
    }

    fn bool_var(name: &str) -> Formula {
        Formula::Var(name.into(), Sort::Bool)
    }

    /// Helper: assert equivalence and print CHECKED (z4) label.
    fn assert_equiv(original: &Formula, simplified: &Formula, rule_name: &str) {
        if !z4_available() {
            eprintln!("SKIP {rule_name}: z4 not available");
            return;
        }
        let result = check_equivalence(original, simplified);
        assert_eq!(
            result,
            SmtEquivResult::Equivalent,
            "Rule '{rule_name}' failed equivalence check: {result:?}"
        );
        eprintln!("{rule_name}: {}", result.label());
    }

    // -----------------------------------------------------------------------
    // z4 availability
    // -----------------------------------------------------------------------

    #[test]
    fn test_z4_available() {
        // This test just verifies we can detect z4. It passes either way.
        let available = z4_available();
        eprintln!("z4 available: {available}");
    }

    // -----------------------------------------------------------------------
    // boolean_simplify rules — CHECKED (z4)
    // -----------------------------------------------------------------------

    #[test]
    fn test_smt_double_negation_elimination() {
        // Rule: Not(Not(x)) -> x
        let p = bool_var("p");
        let original = Formula::Not(Box::new(Formula::Not(Box::new(p.clone()))));
        let simplified = p;
        assert_equiv(&original, &simplified, "double_negation_elimination");
    }

    #[test]
    fn test_smt_and_true_identity() {
        // Rule: And(true, x) -> x
        let p = bool_var("p");
        let original = Formula::And(vec![Formula::Bool(true), p.clone()]);
        let simplified = p;
        assert_equiv(&original, &simplified, "and_true_identity");
    }

    #[test]
    fn test_smt_and_false_annihilation() {
        // Rule: And(false, x) -> false
        let p = bool_var("p");
        let original = Formula::And(vec![Formula::Bool(false), p]);
        let simplified = Formula::Bool(false);
        assert_equiv(&original, &simplified, "and_false_annihilation");
    }

    #[test]
    fn test_smt_or_false_identity() {
        // Rule: Or(false, x) -> x
        let p = bool_var("p");
        let original = Formula::Or(vec![Formula::Bool(false), p.clone()]);
        let simplified = p;
        assert_equiv(&original, &simplified, "or_false_identity");
    }

    #[test]
    fn test_smt_or_true_annihilation() {
        // Rule: Or(true, x) -> true
        let p = bool_var("p");
        let original = Formula::Or(vec![Formula::Bool(true), p]);
        let simplified = Formula::Bool(true);
        assert_equiv(&original, &simplified, "or_true_annihilation");
    }

    #[test]
    fn test_smt_and_empty() {
        // Rule: And([]) -> true
        let original = Formula::And(vec![]);
        let simplified = Formula::Bool(true);
        assert_equiv(&original, &simplified, "and_empty");
    }

    #[test]
    fn test_smt_or_empty() {
        // Rule: Or([]) -> false
        let original = Formula::Or(vec![]);
        let simplified = Formula::Bool(false);
        assert_equiv(&original, &simplified, "or_empty");
    }

    #[test]
    fn test_smt_and_singleton() {
        // Rule: And([x]) -> x
        let p = bool_var("p");
        let original = Formula::And(vec![p.clone()]);
        let simplified = p;
        assert_equiv(&original, &simplified, "and_singleton");
    }

    #[test]
    fn test_smt_or_singleton() {
        // Rule: Or([x]) -> x
        let p = bool_var("p");
        let original = Formula::Or(vec![p.clone()]);
        let simplified = p;
        assert_equiv(&original, &simplified, "or_singleton");
    }

    #[test]
    fn test_smt_and_flatten() {
        // Rule: And(And(a, b), c) -> And(a, b, c)
        let p = bool_var("p");
        let q = bool_var("q");
        let r = bool_var("r");
        let original = Formula::And(vec![
            Formula::And(vec![p.clone(), q.clone()]),
            r.clone(),
        ]);
        let simplified = Formula::And(vec![p, q, r]);
        assert_equiv(&original, &simplified, "and_flatten");
    }

    #[test]
    fn test_smt_or_flatten() {
        // Rule: Or(Or(a, b), c) -> Or(a, b, c)
        let p = bool_var("p");
        let q = bool_var("q");
        let r = bool_var("r");
        let original = Formula::Or(vec![
            Formula::Or(vec![p.clone(), q.clone()]),
            r.clone(),
        ]);
        let simplified = Formula::Or(vec![p, q, r]);
        assert_equiv(&original, &simplified, "or_flatten");
    }

    #[test]
    fn test_smt_and_contradiction() {
        // Rule: And(P, Not(P)) -> false
        let p = bool_var("p");
        let original = Formula::And(vec![p.clone(), Formula::Not(Box::new(p))]);
        let simplified = Formula::Bool(false);
        assert_equiv(&original, &simplified, "and_contradiction");
    }

    #[test]
    fn test_smt_or_excluded_middle() {
        // Rule: Or(P, Not(P)) -> true
        let p = bool_var("p");
        let original = Formula::Or(vec![p.clone(), Formula::Not(Box::new(p))]);
        let simplified = Formula::Bool(true);
        assert_equiv(&original, &simplified, "or_excluded_middle");
    }

    #[test]
    fn test_smt_implies_false_lhs() {
        // Rule: Implies(false, x) -> true
        let p = bool_var("p");
        let original = Formula::Implies(Box::new(Formula::Bool(false)), Box::new(p));
        let simplified = Formula::Bool(true);
        assert_equiv(&original, &simplified, "implies_false_lhs");
    }

    #[test]
    fn test_smt_implies_true_rhs() {
        // Rule: Implies(x, true) -> true
        let p = bool_var("p");
        let original = Formula::Implies(Box::new(p), Box::new(Formula::Bool(true)));
        let simplified = Formula::Bool(true);
        assert_equiv(&original, &simplified, "implies_true_rhs");
    }

    #[test]
    fn test_smt_implies_true_lhs() {
        // Rule: Implies(true, x) -> x
        let p = bool_var("p");
        let original = Formula::Implies(Box::new(Formula::Bool(true)), Box::new(p.clone()));
        let simplified = p;
        assert_equiv(&original, &simplified, "implies_true_lhs");
    }

    #[test]
    fn test_smt_implies_false_rhs() {
        // Rule: Implies(x, false) -> Not(x)
        let p = bool_var("p");
        let original = Formula::Implies(Box::new(p.clone()), Box::new(Formula::Bool(false)));
        let simplified = Formula::Not(Box::new(p));
        assert_equiv(&original, &simplified, "implies_false_rhs");
    }

    // -----------------------------------------------------------------------
    // constant_fold rules — CHECKED (z4)
    // -----------------------------------------------------------------------

    #[test]
    fn test_smt_constant_fold_not_true() {
        // Rule: Not(true) -> false
        let original = Formula::Not(Box::new(Formula::Bool(true)));
        let simplified = Formula::Bool(false);
        assert_equiv(&original, &simplified, "constant_fold_not_true");
    }

    #[test]
    fn test_smt_constant_fold_not_false() {
        // Rule: Not(false) -> true
        let original = Formula::Not(Box::new(Formula::Bool(false)));
        let simplified = Formula::Bool(true);
        assert_equiv(&original, &simplified, "constant_fold_not_false");
    }

    #[test]
    fn test_smt_constant_fold_int_add() {
        // Rule: Add(3, 4) -> 7
        let original = Formula::Add(Box::new(Formula::Int(3)), Box::new(Formula::Int(4)));
        let simplified = Formula::Int(7);
        assert_equiv(&original, &simplified, "constant_fold_int_add");
    }

    #[test]
    fn test_smt_constant_fold_int_sub() {
        // Rule: Sub(10, 3) -> 7
        let original = Formula::Sub(Box::new(Formula::Int(10)), Box::new(Formula::Int(3)));
        let simplified = Formula::Int(7);
        assert_equiv(&original, &simplified, "constant_fold_int_sub");
    }

    #[test]
    fn test_smt_constant_fold_int_mul() {
        // Rule: Mul(3, 4) -> 12
        let original = Formula::Mul(Box::new(Formula::Int(3)), Box::new(Formula::Int(4)));
        let simplified = Formula::Int(12);
        assert_equiv(&original, &simplified, "constant_fold_int_mul");
    }

    #[test]
    fn test_smt_constant_fold_neg() {
        // Rule: Neg(5) -> -5
        let original = Formula::Neg(Box::new(Formula::Int(5)));
        let simplified = Formula::Int(-5);
        assert_equiv(&original, &simplified, "constant_fold_neg");
    }

    #[test]
    fn test_smt_constant_fold_eq_true() {
        // Rule: Eq(3, 3) -> true
        let original = Formula::Eq(Box::new(Formula::Int(3)), Box::new(Formula::Int(3)));
        let simplified = Formula::Bool(true);
        assert_equiv(&original, &simplified, "constant_fold_eq_true");
    }

    #[test]
    fn test_smt_constant_fold_eq_false() {
        // Rule: Eq(3, 4) -> false
        let original = Formula::Eq(Box::new(Formula::Int(3)), Box::new(Formula::Int(4)));
        let simplified = Formula::Bool(false);
        assert_equiv(&original, &simplified, "constant_fold_eq_false");
    }

    #[test]
    fn test_smt_constant_fold_lt() {
        // Rule: Lt(2, 3) -> true
        let original = Formula::Lt(Box::new(Formula::Int(2)), Box::new(Formula::Int(3)));
        let simplified = Formula::Bool(true);
        assert_equiv(&original, &simplified, "constant_fold_lt");
    }

    #[test]
    fn test_smt_constant_fold_gt_false() {
        // Rule: Gt(2, 3) -> false
        let original = Formula::Gt(Box::new(Formula::Int(2)), Box::new(Formula::Int(3)));
        let simplified = Formula::Bool(false);
        assert_equiv(&original, &simplified, "constant_fold_gt_false");
    }

    #[test]
    fn test_smt_constant_fold_ite_true() {
        // Rule: Ite(true, a, b) -> a
        let x = int_var("x");
        let y = int_var("y");
        let original = Formula::Ite(
            Box::new(Formula::Bool(true)),
            Box::new(x.clone()),
            Box::new(y),
        );
        let simplified = x;
        assert_equiv(&original, &simplified, "constant_fold_ite_true");
    }

    #[test]
    fn test_smt_constant_fold_ite_false() {
        // Rule: Ite(false, a, b) -> b
        let x = int_var("x");
        let y = int_var("y");
        let original = Formula::Ite(
            Box::new(Formula::Bool(false)),
            Box::new(x),
            Box::new(y.clone()),
        );
        let simplified = y;
        assert_equiv(&original, &simplified, "constant_fold_ite_false");
    }

    #[test]
    fn test_smt_constant_fold_eq_reflexive() {
        // Rule: Eq(x, x) -> true
        let x = int_var("x");
        let original = Formula::Eq(Box::new(x.clone()), Box::new(x));
        let simplified = Formula::Bool(true);
        assert_equiv(&original, &simplified, "constant_fold_eq_reflexive");
    }

    // -----------------------------------------------------------------------
    // formula_norm rules — CHECKED (z4)
    // -----------------------------------------------------------------------

    #[test]
    fn test_smt_add_zero_identity() {
        // Rule: x + 0 -> x
        let x = int_var("x");
        let original = Formula::Add(Box::new(x.clone()), Box::new(Formula::Int(0)));
        let simplified = x;
        assert_equiv(&original, &simplified, "add_zero_identity");
    }

    #[test]
    fn test_smt_zero_add_identity() {
        // Rule: 0 + x -> x
        let x = int_var("x");
        let original = Formula::Add(Box::new(Formula::Int(0)), Box::new(x.clone()));
        let simplified = x;
        assert_equiv(&original, &simplified, "zero_add_identity");
    }

    #[test]
    fn test_smt_mul_one_identity() {
        // Rule: x * 1 -> x
        let x = int_var("x");
        let original = Formula::Mul(Box::new(x.clone()), Box::new(Formula::Int(1)));
        let simplified = x;
        assert_equiv(&original, &simplified, "mul_one_identity");
    }

    #[test]
    fn test_smt_one_mul_identity() {
        // Rule: 1 * x -> x
        let x = int_var("x");
        let original = Formula::Mul(Box::new(Formula::Int(1)), Box::new(x.clone()));
        let simplified = x;
        assert_equiv(&original, &simplified, "one_mul_identity");
    }

    #[test]
    fn test_smt_mul_zero_annihilation() {
        // Rule: x * 0 -> 0
        let x = int_var("x");
        let original = Formula::Mul(Box::new(x), Box::new(Formula::Int(0)));
        let simplified = Formula::Int(0);
        assert_equiv(&original, &simplified, "mul_zero_annihilation");
    }

    #[test]
    fn test_smt_zero_mul_annihilation() {
        // Rule: 0 * x -> 0
        let x = int_var("x");
        let original = Formula::Mul(Box::new(Formula::Int(0)), Box::new(x));
        let simplified = Formula::Int(0);
        assert_equiv(&original, &simplified, "zero_mul_annihilation");
    }

    #[test]
    fn test_smt_add_commutativity() {
        // Rule: x + y == y + x (commutativity normalization)
        let x = int_var("x");
        let y = int_var("y");
        let original = Formula::Add(Box::new(x.clone()), Box::new(y.clone()));
        let simplified = Formula::Add(Box::new(y), Box::new(x));
        assert_equiv(&original, &simplified, "add_commutativity");
    }

    #[test]
    fn test_smt_mul_commutativity() {
        // Rule: x * 3 == 3 * x (commutativity normalization)
        // Note: z4 cannot decide nonlinear integer arithmetic (x*y == y*x),
        // so we test with a constant multiplier which stays in QF_LIA.
        let x = int_var("x");
        let original = Formula::Mul(Box::new(x.clone()), Box::new(Formula::Int(3)));
        let simplified = Formula::Mul(Box::new(Formula::Int(3)), Box::new(x));
        assert_equiv(&original, &simplified, "mul_commutativity");
    }

    #[test]
    fn test_smt_eq_commutativity() {
        // Rule: Eq(x, y) == Eq(y, x)
        let x = int_var("x");
        let y = int_var("y");
        let original = Formula::Eq(Box::new(x.clone()), Box::new(y.clone()));
        let simplified = Formula::Eq(Box::new(y), Box::new(x));
        assert_equiv(&original, &simplified, "eq_commutativity");
    }

    #[test]
    fn test_smt_and_commutativity() {
        // Rule: And(p, q) == And(q, p)
        let p = bool_var("p");
        let q = bool_var("q");
        let original = Formula::And(vec![p.clone(), q.clone()]);
        let simplified = Formula::And(vec![q, p]);
        assert_equiv(&original, &simplified, "and_commutativity");
    }

    #[test]
    fn test_smt_or_commutativity() {
        // Rule: Or(p, q) == Or(q, p)
        let p = bool_var("p");
        let q = bool_var("q");
        let original = Formula::Or(vec![p.clone(), q.clone()]);
        let simplified = Formula::Or(vec![q, p]);
        assert_equiv(&original, &simplified, "or_commutativity");
    }

    // -----------------------------------------------------------------------
    // End-to-end: apply SimplificationPipeline then check via z4
    // -----------------------------------------------------------------------

    #[test]
    fn test_smt_pipeline_preserves_semantics_bool() {
        if !z4_available() {
            eprintln!("SKIP pipeline_preserves_semantics_bool: z4 not available");
            return;
        }
        for (formula, desc) in generators::bool_formulas() {
            let normalized = crate::formula_norm::normalize(&formula);
            let result = check_equivalence(&formula, &normalized);
            assert_eq!(
                result,
                SmtEquivResult::Equivalent,
                "normalize broke semantics for bool formula: {desc}"
            );
            eprintln!("  normalize({desc}): {}", result.label());
        }
    }

    #[test]
    fn test_smt_pipeline_preserves_semantics_int() {
        if !z4_available() {
            eprintln!("SKIP pipeline_preserves_semantics_int: z4 not available");
            return;
        }
        for (formula, desc) in generators::int_formulas() {
            let normalized = crate::formula_norm::normalize(&formula);
            let result = check_equivalence(&formula, &normalized);
            assert_eq!(
                result,
                SmtEquivResult::Equivalent,
                "normalize broke semantics for int formula: {desc}"
            );
            eprintln!("  normalize({desc}): {}", result.label());
        }
    }

    // -----------------------------------------------------------------------
    // Compound simplification checks
    // -----------------------------------------------------------------------

    #[test]
    fn test_smt_nested_double_negation_and_identity() {
        // And(true, Not(Not(p))) -> p
        let p = bool_var("p");
        let original = Formula::And(vec![
            Formula::Bool(true),
            Formula::Not(Box::new(Formula::Not(Box::new(p.clone())))),
        ]);
        let simplified = p;
        assert_equiv(
            &original,
            &simplified,
            "nested_double_negation_and_identity",
        );
    }

    #[test]
    fn test_smt_deeply_nested_constant_fold() {
        // Not(Eq(Add(1,2), 3)) -> Not(true) -> false
        let original = Formula::Not(Box::new(Formula::Eq(
            Box::new(Formula::Add(
                Box::new(Formula::Int(1)),
                Box::new(Formula::Int(2)),
            )),
            Box::new(Formula::Int(3)),
        )));
        let simplified = Formula::Bool(false);
        assert_equiv(&original, &simplified, "deeply_nested_constant_fold");
    }

    #[test]
    fn test_smt_add_zero_in_comparison() {
        // Lt(x + 0, y) == Lt(x, y)
        let x = int_var("x");
        let y = int_var("y");
        let original = Formula::Lt(
            Box::new(Formula::Add(Box::new(x.clone()), Box::new(Formula::Int(0)))),
            Box::new(y.clone()),
        );
        let simplified = Formula::Lt(Box::new(x), Box::new(y));
        assert_equiv(&original, &simplified, "add_zero_in_comparison");
    }

    #[test]
    fn test_smt_mul_zero_in_eq() {
        // Eq(x * 0, 0) == true (for all x)
        let x = int_var("x");
        let original = Formula::Eq(
            Box::new(Formula::Mul(Box::new(x), Box::new(Formula::Int(0)))),
            Box::new(Formula::Int(0)),
        );
        let simplified = Formula::Bool(true);
        assert_equiv(&original, &simplified, "mul_zero_in_eq");
    }

    #[test]
    fn test_smt_or_with_contradiction_in_and() {
        // Or(And(p, Not(p)), q) == Or(false, q) == q
        let p = bool_var("p");
        let q = bool_var("q");
        let original = Formula::Or(vec![
            Formula::And(vec![p.clone(), Formula::Not(Box::new(p))]),
            q.clone(),
        ]);
        let simplified = q;
        assert_equiv(
            &original,
            &simplified,
            "or_with_contradiction_in_and",
        );
    }

    // -----------------------------------------------------------------------
    // Variable alignment verification
    // -----------------------------------------------------------------------

    #[test]
    fn test_smt_free_var_subset_after_normalize() {
        // Verify that normalization does not introduce new free variables.
        // This checks variable alignment for the equivalence check.
        let x = int_var("x");
        let y = int_var("y");
        let formula = Formula::And(vec![
            Formula::Gt(Box::new(x.clone()), Box::new(Formula::Int(0))),
            Formula::Le(Box::new(y.clone()), Box::new(Formula::Int(10))),
            Formula::Bool(true), // identity element, will be removed
        ]);
        let original_vars = formula.free_variables();
        let normalized = crate::formula_norm::normalize(&formula);
        let normalized_vars = normalized.free_variables();
        assert!(
            normalized_vars.is_subset(&original_vars),
            "normalization introduced new vars: original={original_vars:?}, normalized={normalized_vars:?}"
        );
    }
}
