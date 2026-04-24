// trust-cegar: Craig interpolation from z4 unsat cores
//
// Given a path formula split into prefix (A) and suffix (B), and an unsat core
// from checking A /\ B, extract predicates that separate A from B.
//
// Theory: If A /\ B is unsatisfiable, a Craig interpolant I exists such that:
//   - A |= I
//   - I /\ B is unsatisfiable
//   - I only uses symbols common to A and B
//
// Our heuristic: clauses from A that appear in the unsat core become predicates,
// since they are the "reason" the prefix makes the suffix infeasible.
//
// Reference: CPAchecker's predicate CPA interpolation
//   refs/cpachecker/src/org/sosy_lab/cpachecker/cpa/predicate/
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::Formula;

use crate::error::CegarError;
use crate::predicate::{CmpOp, Predicate};

/// An unsat core: a subset of clause IDs that are jointly unsatisfiable.
///
/// Each ID corresponds to a named assertion label used in the SMT-LIB2
/// `(assert (! formula :named label))` pattern.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct UnsatCore {
    /// Labels of the clauses in the unsat core.
    pub labels: Vec<String>,
}

impl UnsatCore {
    /// Create an unsat core from a set of labels.
    #[must_use]
    pub fn new(labels: Vec<String>) -> Self {
        Self { labels }
    }

    /// Whether this unsat core is empty (solver returned no core).
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.labels.is_empty()
    }

    /// Number of clauses in the core.
    #[must_use]
    pub fn len(&self) -> usize {
        self.labels.len()
    }

    /// Check if a label is part of this unsat core.
    #[must_use]
    pub fn contains(&self, label: &str) -> bool {
        self.labels.iter().any(|l| l == label)
    }
}

/// Extract Craig interpolant predicates from an unsat core.
///
/// Given a path formula split into prefix (`path_a`) and suffix (`path_b`),
/// and an unsat core from checking A /\ B, extract predicates that separate
/// the prefix from the suffix.
///
/// The heuristic: formulas from A that appear in the unsat core encode the
/// "interface" information that makes B infeasible. We extract comparison
/// predicates from these formulas.
///
/// # Arguments
/// * `path_a` - Named formulas for the prefix: `(label, formula)` pairs.
/// * `path_b` - Named formulas for the suffix: `(label, formula)` pairs.
/// * `unsat_core` - The unsat core labels returned by the solver.
///
/// # Errors
/// Returns `CegarError::SolverError` if the unsat core references unknown labels.
pub fn craig_interpolant(
    path_a: &[(String, Formula)],
    path_b: &[(String, Formula)],
    unsat_core: &UnsatCore,
) -> Result<Vec<Predicate>, CegarError> {
    // Validate that all core labels exist in either A or B.
    let all_labels: Vec<&str> =
        path_a.iter().chain(path_b.iter()).map(|(label, _)| label.as_str()).collect();

    for core_label in &unsat_core.labels {
        if !all_labels.contains(&core_label.as_str()) {
            return Err(CegarError::SolverError {
                detail: format!("unsat core label `{core_label}` not found in path formulas"),
            });
        }
    }

    let mut predicates = Vec::new();

    // Extract predicates from A-side formulas that appear in the unsat core.
    // These are the "interface" predicates that make B infeasible.
    for (label, formula) in path_a {
        if unsat_core.contains(label) {
            extract_predicates_from_formula(formula, &mut predicates);
        }
    }

    // Also extract from B-side core formulas (negated), as they tell us
    // what the suffix requires to be feasible.
    for (label, formula) in path_b {
        if unsat_core.contains(label) {
            extract_negated_predicates_from_formula(formula, &mut predicates);
        }
    }

    // Deduplicate.
    predicates.sort();
    predicates.dedup();

    Ok(predicates)
}

/// Collect variables mentioned in a formula (for common-symbol filtering).
#[must_use]
pub fn formula_variables(formula: &Formula) -> Vec<String> {
    let mut vars = Vec::new();
    collect_vars(formula, &mut vars);
    vars.sort();
    vars.dedup();
    vars
}

fn collect_vars(formula: &Formula, out: &mut Vec<String>) {
    match formula {
        Formula::Var(name, _) => out.push(name.clone()),
        Formula::Not(inner) | Formula::Neg(inner) => collect_vars(inner, out),
        Formula::And(children) | Formula::Or(children) => {
            for child in children {
                collect_vars(child, out);
            }
        }
        Formula::Implies(a, b)
        | Formula::Eq(a, b)
        | Formula::Lt(a, b)
        | Formula::Le(a, b)
        | Formula::Gt(a, b)
        | Formula::Ge(a, b)
        | Formula::Add(a, b)
        | Formula::Sub(a, b)
        | Formula::Mul(a, b)
        | Formula::Div(a, b)
        | Formula::Rem(a, b) => {
            collect_vars(a, out);
            collect_vars(b, out);
        }
        Formula::Ite(cond, then, els) | Formula::Store(cond, then, els) => {
            collect_vars(cond, out);
            collect_vars(then, out);
            collect_vars(els, out);
        }
        Formula::Select(a, b) => {
            collect_vars(a, out);
            collect_vars(b, out);
        }
        Formula::Forall(bindings, body) | Formula::Exists(bindings, body) => {
            for (name, _) in bindings {
                out.push(name.to_string());
            }
            collect_vars(body, out);
        }
        // Bitvector ops
        Formula::BvAdd(a, b, _)
        | Formula::BvSub(a, b, _)
        | Formula::BvMul(a, b, _)
        | Formula::BvUDiv(a, b, _)
        | Formula::BvSDiv(a, b, _)
        | Formula::BvURem(a, b, _)
        | Formula::BvSRem(a, b, _)
        | Formula::BvAnd(a, b, _)
        | Formula::BvOr(a, b, _)
        | Formula::BvXor(a, b, _)
        | Formula::BvShl(a, b, _)
        | Formula::BvLShr(a, b, _)
        | Formula::BvAShr(a, b, _)
        | Formula::BvULt(a, b, _)
        | Formula::BvULe(a, b, _)
        | Formula::BvSLt(a, b, _)
        | Formula::BvSLe(a, b, _)
        | Formula::BvConcat(a, b) => {
            collect_vars(a, out);
            collect_vars(b, out);
        }
        Formula::BvNot(inner, _)
        | Formula::BvToInt(inner, _, _)
        | Formula::IntToBv(inner, _)
        | Formula::BvZeroExt(inner, _)
        | Formula::BvSignExt(inner, _) => {
            collect_vars(inner, out);
        }
        Formula::BvExtract { inner, .. } => collect_vars(inner, out),
        // Literals have no variables.
        Formula::Bool(_) | Formula::Int(_) | Formula::UInt(_) | Formula::BitVec { .. } => {}
        _ => {}
    }
}

/// Extract comparison predicates from a formula.
fn extract_predicates_from_formula(formula: &Formula, out: &mut Vec<Predicate>) {
    match formula {
        // Direct comparisons become predicates.
        Formula::Lt(a, b) => {
            if let (Some(lhs), Some(rhs)) = (formula_to_name(a), formula_to_name(b)) {
                out.push(Predicate::comparison(lhs, CmpOp::Lt, rhs));
            }
        }
        Formula::Le(a, b) => {
            if let (Some(lhs), Some(rhs)) = (formula_to_name(a), formula_to_name(b)) {
                out.push(Predicate::comparison(lhs, CmpOp::Le, rhs));
            }
        }
        Formula::Gt(a, b) => {
            if let (Some(lhs), Some(rhs)) = (formula_to_name(a), formula_to_name(b)) {
                out.push(Predicate::comparison(lhs, CmpOp::Gt, rhs));
            }
        }
        Formula::Ge(a, b) => {
            if let (Some(lhs), Some(rhs)) = (formula_to_name(a), formula_to_name(b)) {
                out.push(Predicate::comparison(lhs, CmpOp::Ge, rhs));
            }
        }
        Formula::Eq(a, b) => {
            if let (Some(lhs), Some(rhs)) = (formula_to_name(a), formula_to_name(b)) {
                out.push(Predicate::comparison(lhs, CmpOp::Eq, rhs));
            }
        }
        // Recurse into boolean connectives.
        Formula::And(children) | Formula::Or(children) => {
            for child in children {
                extract_predicates_from_formula(child, out);
            }
        }
        Formula::Not(inner) => {
            extract_negated_predicates_from_formula(inner, out);
        }
        Formula::Implies(a, b) => {
            extract_negated_predicates_from_formula(a, out);
            extract_predicates_from_formula(b, out);
        }
        _ => {}
    }
}

/// Extract predicates from the negation of a formula.
fn extract_negated_predicates_from_formula(formula: &Formula, out: &mut Vec<Predicate>) {
    match formula {
        Formula::Lt(a, b) => {
            if let (Some(lhs), Some(rhs)) = (formula_to_name(a), formula_to_name(b)) {
                out.push(Predicate::comparison(lhs, CmpOp::Ge, rhs));
            }
        }
        Formula::Le(a, b) => {
            if let (Some(lhs), Some(rhs)) = (formula_to_name(a), formula_to_name(b)) {
                out.push(Predicate::comparison(lhs, CmpOp::Gt, rhs));
            }
        }
        Formula::Gt(a, b) => {
            if let (Some(lhs), Some(rhs)) = (formula_to_name(a), formula_to_name(b)) {
                out.push(Predicate::comparison(lhs, CmpOp::Le, rhs));
            }
        }
        Formula::Ge(a, b) => {
            if let (Some(lhs), Some(rhs)) = (formula_to_name(a), formula_to_name(b)) {
                out.push(Predicate::comparison(lhs, CmpOp::Lt, rhs));
            }
        }
        Formula::Eq(a, b) => {
            if let (Some(lhs), Some(rhs)) = (formula_to_name(a), formula_to_name(b)) {
                out.push(Predicate::comparison(lhs, CmpOp::Ne, rhs));
            }
        }
        Formula::Not(inner) => {
            // Double negation: extract positively.
            extract_predicates_from_formula(inner, out);
        }
        Formula::And(children) | Formula::Or(children) => {
            for child in children {
                extract_negated_predicates_from_formula(child, out);
            }
        }
        _ => {}
    }
}

/// Convert a formula leaf to a name string for predicate construction.
fn formula_to_name(formula: &Formula) -> Option<String> {
    match formula {
        Formula::Var(name, _) => Some(name.clone()),
        Formula::Int(n) => Some(n.to_string()),
        Formula::Bool(b) => Some(if *b { "1".to_string() } else { "0".to_string() }),
        Formula::BitVec { value, .. } => Some(value.to_string()),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use trust_types::Sort;

    use super::*;

    #[test]
    fn test_unsat_core_basic() {
        let core = UnsatCore::new(vec!["a0".into(), "b1".into()]);
        assert_eq!(core.len(), 2);
        assert!(!core.is_empty());
        assert!(core.contains("a0"));
        assert!(core.contains("b1"));
        assert!(!core.contains("c2"));
    }

    #[test]
    fn test_unsat_core_empty() {
        let core = UnsatCore::default();
        assert!(core.is_empty());
        assert_eq!(core.len(), 0);
    }

    #[test]
    fn test_craig_interpolant_extracts_from_a_side() {
        // A: x < 10
        // B: x >= 20
        // Core includes both -> interpolant should contain x < 10 (from A)
        let path_a = vec![(
            "a0".to_string(),
            Formula::Lt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(10))),
        )];
        let path_b = vec![(
            "b0".to_string(),
            Formula::Ge(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(20))),
        )];
        let core = UnsatCore::new(vec!["a0".into(), "b0".into()]);

        let preds = craig_interpolant(&path_a, &path_b, &core).expect("should extract interpolant");
        assert!(!preds.is_empty());
        // Should contain "x < 10" from A-side
        assert!(preds.contains(&Predicate::comparison("x", CmpOp::Lt, "10")));
        // Should contain "x < 20" from negated B-side (Ge negated = Lt)
        assert!(preds.contains(&Predicate::comparison("x", CmpOp::Lt, "20")));
    }

    #[test]
    fn test_craig_interpolant_only_a_in_core() {
        // Only A-side formulas in core -> only A-side predicates extracted
        let path_a = vec![(
            "a0".to_string(),
            Formula::Le(Box::new(Formula::Var("y".into(), Sort::Int)), Box::new(Formula::Int(0))),
        )];
        let path_b = vec![(
            "b0".to_string(),
            Formula::Gt(Box::new(Formula::Var("y".into(), Sort::Int)), Box::new(Formula::Int(100))),
        )];
        let core = UnsatCore::new(vec!["a0".into()]);

        let preds = craig_interpolant(&path_a, &path_b, &core).expect("should succeed");
        assert!(preds.contains(&Predicate::comparison("y", CmpOp::Le, "0")));
        // b0 not in core, so no B-side predicates
        assert!(!preds.contains(&Predicate::comparison("y", CmpOp::Le, "100")));
    }

    #[test]
    fn test_craig_interpolant_unknown_label_error() {
        let path_a = vec![("a0".to_string(), Formula::Bool(true))];
        let path_b = vec![("b0".to_string(), Formula::Bool(false))];
        let core = UnsatCore::new(vec!["unknown_label".into()]);

        let result = craig_interpolant(&path_a, &path_b, &core);
        assert!(matches!(result, Err(CegarError::SolverError { .. })));
    }

    #[test]
    fn test_craig_interpolant_empty_core() {
        let path_a = vec![("a0".to_string(), Formula::Bool(true))];
        let path_b = vec![("b0".to_string(), Formula::Bool(false))];
        let core = UnsatCore::default();

        let preds = craig_interpolant(&path_a, &path_b, &core).expect("empty core should succeed");
        assert!(preds.is_empty());
    }

    #[test]
    fn test_craig_interpolant_equality() {
        let path_a = vec![(
            "a0".to_string(),
            Formula::Eq(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Var("y".into(), Sort::Int)),
            ),
        )];
        let path_b = vec![];
        let core = UnsatCore::new(vec!["a0".into()]);

        let preds = craig_interpolant(&path_a, &path_b, &core).expect("should succeed");
        assert!(preds.contains(&Predicate::comparison("x", CmpOp::Eq, "y")));
    }

    #[test]
    fn test_craig_interpolant_and_formula() {
        // A: (x < 5) AND (y > 0)
        let path_a = vec![(
            "a0".to_string(),
            Formula::And(vec![
                Formula::Lt(
                    Box::new(Formula::Var("x".into(), Sort::Int)),
                    Box::new(Formula::Int(5)),
                ),
                Formula::Gt(
                    Box::new(Formula::Var("y".into(), Sort::Int)),
                    Box::new(Formula::Int(0)),
                ),
            ]),
        )];
        let path_b = vec![];
        let core = UnsatCore::new(vec!["a0".into()]);

        let preds =
            craig_interpolant(&path_a, &path_b, &core).expect("should extract from conjunction");
        assert!(preds.contains(&Predicate::comparison("x", CmpOp::Lt, "5")));
        assert!(preds.contains(&Predicate::comparison("y", CmpOp::Gt, "0")));
    }

    #[test]
    fn test_craig_interpolant_not_formula() {
        // A: NOT(x >= 10) which means x < 10
        let path_a = vec![(
            "a0".to_string(),
            Formula::Not(Box::new(Formula::Ge(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(10)),
            ))),
        )];
        let path_b = vec![];
        let core = UnsatCore::new(vec!["a0".into()]);

        let preds = craig_interpolant(&path_a, &path_b, &core).expect("should handle negation");
        // NOT(x >= 10) -> x < 10
        assert!(preds.contains(&Predicate::comparison("x", CmpOp::Lt, "10")));
    }

    #[test]
    fn test_formula_variables_simple() {
        let f = Formula::Lt(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Var("y".into(), Sort::Int)),
        );
        let vars = formula_variables(&f);
        assert_eq!(vars, vec!["x".to_string(), "y".to_string()]);
    }

    #[test]
    fn test_formula_variables_nested() {
        let f = Formula::And(vec![
            Formula::Lt(Box::new(Formula::Var("a".into(), Sort::Int)), Box::new(Formula::Int(10))),
            Formula::Ge(
                Box::new(Formula::Var("b".into(), Sort::Int)),
                Box::new(Formula::Var("a".into(), Sort::Int)),
            ),
        ]);
        let vars = formula_variables(&f);
        assert_eq!(vars, vec!["a".to_string(), "b".to_string()]);
    }

    #[test]
    fn test_formula_variables_no_vars() {
        let f = Formula::Bool(true);
        let vars = formula_variables(&f);
        assert!(vars.is_empty());
    }

    #[test]
    fn test_craig_interpolant_deduplicates() {
        // Same predicate appears from both A and negated-B
        let path_a = vec![(
            "a0".to_string(),
            Formula::Lt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(10))),
        )];
        let path_b = vec![(
            "b0".to_string(),
            Formula::Ge(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(10))),
        )];
        let core = UnsatCore::new(vec!["a0".into(), "b0".into()]);

        let preds = craig_interpolant(&path_a, &path_b, &core).expect("should deduplicate");
        // x < 10 should appear only once
        let count =
            preds.iter().filter(|p| **p == Predicate::comparison("x", CmpOp::Lt, "10")).count();
        assert_eq!(count, 1);
    }
}
