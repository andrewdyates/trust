// trust-cegar: z4 bridge for unsat core extraction
//
// Generates SMT-LIB2 with named assertions and parses unsat core responses.
// This is the interface between trust-cegar's CEGAR loop and the z4 solver.
//
// SMT-LIB2 pattern:
//   (set-option :produce-unsat-cores true)
//   (assert (! formula :named label))
//   ...
//   (check-sat)
//   (get-unsat-core)
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{Formula, Sort};
use std::fmt::Write;

use crate::error::CegarError;
use crate::interpolation::UnsatCore;

/// A request to extract an unsat core from a set of named formulas.
#[derive(Debug, Clone)]
pub struct UnsatCoreRequest {
    /// Named formulas: `(label, formula)` pairs.
    /// Each label must be a valid SMT-LIB2 symbol.
    pub formulas: Vec<(String, Formula)>,
}

impl UnsatCoreRequest {
    /// Create a new request from named formulas.
    #[must_use]
    pub fn new(formulas: Vec<(String, Formula)>) -> Self {
        Self { formulas }
    }

    /// Number of formulas in this request.
    #[must_use]
    pub fn len(&self) -> usize {
        self.formulas.len()
    }

    /// Whether the request has no formulas.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.formulas.is_empty()
    }

    /// Generate SMT-LIB2 script for this request.
    ///
    /// Output includes:
    /// 1. Logic and option settings
    /// 2. Variable declarations (collected from all formulas)
    /// 3. Named assertions
    /// 4. `(check-sat)` and `(get-unsat-core)` commands
    #[must_use]
    pub fn to_smtlib2(&self) -> String {
        let mut script = String::new();

        // Preamble: enable unsat core production.
        script.push_str("(set-option :produce-unsat-cores true)\n");
        script.push_str("(set-logic ALL)\n");

        // Collect and declare variables from all formulas.
        let mut vars: Vec<(String, Sort)> = Vec::new();
        for (_, formula) in &self.formulas {
            collect_formula_vars(formula, &mut vars);
        }
        // Deduplicate by name (first occurrence wins).
        vars.sort_by(|a, b| a.0.cmp(&b.0));
        vars.dedup_by(|a, b| a.0 == b.0);

        for (name, sort) in &vars {
            let _ = writeln!(script, 
                "(declare-const {} {})",
                sanitize_smtlib_symbol(name),
                sort_to_smtlib(sort)
            );
        }

        // Named assertions.
        for (label, formula) in &self.formulas {
            let smt_formula = formula_to_smtlib(formula);
            let _ = writeln!(script, 
                "(assert (! {} :named {}))",
                smt_formula,
                sanitize_smtlib_symbol(label)
            );
        }

        // Check satisfiability and request unsat core.
        script.push_str("(check-sat)\n");
        script.push_str("(get-unsat-core)\n");

        script
    }
}

/// Parse an unsat core response from SMT-LIB2 solver output.
///
/// Expected format after `(check-sat)` returns `unsat`:
/// ```text
/// unsat
/// (label1 label2 label3)
/// ```
///
/// # Errors
/// Returns `CegarError::SolverError` if the output is not parseable or
/// the result is `sat` (meaning the formulas are satisfiable, so no core).
pub fn parse_unsat_core_response(output: &str) -> Result<UnsatCore, CegarError> {
    let trimmed = output.trim();
    let lines: Vec<&str> = trimmed.lines().map(str::trim).collect();

    if lines.is_empty() {
        return Err(CegarError::SolverError {
            detail: "empty solver response".to_string(),
        });
    }

    // Find the check-sat result line.
    let sat_line = lines.iter().find(|l| **l == "sat" || **l == "unsat" || **l == "unknown");

    match sat_line {
        Some(&"sat") => {
            return Err(CegarError::SolverError {
                detail: "formulas are satisfiable (no unsat core available)".to_string(),
            });
        }
        Some(&"unknown") => {
            return Err(CegarError::SolverError {
                detail: "solver returned unknown (timeout or incomplete)".to_string(),
            });
        }
        Some(&"unsat") => { /* continue to parse core */ }
        _ => {
            return Err(CegarError::SolverError {
                detail: format!("unexpected solver response: {trimmed}"),
            });
        }
    }

    // Find the unsat core line: a parenthesized list of labels.
    // It should be after the "unsat" line.
    let core_line = lines.iter().find(|l| l.starts_with('(') && l.ends_with(')'));

    match core_line {
        Some(line) => {
            let inner = &line[1..line.len() - 1];
            if inner.trim().is_empty() {
                return Ok(UnsatCore::new(vec![]));
            }
            let labels: Vec<String> = inner
                .split_whitespace()
                .map(|s| s.to_string())
                .collect();
            Ok(UnsatCore::new(labels))
        }
        None => {
            // No core line found; return empty core.
            Ok(UnsatCore::new(vec![]))
        }
    }
}

/// Delegate to the canonical `Formula::to_smtlib()` method in trust-types.
pub(crate) fn formula_to_smtlib(formula: &Formula) -> String {
    formula.to_smtlib()
}

/// Delegate to the canonical `Sort::to_smtlib()` method in trust-types.
fn sort_to_smtlib(sort: &Sort) -> String {
    sort.to_smtlib()
}

/// Sanitize a variable name into a valid SMT-LIB2 symbol.
///
/// SMT-LIB2 symbols must start with a letter or underscore and contain only
/// letters, digits, and a few special characters. We replace problematic chars.
fn sanitize_smtlib_symbol(name: &str) -> String {
    if name.is_empty() {
        return "_empty".to_string();
    }
    let mut out = String::with_capacity(name.len());
    for c in name.chars() {
        if c.is_alphanumeric() || c == '_' || c == '.' || c == '!' || c == '-' {
            out.push(c);
        } else {
            out.push('_');
        }
    }
    // Ensure it does not start with a digit.
    if out.starts_with(|c: char| c.is_ascii_digit()) {
        out.insert(0, '_');
    }
    out
}

/// Collect variables (with sorts) from a formula.
fn collect_formula_vars(formula: &Formula, out: &mut Vec<(String, Sort)>) {
    match formula {
        Formula::Var(name, sort) => out.push((name.clone(), sort.clone())),
        Formula::Not(inner) | Formula::Neg(inner) => collect_formula_vars(inner, out),
        Formula::And(children) | Formula::Or(children) => {
            for child in children {
                collect_formula_vars(child, out);
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
        | Formula::Rem(a, b)
        | Formula::Select(a, b) => {
            collect_formula_vars(a, out);
            collect_formula_vars(b, out);
        }
        Formula::Ite(c, t, e) | Formula::Store(c, t, e) => {
            collect_formula_vars(c, out);
            collect_formula_vars(t, out);
            collect_formula_vars(e, out);
        }
        Formula::Forall(bindings, body) | Formula::Exists(bindings, body) => {
            out.extend(bindings.iter().cloned());
            collect_formula_vars(body, out);
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
            collect_formula_vars(a, out);
            collect_formula_vars(b, out);
        }
        Formula::BvNot(inner, _)
        | Formula::BvToInt(inner, _, _)
        | Formula::IntToBv(inner, _)
        | Formula::BvZeroExt(inner, _)
        | Formula::BvSignExt(inner, _) => {
            collect_formula_vars(inner, out);
        }
        Formula::BvExtract { inner, .. } => collect_formula_vars(inner, out),
        // Literals: no variables.
        Formula::Bool(_) | Formula::Int(_) | Formula::UInt(_) | Formula::BitVec { .. } => {}
        _ => {},
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_unsat_core_request_to_smtlib2() {
        let req = UnsatCoreRequest::new(vec![
            (
                "a0".to_string(),
                Formula::Lt(
                    Box::new(Formula::Var("x".into(), Sort::Int)),
                    Box::new(Formula::Int(10)),
                ),
            ),
            (
                "b0".to_string(),
                Formula::Gt(
                    Box::new(Formula::Var("x".into(), Sort::Int)),
                    Box::new(Formula::Int(20)),
                ),
            ),
        ]);

        let script = req.to_smtlib2();
        assert!(script.contains("(set-option :produce-unsat-cores true)"));
        assert!(script.contains("(declare-const x Int)"));
        assert!(script.contains("(assert (! (< x 10) :named a0))"));
        assert!(script.contains("(assert (! (> x 20) :named b0))"));
        assert!(script.contains("(check-sat)"));
        assert!(script.contains("(get-unsat-core)"));
    }

    #[test]
    fn test_unsat_core_request_empty() {
        let req = UnsatCoreRequest::new(vec![]);
        assert!(req.is_empty());
        assert_eq!(req.len(), 0);
        let script = req.to_smtlib2();
        assert!(script.contains("(check-sat)"));
    }

    #[test]
    fn test_parse_unsat_core_response_basic() {
        let output = "unsat\n(a0 b0 a1)\n";
        let core = parse_unsat_core_response(output).expect("should parse");
        assert_eq!(core.len(), 3);
        assert!(core.contains("a0"));
        assert!(core.contains("b0"));
        assert!(core.contains("a1"));
    }

    #[test]
    fn test_parse_unsat_core_response_empty_core() {
        let output = "unsat\n()\n";
        let core = parse_unsat_core_response(output).expect("should parse empty");
        assert!(core.is_empty());
    }

    #[test]
    fn test_parse_unsat_core_response_sat_error() {
        let output = "sat\n";
        let result = parse_unsat_core_response(output);
        assert!(matches!(result, Err(CegarError::SolverError { .. })));
    }

    #[test]
    fn test_parse_unsat_core_response_unknown_error() {
        let output = "unknown\n";
        let result = parse_unsat_core_response(output);
        assert!(matches!(result, Err(CegarError::SolverError { .. })));
    }

    #[test]
    fn test_parse_unsat_core_response_empty_output() {
        let result = parse_unsat_core_response("");
        assert!(matches!(result, Err(CegarError::SolverError { .. })));
    }

    #[test]
    fn test_parse_unsat_core_response_no_core_line() {
        let output = "unsat\n";
        let core = parse_unsat_core_response(output).expect("should return empty core");
        assert!(core.is_empty());
    }

    #[test]
    fn test_formula_to_smtlib_int() {
        assert_eq!(formula_to_smtlib(&Formula::Int(42)), "42");
        assert_eq!(formula_to_smtlib(&Formula::Int(-5)), "(- 5)");
    }

    #[test]
    fn test_formula_to_smtlib_bool() {
        assert_eq!(formula_to_smtlib(&Formula::Bool(true)), "true");
        assert_eq!(formula_to_smtlib(&Formula::Bool(false)), "false");
    }

    #[test]
    fn test_formula_to_smtlib_comparison() {
        let f = Formula::Lt(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Int(10)),
        );
        assert_eq!(formula_to_smtlib(&f), "(< x 10)");
    }

    #[test]
    fn test_formula_to_smtlib_and() {
        let f = Formula::And(vec![
            Formula::Bool(true),
            Formula::Bool(false),
        ]);
        assert_eq!(formula_to_smtlib(&f), "(and true false)");
    }

    #[test]
    fn test_formula_to_smtlib_empty_and() {
        assert_eq!(formula_to_smtlib(&Formula::And(vec![])), "true");
    }

    #[test]
    fn test_formula_to_smtlib_single_and() {
        let f = Formula::And(vec![Formula::Bool(true)]);
        assert_eq!(formula_to_smtlib(&f), "true");
    }

    #[test]
    fn test_sanitize_smtlib_symbol() {
        assert_eq!(sanitize_smtlib_symbol("x"), "x");
        assert_eq!(sanitize_smtlib_symbol("_1"), "_1");
        assert_eq!(sanitize_smtlib_symbol("a.b"), "a.b");
        assert_eq!(sanitize_smtlib_symbol("123"), "_123");
        assert_eq!(sanitize_smtlib_symbol(""), "_empty");
    }

    #[test]
    fn test_sort_to_smtlib_representations() {
        assert_eq!(sort_to_smtlib(&Sort::Bool), "Bool");
        assert_eq!(sort_to_smtlib(&Sort::Int), "Int");
        assert_eq!(sort_to_smtlib(&Sort::BitVec(32)), "(_ BitVec 32)");
        assert_eq!(
            sort_to_smtlib(&Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int))),
            "(Array Int Int)"
        );
    }

    #[test]
    fn test_smtlib2_bitvec_variables() {
        let req = UnsatCoreRequest::new(vec![(
            "c0".to_string(),
            Formula::BvULt(
                Box::new(Formula::Var("a".into(), Sort::BitVec(32))),
                Box::new(Formula::Var("b".into(), Sort::BitVec(32))),
                32,
            ),
        )]);
        let script = req.to_smtlib2();
        assert!(script.contains("(declare-const a (_ BitVec 32))"));
        assert!(script.contains("(declare-const b (_ BitVec 32))"));
    }

    #[test]
    fn test_unsat_core_request_deduplicates_vars() {
        let req = UnsatCoreRequest::new(vec![
            (
                "a0".to_string(),
                Formula::Lt(
                    Box::new(Formula::Var("x".into(), Sort::Int)),
                    Box::new(Formula::Int(5)),
                ),
            ),
            (
                "a1".to_string(),
                Formula::Gt(
                    Box::new(Formula::Var("x".into(), Sort::Int)),
                    Box::new(Formula::Int(0)),
                ),
            ),
        ]);
        let script = req.to_smtlib2();
        // x should be declared only once.
        let decl_count = script.matches("(declare-const x Int)").count();
        assert_eq!(decl_count, 1);
    }
}
