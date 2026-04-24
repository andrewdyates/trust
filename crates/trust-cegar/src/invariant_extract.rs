// tRust: Loop invariant extraction from Spacer solutions
//
// Converts z4 Spacer fixedpoint model interpretations into trust-types
// Formula and trust-cegar Predicate formats for use in the CEGAR loop.
//
// The Spacer engine returns predicate interpretations as SMT-LIB2 expressions.
// This module parses those expressions into our internal representation.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{Formula, Sort};

use crate::error::CegarError;
use crate::predicate::{CmpOp, Predicate};
use crate::spacer::PredicateInterpretation;

// ---------------------------------------------------------------------------
// Invariant types
// ---------------------------------------------------------------------------

/// A loop invariant extracted from a Spacer solution.
///
/// Maps a set of variable names to a formula that characterizes
/// the invariant over those variables.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoopInvariant {
    /// The name of the loop (matches the CHC predicate name).
    pub loop_name: String,
    /// Parameter names in the invariant (from Spacer's define-fun).
    pub params: Vec<String>,
    /// The invariant formula.
    pub formula: Formula,
    /// CEGAR predicates extracted from the invariant.
    pub predicates: Vec<Predicate>,
}

// ---------------------------------------------------------------------------
// Extraction
// ---------------------------------------------------------------------------

/// Extract loop invariants from Spacer predicate interpretations.
///
/// For each interpretation, parse the SMT-LIB2 body into a Formula and
/// extract CEGAR-compatible predicates.
///
/// # Arguments
/// * `interpretations` - Predicate interpretations from Spacer.
/// * `variable_map` - Maps Spacer parameter names (e.g., "x!0") to
///   original variable names and sorts.
///
/// # Errors
/// Returns `CegarError::SolverError` if parsing fails.
pub fn extract_invariants(
    interpretations: &[PredicateInterpretation],
    variable_map: &[(String, String, Sort)], // (spacer_name, original_name, sort)
) -> Result<Vec<LoopInvariant>, CegarError> {
    let mut invariants = Vec::new();

    for interp in interpretations {
        let formula = parse_smtlib_expr(&interp.body, variable_map)?;
        let predicates = extract_predicates_from_invariant(&formula, variable_map);

        invariants.push(LoopInvariant {
            loop_name: interp.name.clone(),
            params: interp.params.clone(),
            formula,
            predicates,
        });
    }

    Ok(invariants)
}

/// Parse a simplified SMT-LIB2 expression into a Formula.
///
/// Handles the common patterns returned by Spacer:
/// - Atoms: `true`, `false`, integers
/// - Variables: names from the variable_map
/// - Comparisons: `(>= x 0)`, `(<= x 10)`, `(= x y)`
/// - Boolean connectives: `(and ...)`, `(or ...)`, `(not ...)`
///
/// This is intentionally limited — it handles what Spacer actually returns,
/// not the full SMT-LIB2 grammar.
pub fn parse_smtlib_expr(
    expr: &str,
    variable_map: &[(String, String, Sort)],
) -> Result<Formula, CegarError> {
    let trimmed = expr.trim();

    // Atom cases.
    if trimmed == "true" {
        return Ok(Formula::Bool(true));
    }
    if trimmed == "false" {
        return Ok(Formula::Bool(false));
    }

    // Integer literal.
    if let Ok(n) = trimmed.parse::<i128>() {
        return Ok(Formula::Int(n));
    }

    // Variable reference.
    if !trimmed.starts_with('(') {
        // Look up in variable map.
        if let Some((_, orig_name, sort)) =
            variable_map.iter().find(|(spacer_name, _, _)| spacer_name == trimmed)
        {
            return Ok(Formula::Var(orig_name.clone(), sort.clone()));
        }
        // Not in map — treat as a variable with Int sort.
        return Ok(Formula::Var(trimmed.to_string(), Sort::Int));
    }

    // S-expression: (op arg1 arg2 ...)
    let inner = &trimmed[1..trimmed.len() - 1]; // strip outer parens

    // Split into operator and arguments.
    let (operator, args_str) = split_sexp(inner)?;

    match operator {
        "and" => {
            let args = parse_sexp_args(args_str, variable_map)?;
            Ok(Formula::And(args))
        }
        "or" => {
            let args = parse_sexp_args(args_str, variable_map)?;
            Ok(Formula::Or(args))
        }
        "not" => {
            let inner_formula = parse_smtlib_expr(args_str.trim(), variable_map)?;
            Ok(Formula::Not(Box::new(inner_formula)))
        }
        "=>" => {
            let parts = split_two_args(args_str)?;
            let lhs = parse_smtlib_expr(parts.0, variable_map)?;
            let rhs = parse_smtlib_expr(parts.1, variable_map)?;
            Ok(Formula::Implies(Box::new(lhs), Box::new(rhs)))
        }
        "=" => {
            let parts = split_two_args(args_str)?;
            let lhs = parse_smtlib_expr(parts.0, variable_map)?;
            let rhs = parse_smtlib_expr(parts.1, variable_map)?;
            Ok(Formula::Eq(Box::new(lhs), Box::new(rhs)))
        }
        "<" => {
            let parts = split_two_args(args_str)?;
            let lhs = parse_smtlib_expr(parts.0, variable_map)?;
            let rhs = parse_smtlib_expr(parts.1, variable_map)?;
            Ok(Formula::Lt(Box::new(lhs), Box::new(rhs)))
        }
        "<=" => {
            let parts = split_two_args(args_str)?;
            let lhs = parse_smtlib_expr(parts.0, variable_map)?;
            let rhs = parse_smtlib_expr(parts.1, variable_map)?;
            Ok(Formula::Le(Box::new(lhs), Box::new(rhs)))
        }
        ">" => {
            let parts = split_two_args(args_str)?;
            let lhs = parse_smtlib_expr(parts.0, variable_map)?;
            let rhs = parse_smtlib_expr(parts.1, variable_map)?;
            Ok(Formula::Gt(Box::new(lhs), Box::new(rhs)))
        }
        ">=" => {
            let parts = split_two_args(args_str)?;
            let lhs = parse_smtlib_expr(parts.0, variable_map)?;
            let rhs = parse_smtlib_expr(parts.1, variable_map)?;
            Ok(Formula::Ge(Box::new(lhs), Box::new(rhs)))
        }
        "+" => {
            let parts = split_two_args(args_str)?;
            let lhs = parse_smtlib_expr(parts.0, variable_map)?;
            let rhs = parse_smtlib_expr(parts.1, variable_map)?;
            Ok(Formula::Add(Box::new(lhs), Box::new(rhs)))
        }
        "-" => {
            // Could be unary negation or binary subtraction.
            match split_two_args(args_str) {
                Ok(parts) => {
                    let lhs = parse_smtlib_expr(parts.0, variable_map)?;
                    let rhs = parse_smtlib_expr(parts.1, variable_map)?;
                    Ok(Formula::Sub(Box::new(lhs), Box::new(rhs)))
                }
                Err(_) => {
                    // Unary negation.
                    let inner_formula = parse_smtlib_expr(args_str.trim(), variable_map)?;
                    Ok(Formula::Neg(Box::new(inner_formula)))
                }
            }
        }
        "*" => {
            let parts = split_two_args(args_str)?;
            let lhs = parse_smtlib_expr(parts.0, variable_map)?;
            let rhs = parse_smtlib_expr(parts.1, variable_map)?;
            Ok(Formula::Mul(Box::new(lhs), Box::new(rhs)))
        }
        "div" => {
            let parts = split_two_args(args_str)?;
            let lhs = parse_smtlib_expr(parts.0, variable_map)?;
            let rhs = parse_smtlib_expr(parts.1, variable_map)?;
            Ok(Formula::Div(Box::new(lhs), Box::new(rhs)))
        }
        "mod" => {
            let parts = split_two_args(args_str)?;
            let lhs = parse_smtlib_expr(parts.0, variable_map)?;
            let rhs = parse_smtlib_expr(parts.1, variable_map)?;
            Ok(Formula::Rem(Box::new(lhs), Box::new(rhs)))
        }
        "ite" => {
            let args = parse_sexp_args(args_str, variable_map)?;
            if args.len() != 3 {
                return Err(CegarError::SolverError {
                    detail: format!("ite expects 3 arguments, got {}", args.len()),
                });
            }
            let mut args_iter = args.into_iter();
            let cond = args_iter.next().unwrap_or(Formula::Bool(true));
            let then_branch = args_iter.next().unwrap_or(Formula::Bool(true));
            let else_branch = args_iter.next().unwrap_or(Formula::Bool(false));
            Ok(Formula::Ite(Box::new(cond), Box::new(then_branch), Box::new(else_branch)))
        }
        other => Err(CegarError::SolverError {
            detail: format!("unsupported SMT-LIB2 operator: {other}"),
        }),
    }
}

/// Split an s-expression into operator and arguments string.
fn split_sexp(inner: &str) -> Result<(&str, &str), CegarError> {
    let trimmed = inner.trim();
    let op_end = trimmed.find(|c: char| c.is_whitespace()).unwrap_or(trimmed.len());
    let operator = &trimmed[..op_end];
    let args = if op_end < trimmed.len() { &trimmed[op_end + 1..] } else { "" };
    Ok((operator, args.trim()))
}

/// Split arguments string into exactly two s-expression arguments.
fn split_two_args(args: &str) -> Result<(&str, &str), CegarError> {
    let trimmed = args.trim();
    let first_end = find_sexp_end(trimmed)?;
    let first = &trimmed[..first_end];
    let second = trimmed[first_end..].trim();
    if second.is_empty() {
        return Err(CegarError::SolverError {
            detail: format!("expected two arguments, got one in: {trimmed}"),
        });
    }
    Ok((first.trim(), second.trim()))
}

/// Parse multiple s-expression arguments.
fn parse_sexp_args(
    args: &str,
    variable_map: &[(String, String, Sort)],
) -> Result<Vec<Formula>, CegarError> {
    let mut results = Vec::new();
    let mut remaining = args.trim();

    while !remaining.is_empty() {
        let end = find_sexp_end(remaining)?;
        let arg = &remaining[..end];
        results.push(parse_smtlib_expr(arg.trim(), variable_map)?);
        remaining = remaining[end..].trim();
    }

    Ok(results)
}

/// Find the end of the first s-expression in the string.
fn find_sexp_end(input: &str) -> Result<usize, CegarError> {
    let trimmed = input.trim();
    if trimmed.is_empty() {
        return Err(CegarError::SolverError { detail: "empty s-expression".to_string() });
    }

    if trimmed.starts_with('(') {
        // Find matching close paren.
        let mut depth = 0;
        for (idx, ch) in trimmed.char_indices() {
            match ch {
                '(' => depth += 1,
                ')' => {
                    depth -= 1;
                    if depth == 0 {
                        return Ok(idx + 1);
                    }
                }
                _ => {}
            }
        }
        Err(CegarError::SolverError { detail: format!("unbalanced parentheses in: {trimmed}") })
    } else {
        // Atom: find end of token.
        let end = trimmed.find(|c: char| c.is_whitespace() || c == ')').unwrap_or(trimmed.len());
        Ok(end)
    }
}

// ---------------------------------------------------------------------------
// Predicate extraction from invariants
// ---------------------------------------------------------------------------

/// Extract CEGAR predicates from an invariant formula.
///
/// Walks the formula looking for comparison atoms and converts them
/// to `Predicate` values usable in the CEGAR refinement loop.
fn extract_predicates_from_invariant(
    formula: &Formula,
    variable_map: &[(String, String, Sort)],
) -> Vec<Predicate> {
    let mut predicates = Vec::new();
    extract_preds_recursive(formula, variable_map, &mut predicates);
    predicates.sort();
    predicates.dedup();
    predicates
}

fn extract_preds_recursive(
    formula: &Formula,
    _variable_map: &[(String, String, Sort)],
    out: &mut Vec<Predicate>,
) {
    match formula {
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
        Formula::And(children) | Formula::Or(children) => {
            for child in children {
                extract_preds_recursive(child, _variable_map, out);
            }
        }
        Formula::Not(inner) => {
            extract_preds_recursive(inner, _variable_map, out);
        }
        Formula::Implies(a, b) => {
            extract_preds_recursive(a, _variable_map, out);
            extract_preds_recursive(b, _variable_map, out);
        }
        _ => {}
    }
}

/// Convert a formula leaf to a name string.
fn formula_to_name(formula: &Formula) -> Option<String> {
    match formula {
        Formula::Var(name, _) => Some(name.clone()),
        Formula::Int(n) => Some(n.to_string()),
        Formula::Bool(b) => Some(if *b { "1".to_string() } else { "0".to_string() }),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_smtlib_true() {
        let var_map = vec![];
        let formula = parse_smtlib_expr("true", &var_map).expect("should parse");
        assert_eq!(formula, Formula::Bool(true));
    }

    #[test]
    fn test_parse_smtlib_false() {
        let var_map = vec![];
        let formula = parse_smtlib_expr("false", &var_map).expect("should parse");
        assert_eq!(formula, Formula::Bool(false));
    }

    #[test]
    fn test_parse_smtlib_integer() {
        let var_map = vec![];
        let formula = parse_smtlib_expr("42", &var_map).expect("should parse");
        assert_eq!(formula, Formula::Int(42));
    }

    #[test]
    fn test_parse_smtlib_variable_mapped() {
        let var_map = vec![("x!0".to_string(), "x".to_string(), Sort::Int)];
        let formula = parse_smtlib_expr("x!0", &var_map).expect("should parse");
        assert_eq!(formula, Formula::Var("x".into(), Sort::Int));
    }

    #[test]
    fn test_parse_smtlib_variable_unmapped() {
        let var_map = vec![];
        let formula = parse_smtlib_expr("unknown_var", &var_map).expect("should parse");
        assert_eq!(formula, Formula::Var("unknown_var".into(), Sort::Int));
    }

    #[test]
    fn test_parse_smtlib_comparison() {
        let var_map = vec![("x!0".to_string(), "x".to_string(), Sort::Int)];
        let formula = parse_smtlib_expr("(>= x!0 0)", &var_map).expect("should parse");
        assert_eq!(
            formula,
            Formula::Ge(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(0)),)
        );
    }

    #[test]
    fn test_parse_smtlib_and() {
        let var_map = vec![("x!0".to_string(), "x".to_string(), Sort::Int)];
        let formula =
            parse_smtlib_expr("(and (>= x!0 0) (<= x!0 10))", &var_map).expect("should parse");
        match formula {
            Formula::And(children) => {
                assert_eq!(children.len(), 2);
            }
            other => panic!("expected And, got: {:?}", other),
        }
    }

    #[test]
    fn test_parse_smtlib_not() {
        let var_map = vec![];
        let formula = parse_smtlib_expr("(not true)", &var_map).expect("should parse");
        assert_eq!(formula, Formula::Not(Box::new(Formula::Bool(true))));
    }

    #[test]
    fn test_parse_smtlib_arithmetic() {
        let var_map = vec![("x".to_string(), "x".to_string(), Sort::Int)];
        let formula = parse_smtlib_expr("(+ x 1)", &var_map).expect("should parse");
        assert_eq!(
            formula,
            Formula::Add(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(1)),)
        );
    }

    #[test]
    fn test_parse_smtlib_negation() {
        let var_map = vec![("x".to_string(), "x".to_string(), Sort::Int)];
        let formula = parse_smtlib_expr("(- x)", &var_map).expect("should parse");
        assert_eq!(formula, Formula::Neg(Box::new(Formula::Var("x".into(), Sort::Int))));
    }

    #[test]
    fn test_extract_invariants_basic() {
        let interp = PredicateInterpretation {
            name: "Inv".to_string(),
            params: vec!["x!0".to_string()],
            body: "(and (>= x!0 0) (<= x!0 10))".to_string(),
        };
        let var_map = vec![("x!0".to_string(), "x".to_string(), Sort::Int)];

        let invariants = extract_invariants(&[interp], &var_map).expect("should extract");

        assert_eq!(invariants.len(), 1);
        assert_eq!(invariants[0].loop_name, "Inv");
        assert!(!invariants[0].predicates.is_empty());
        // Should have x >= 0 and x <= 10
        assert!(invariants[0].predicates.contains(&Predicate::comparison("x", CmpOp::Ge, "0")));
        assert!(invariants[0].predicates.contains(&Predicate::comparison("x", CmpOp::Le, "10")));
    }

    #[test]
    fn test_extract_invariants_empty() {
        let invariants = extract_invariants(&[], &[]).expect("empty should succeed");
        assert!(invariants.is_empty());
    }

    #[test]
    fn test_extract_invariants_true_body() {
        let interp = PredicateInterpretation {
            name: "Inv".to_string(),
            params: vec![],
            body: "true".to_string(),
        };

        let invariants = extract_invariants(&[interp], &[]).expect("should extract");
        assert_eq!(invariants[0].formula, Formula::Bool(true));
        assert!(invariants[0].predicates.is_empty());
    }

    #[test]
    fn test_loop_invariant_struct() {
        let inv = LoopInvariant {
            loop_name: "test".into(),
            params: vec!["x".into()],
            formula: Formula::Bool(true),
            predicates: vec![],
        };
        assert_eq!(inv.loop_name, "test");
        assert_eq!(inv.params.len(), 1);
    }

    #[test]
    fn test_parse_smtlib_nested() {
        let var_map = vec![("x!0".to_string(), "x".to_string(), Sort::Int)];
        let formula = parse_smtlib_expr("(and (>= x!0 0) (or (<= x!0 10) (= x!0 20)))", &var_map)
            .expect("should parse nested");

        match formula {
            Formula::And(children) => {
                assert_eq!(children.len(), 2);
                match &children[1] {
                    Formula::Or(or_children) => {
                        assert_eq!(or_children.len(), 2);
                    }
                    other => panic!("expected Or, got: {:?}", other),
                }
            }
            other => panic!("expected And, got: {:?}", other),
        }
    }

    #[test]
    fn test_parse_smtlib_ite() {
        let var_map = vec![("x".to_string(), "x".to_string(), Sort::Int)];
        let formula =
            parse_smtlib_expr("(ite (>= x 0) x (- x))", &var_map).expect("should parse ite");
        match formula {
            Formula::Ite(_, _, _) => {} // correct
            other => panic!("expected Ite, got: {:?}", other),
        }
    }

    #[test]
    fn test_extract_predicates_equality() {
        let formula =
            Formula::Eq(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(5)));
        let preds = extract_predicates_from_invariant(&formula, &[]);
        assert!(preds.contains(&Predicate::comparison("x", CmpOp::Eq, "5")));
    }
}
