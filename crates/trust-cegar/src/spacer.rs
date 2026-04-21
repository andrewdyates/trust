// tRust: z4 Spacer bridge for CHC solving
//
// Generates SMT-LIB2 fixedpoint scripts from CHC systems and parses
// Spacer engine results back into predicate interpretations.
//
// Spacer uses the SMT-LIB2 fixedpoint extension:
//   (set-logic HORN)
//   (declare-fun Inv (Int) Bool)
//   (assert (forall ((x Int)) (=> (pre x) (Inv x))))      ; init
//   (assert (forall ((x Int) (x! Int)) (=> (and (Inv x) (body x x!)) (Inv x!))))  ; step
//   (assert (forall ((x Int)) (=> (and (Inv x) (exit x)) (post x))))  ; property
//   (check-sat)
//   (get-model)  ; contains Inv interpretation
//
// Reference: Komuravelli, Gurfinkel, Chaki,
//   "SMT-Based Model Checking for Recursive Programs" (CAV 2014)
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::Sort;
use std::fmt::Write;

use crate::chc::{ChcSystem, ClauseKind, HornClause, PredicateApp};
use crate::error::CegarError;
use crate::z4_bridge::formula_to_smtlib;

// ---------------------------------------------------------------------------
// Spacer result types
// ---------------------------------------------------------------------------

/// The result of a Spacer CHC solving attempt.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum SpacerResult {
    /// The CHC system is satisfiable — an invariant exists.
    /// Contains predicate interpretations: `(predicate_name, param_names, body_smtlib)`.
    Sat {
        /// Interpretations for each predicate.
        interpretations: Vec<PredicateInterpretation>,
    },
    /// The CHC system is unsatisfiable — no invariant exists (property violated).
    Unsat,
    /// Solver timed out or returned unknown.
    Unknown { reason: String },
}

/// A predicate interpretation returned by Spacer.
///
/// Represents the discovered invariant: `Inv(x1, x2, ...) := body`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PredicateInterpretation {
    /// The predicate name.
    pub name: String,
    /// Parameter names used in the body.
    pub params: Vec<String>,
    /// The body formula as an SMT-LIB2 string.
    /// Parsed into a `Formula` by `invariant_extract`.
    pub body: String,
}

// ---------------------------------------------------------------------------
// SMT-LIB2 fixedpoint generation
// ---------------------------------------------------------------------------

/// Generate an SMT-LIB2 fixedpoint script from a CHC system for z4's Spacer.
///
/// The script uses the HORN logic with universally quantified Horn clauses.
///
/// # Errors
/// Returns `CegarError::InconsistentAbstraction` if the system is invalid.
pub fn chc_to_smtlib2(system: &ChcSystem) -> Result<String, CegarError> {
    system.validate()?;

    let mut script = String::new();

    // Preamble.
    script.push_str("; tRust: CHC system for Spacer\n");
    script.push_str("(set-logic HORN)\n\n");

    // Declare predicate symbols as uninterpreted functions returning Bool.
    for pred in &system.predicates {
        let _ = write!(script, "(declare-fun {} (", pred.name);
        for (idx, sort) in pred.arg_sorts.iter().enumerate() {
            if idx > 0 {
                script.push(' ');
            }
            script.push_str(&sort_to_smtlib(sort));
        }
        script.push_str(") Bool)\n");
    }
    script.push('\n');

    // Emit each Horn clause as a universally quantified assertion.
    for (idx, clause) in system.clauses.iter().enumerate() {
        let _ = writeln!(script, "; Clause {idx}: {:?}", clause.kind);
        script.push_str(&clause_to_smtlib(clause, system));
        script.push('\n');
    }

    // Check satisfiability.
    script.push_str("(check-sat)\n");
    script.push_str("(get-model)\n");

    Ok(script)
}

/// Convert a single Horn clause to an SMT-LIB2 assertion.
fn clause_to_smtlib(clause: &HornClause, system: &ChcSystem) -> String {
    // Collect all variables that need to be universally quantified.
    let mut bound_vars: Vec<(String, Sort)> = Vec::new();

    // Collect from body predicates.
    for app in &clause.body_predicates {
        collect_app_vars(app, system, &mut bound_vars);
    }
    // Collect from head predicate.
    if let Some(head) = &clause.head {
        collect_app_vars(head, system, &mut bound_vars);
    }
    // Collect from constraint.
    collect_formula_free_vars(&clause.constraint, &mut bound_vars);
    // Collect from postcondition.
    if let Some(post) = &clause.postcondition {
        collect_formula_free_vars(post, &mut bound_vars);
    }

    // Deduplicate by name.
    bound_vars.sort_by(|a, b| a.0.cmp(&b.0));
    bound_vars.dedup_by(|a, b| a.0 == b.0);

    // Build the implication body: body_preds /\ constraint.
    let mut body_parts: Vec<String> = Vec::new();

    for app in &clause.body_predicates {
        body_parts.push(app_to_smtlib(app));
    }

    let constraint_smt = formula_to_smtlib(&clause.constraint);
    // Only add constraint if it's not trivially true.
    if constraint_smt != "true" {
        body_parts.push(constraint_smt);
    }

    let body_smt = match body_parts.len() {
        0 => "true".to_string(),
        1 => body_parts.into_iter().next().unwrap_or_default(),
        _ => format!("(and {})", body_parts.join(" ")),
    };

    // Build the head.
    let head_smt = match &clause.kind {
        ClauseKind::Init | ClauseKind::Step => {
            if let Some(head) = &clause.head {
                app_to_smtlib(head)
            } else {
                "false".to_string()
            }
        }
        ClauseKind::Property => {
            if let Some(post) = &clause.postcondition {
                formula_to_smtlib(post)
            } else {
                "true".to_string()
            }
        }
    };

    // Build quantifier binding list.
    let bindings: String = bound_vars
        .iter()
        .map(|(name, sort)| format!("({name} {})", sort_to_smtlib(sort)))
        .collect::<Vec<_>>()
        .join(" ");

    if bound_vars.is_empty() {
        format!("(assert (=> {body_smt} {head_smt}))\n")
    } else {
        format!("(assert (forall ({bindings}) (=> {body_smt} {head_smt})))\n")
    }
}

/// Convert a predicate application to SMT-LIB2.
fn app_to_smtlib(app: &PredicateApp) -> String {
    if app.args.is_empty() {
        app.predicate.clone()
    } else {
        let args: Vec<String> = app.args.iter().map(formula_to_smtlib).collect();
        format!("({} {})", app.predicate, args.join(" "))
    }
}

/// Collect free variables from a predicate application.
fn collect_app_vars(
    app: &PredicateApp,
    system: &ChcSystem,
    out: &mut Vec<(String, Sort)>,
) {
    let decl = system.predicates.iter().find(|p| p.name == app.predicate);
    for (idx, arg) in app.args.iter().enumerate() {
        if let trust_types::Formula::Var(name, sort) = arg {
            let _ = idx; // Sort comes from the variable itself, not the decl
            out.push((name.clone(), sort.clone()));
        }
        // For non-variable args, collect recursively.
        collect_formula_free_vars(arg, out);
    }
    let _ = decl; // Used for documentation
}

/// Collect free variables from a formula.
fn collect_formula_free_vars(formula: &trust_types::Formula, out: &mut Vec<(String, Sort)>) {
    match formula {
        trust_types::Formula::Var(name, sort) => {
            out.push((name.clone(), sort.clone()));
        }
        trust_types::Formula::Not(inner) | trust_types::Formula::Neg(inner) => {
            collect_formula_free_vars(inner, out);
        }
        trust_types::Formula::And(children) | trust_types::Formula::Or(children) => {
            for child in children {
                collect_formula_free_vars(child, out);
            }
        }
        trust_types::Formula::Implies(a, b)
        | trust_types::Formula::Eq(a, b)
        | trust_types::Formula::Lt(a, b)
        | trust_types::Formula::Le(a, b)
        | trust_types::Formula::Gt(a, b)
        | trust_types::Formula::Ge(a, b)
        | trust_types::Formula::Add(a, b)
        | trust_types::Formula::Sub(a, b)
        | trust_types::Formula::Mul(a, b)
        | trust_types::Formula::Div(a, b)
        | trust_types::Formula::Rem(a, b) => {
            collect_formula_free_vars(a, out);
            collect_formula_free_vars(b, out);
        }
        trust_types::Formula::Ite(c, t, e) => {
            collect_formula_free_vars(c, out);
            collect_formula_free_vars(t, out);
            collect_formula_free_vars(e, out);
        }
        _ => {}
    }
}

/// Delegate to the canonical `Sort::to_smtlib()` method in trust-types.
fn sort_to_smtlib(sort: &Sort) -> String {
    sort.to_smtlib()
}

// ---------------------------------------------------------------------------
// Spacer response parsing
// ---------------------------------------------------------------------------

/// Parse a Spacer response to extract predicate interpretations.
///
/// Expected format:
/// ```text
/// sat
/// (model
///   (define-fun Inv ((x!0 Int)) Bool
///     (and (>= x!0 0) (<= x!0 10)))
/// )
/// ```
///
/// # Errors
/// Returns `CegarError::SolverError` on parse failure.
pub fn parse_spacer_response(output: &str) -> Result<SpacerResult, CegarError> {
    let trimmed = output.trim();

    if trimmed.is_empty() {
        return Err(CegarError::SolverError {
            detail: "empty Spacer response".to_string(),
        });
    }

    // Find the sat/unsat/unknown line.
    let first_line = trimmed.lines().next().unwrap_or("").trim();

    match first_line {
        "unsat" => Ok(SpacerResult::Unsat),
        "unknown" => {
            let reason = trimmed
                .lines()
                .nth(1)
                .unwrap_or("no reason given")
                .trim()
                .to_string();
            Ok(SpacerResult::Unknown { reason })
        }
        "sat" => {
            let interpretations = parse_model(trimmed)?;
            Ok(SpacerResult::Sat { interpretations })
        }
        other => Err(CegarError::SolverError {
            detail: format!("unexpected Spacer result: {other}"),
        }),
    }
}

/// Parse a (model ...) block to extract define-fun interpretations.
fn parse_model(output: &str) -> Result<Vec<PredicateInterpretation>, CegarError> {
    let mut interpretations = Vec::new();

    // Look for define-fun entries.
    // Format: (define-fun Name ((param Sort) ...) Bool body)
    let mut remaining = output;

    while let Some(def_start) = remaining.find("(define-fun ") {
        remaining = &remaining[def_start + 12..]; // skip "(define-fun "

        // Extract the function name.
        let name_end = remaining.find(|c: char| c.is_whitespace()).unwrap_or(remaining.len());
        let name = remaining[..name_end].to_string();
        remaining = remaining[name_end..].trim_start();

        // Extract parameter list: ((param1 Sort1) (param2 Sort2) ...)
        if !remaining.starts_with('(') {
            continue;
        }
        let params_end = find_matching_paren(remaining);
        if params_end == 0 {
            continue;
        }
        let params_str = &remaining[1..params_end - 1]; // strip outer parens
        let params = parse_params(params_str);
        remaining = remaining[params_end..].trim_start();

        // Skip return sort (Bool).
        if let Some(sort_end) = remaining.find(|c: char| c.is_whitespace()) {
            remaining = remaining[sort_end..].trim_start();
        } else {
            continue;
        }

        // Extract body (everything until the matching close paren of define-fun).
        // The body might be a complex s-expression.
        let body = if remaining.starts_with('(') {
            let body_end = find_matching_paren(remaining);
            if body_end == 0 {
                continue;
            }
            let body_str = remaining[..body_end].to_string();
            remaining = &remaining[body_end..];
            body_str
        } else {
            // Simple atom (e.g., "true", "false").
            let body_end = remaining
                .find(|c: char| c == ')' || c.is_whitespace())
                .unwrap_or(remaining.len());
            let body_str = remaining[..body_end].to_string();
            remaining = &remaining[body_end..];
            body_str
        };

        interpretations.push(PredicateInterpretation {
            name,
            params,
            body,
        });
    }

    Ok(interpretations)
}

/// Parse parameter list from define-fun.
/// Input: "(x!0 Int) (y!0 Int)" -> ["x!0", "y!0"]
fn parse_params(params_str: &str) -> Vec<String> {
    let mut params = Vec::new();
    let mut rest = params_str.trim();

    while let Some(start) = rest.find('(') {
        rest = &rest[start + 1..];
        if let Some(name_end) = rest.find(|c: char| c.is_whitespace()) {
            params.push(rest[..name_end].to_string());
        }
        if let Some(end) = rest.find(')') {
            rest = &rest[end + 1..];
        } else {
            break;
        }
    }

    params
}

/// Find the index past the matching closing parenthesis.
/// Returns 0 if no match found.
fn find_matching_paren(input: &str) -> usize {
    if !input.starts_with('(') {
        return 0;
    }
    let mut depth = 0;
    for (idx, ch) in input.char_indices() {
        match ch {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return idx + 1;
                }
            }
            _ => {}
        }
    }
    0 // unbalanced
}

/// Configuration for Spacer solving.
#[derive(Debug, Clone)]
pub struct SpacerConfig {
    /// Timeout in milliseconds for the Spacer engine.
    pub timeout_ms: u64,
    /// Maximum number of unfolding steps before giving up.
    pub max_unfold: Option<u32>,
}

impl Default for SpacerConfig {
    fn default() -> Self {
        Self {
            timeout_ms: 30_000,
            max_unfold: None,
        }
    }
}

impl SpacerConfig {
    /// Generate SMT-LIB2 options for this configuration.
    #[must_use]
    pub fn to_smtlib2_options(&self) -> String {
        let mut opts = String::new();
        let _ = writeln!(opts, 
            "(set-option :timeout {})",
            self.timeout_ms
        );
        if let Some(max) = self.max_unfold {
            let _ = writeln!(opts, 
                "(set-option :fp.spacer.max_level {})",
                max
            );
        }
        opts
    }
}

#[cfg(test)]
mod tests {
    use trust_types::Formula;

    use super::*;
    use crate::chc::{ChcPredicate, HornClause, PredicateApp};

    fn simple_counting_system() -> ChcSystem {
        let mut system = ChcSystem::new();
        system.add_predicate(ChcPredicate::new("Inv", vec![Sort::Int]));

        // Init: x = 0 => Inv(x)
        system.add_clause(HornClause::init(
            Formula::Eq(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            PredicateApp::new("Inv", vec![Formula::Var("x".into(), Sort::Int)]),
        ));

        // Step: Inv(x) /\ x < 10 /\ x' = x + 1 => Inv(x')
        system.add_clause(HornClause::step(
            PredicateApp::new("Inv", vec![Formula::Var("x".into(), Sort::Int)]),
            Formula::And(vec![
                Formula::Lt(
                    Box::new(Formula::Var("x".into(), Sort::Int)),
                    Box::new(Formula::Int(10)),
                ),
                Formula::Eq(
                    Box::new(Formula::Var("x_prime".into(), Sort::Int)),
                    Box::new(Formula::Add(
                        Box::new(Formula::Var("x".into(), Sort::Int)),
                        Box::new(Formula::Int(1)),
                    )),
                ),
            ]),
            PredicateApp::new("Inv", vec![Formula::Var("x_prime".into(), Sort::Int)]),
        ));

        // Property: Inv(x) /\ x >= 10 => x <= 10
        system.add_clause(HornClause::property(
            PredicateApp::new("Inv", vec![Formula::Var("x".into(), Sort::Int)]),
            Formula::Ge(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(10)),
            ),
            Formula::Le(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(10)),
            ),
        ));

        system
    }

    #[test]
    fn test_chc_to_smtlib2_basic() {
        let system = simple_counting_system();
        let script = chc_to_smtlib2(&system).expect("should generate");

        assert!(script.contains("(set-logic HORN)"));
        assert!(script.contains("(declare-fun Inv (Int) Bool)"));
        assert!(script.contains("(check-sat)"));
        assert!(script.contains("(get-model)"));
        assert!(script.contains("forall"));
    }

    #[test]
    fn test_chc_to_smtlib2_contains_clauses() {
        let system = simple_counting_system();
        let script = chc_to_smtlib2(&system).expect("should generate");

        // Should have 3 assert statements (one per clause).
        let assert_count = script.matches("(assert ").count();
        assert_eq!(assert_count, 3);
    }

    #[test]
    fn test_chc_to_smtlib2_empty_system() {
        let system = ChcSystem::new();
        let script = chc_to_smtlib2(&system).expect("should generate for empty");
        assert!(script.contains("(set-logic HORN)"));
        assert!(script.contains("(check-sat)"));
    }

    #[test]
    fn test_parse_spacer_response_sat() {
        let output = r#"sat
(model
  (define-fun Inv ((x!0 Int)) Bool
    (and (>= x!0 0) (<= x!0 10)))
)"#;
        let result = parse_spacer_response(output).expect("should parse");
        match result {
            SpacerResult::Sat { interpretations } => {
                assert_eq!(interpretations.len(), 1);
                assert_eq!(interpretations[0].name, "Inv");
                assert_eq!(interpretations[0].params, vec!["x!0"]);
                assert!(interpretations[0].body.contains(">="));
                assert!(interpretations[0].body.contains("<="));
            }
            other => panic!("expected Sat, got: {:?}", other),
        }
    }

    #[test]
    fn test_parse_spacer_response_unsat() {
        let result = parse_spacer_response("unsat\n").expect("should parse");
        assert_eq!(result, SpacerResult::Unsat);
    }

    #[test]
    fn test_parse_spacer_response_unknown() {
        let result = parse_spacer_response("unknown\ntimeout\n").expect("should parse");
        match result {
            SpacerResult::Unknown { reason } => {
                assert_eq!(reason, "timeout");
            }
            other => panic!("expected Unknown, got: {:?}", other),
        }
    }

    #[test]
    fn test_parse_spacer_response_empty() {
        let result = parse_spacer_response("");
        assert!(matches!(result, Err(CegarError::SolverError { .. })));
    }

    #[test]
    fn test_parse_spacer_response_simple_body() {
        let output = "sat\n(model\n  (define-fun P () Bool true)\n)";
        let result = parse_spacer_response(output).expect("should parse");
        match result {
            SpacerResult::Sat { interpretations } => {
                assert_eq!(interpretations.len(), 1);
                assert_eq!(interpretations[0].name, "P");
                assert_eq!(interpretations[0].body, "true");
            }
            other => panic!("expected Sat, got: {:?}", other),
        }
    }

    #[test]
    fn test_parse_spacer_response_multiple_predicates() {
        let output = r#"sat
(model
  (define-fun Inv1 ((x!0 Int)) Bool (>= x!0 0))
  (define-fun Inv2 ((y!0 Int)) Bool (<= y!0 100))
)"#;
        let result = parse_spacer_response(output).expect("should parse");
        match result {
            SpacerResult::Sat { interpretations } => {
                assert_eq!(interpretations.len(), 2);
                assert_eq!(interpretations[0].name, "Inv1");
                assert_eq!(interpretations[1].name, "Inv2");
            }
            other => panic!("expected Sat, got: {:?}", other),
        }
    }

    #[test]
    fn test_find_matching_paren() {
        assert_eq!(find_matching_paren("(abc)"), 5);
        assert_eq!(find_matching_paren("(a (b) c)"), 9);
        assert_eq!(find_matching_paren("((()))"), 6);
        assert_eq!(find_matching_paren("abc"), 0);
        assert_eq!(find_matching_paren("(unbalanced"), 0);
    }

    #[test]
    fn test_parse_params() {
        let params = parse_params("(x!0 Int) (y!0 Bool)");
        assert_eq!(params, vec!["x!0", "y!0"]);
    }

    #[test]
    fn test_parse_params_empty() {
        let params = parse_params("");
        assert!(params.is_empty());
    }

    #[test]
    fn test_spacer_config_default() {
        let config = SpacerConfig::default();
        assert_eq!(config.timeout_ms, 30_000);
        assert!(config.max_unfold.is_none());
    }

    #[test]
    fn test_spacer_config_to_smtlib2() {
        let config = SpacerConfig {
            timeout_ms: 5000,
            max_unfold: Some(20),
        };
        let opts = config.to_smtlib2_options();
        assert!(opts.contains("(set-option :timeout 5000)"));
        assert!(opts.contains("(set-option :fp.spacer.max_level 20)"));
    }

    #[test]
    fn test_app_to_smtlib_no_args() {
        let app = PredicateApp::new("P", vec![]);
        assert_eq!(app_to_smtlib(&app), "P");
    }

    #[test]
    fn test_app_to_smtlib_with_args() {
        let app = PredicateApp::new(
            "Inv",
            vec![
                Formula::Var("x".into(), Sort::Int),
                Formula::Int(5),
            ],
        );
        assert_eq!(app_to_smtlib(&app), "(Inv x 5)");
    }
}
