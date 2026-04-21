// trust-runtime/contract.rs: Design-by-contract runtime enforcement
//
// Converts verification conditions and spec suggestions into runtime contracts
// (preconditions, postconditions, invariants) and generates wrapper code for
// function-boundary enforcement.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;
use std::fmt::Write;

use serde::{Deserialize, Serialize};
use thiserror::Error;
use trust_types::SpecSuggestion;
use trust_types::fx::FxHashSet;

// ---------------------------------------------------------------------------
// ContractError
// ---------------------------------------------------------------------------

/// Errors from contract enforcement.
#[derive(Debug, Error)]
#[non_exhaustive]
#[allow(clippy::enum_variant_names)]
pub(crate) enum ContractError {
    /// A precondition was violated.
    #[error("precondition violated: {violation}")]
    PreconditionViolated { violation: ContractViolation },

    /// A postcondition was violated.
    #[error("postcondition violated: {violation}")]
    PostconditionViolated { violation: ContractViolation },

    /// An invariant was violated.
    #[error("invariant violated: {violation}")]
    InvariantViolated { violation: ContractViolation },
}

// ---------------------------------------------------------------------------
// ContractViolation
// ---------------------------------------------------------------------------

/// Details of a contract clause violation.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub(crate) struct ContractViolation {
    /// Which clause was violated (human-readable).
    pub clause: String,
    /// The actual value observed (stringified).
    pub actual: String,
    /// The expected constraint (stringified).
    pub expected: String,
    /// The function where the violation occurred.
    pub function: String,
}

impl std::fmt::Display for ContractViolation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "`{}` in `{}`: actual={}, expected={}",
            self.clause, self.function, self.actual, self.expected
        )
    }
}

// ---------------------------------------------------------------------------
// ContractClause
// ---------------------------------------------------------------------------

/// A single clause in a contract (precondition, postcondition, or invariant).
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub(crate) struct ContractClause {
    /// Human-readable description of the clause.
    pub description: String,
    /// The expression to evaluate (as a Rust expression string).
    pub expression: String,
    /// Variables referenced by this clause.
    pub variables: Vec<String>,
}

impl ContractClause {
    /// Construct a new clause.
    #[must_use]
    pub(crate) fn new(
        description: impl Into<String>,
        expression: impl Into<String>,
        variables: Vec<String>,
    ) -> Self {
        Self {
            description: description.into(),
            expression: expression.into(),
            variables,
        }
    }
}

// ---------------------------------------------------------------------------
// Contract
// ---------------------------------------------------------------------------

/// A design-by-contract specification for a function.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub(crate) struct Contract {
    /// The function this contract applies to.
    pub function: String,
    /// Preconditions that must hold before the function executes.
    pub preconditions: Vec<ContractClause>,
    /// Postconditions that must hold after the function returns.
    pub postconditions: Vec<ContractClause>,
    /// Invariants that must hold both before and after the function.
    pub invariants: Vec<ContractClause>,
}

impl Contract {
    /// Construct an empty contract for a function.
    #[must_use]
    pub(crate) fn new(function: impl Into<String>) -> Self {
        Self {
            function: function.into(),
            preconditions: Vec::new(),
            postconditions: Vec::new(),
            invariants: Vec::new(),
        }
    }

    /// Add a precondition clause.
    #[must_use]
    pub(crate) fn with_precondition(mut self, clause: ContractClause) -> Self {
        self.preconditions.push(clause);
        self
    }

    /// Add a postcondition clause.
    #[must_use]
    pub(crate) fn with_postcondition(mut self, clause: ContractClause) -> Self {
        self.postconditions.push(clause);
        self
    }

    /// Add an invariant clause.
    #[must_use]
    pub(crate) fn with_invariant(mut self, clause: ContractClause) -> Self {
        self.invariants.push(clause);
        self
    }

    /// Total number of clauses.
    #[must_use]
    pub(crate) fn clause_count(&self) -> usize {
        self.preconditions.len() + self.postconditions.len() + self.invariants.len()
    }

    /// True if the contract has no clauses.
    #[must_use]
    pub(crate) fn is_empty(&self) -> bool {
        self.clause_count() == 0
    }
}

// ---------------------------------------------------------------------------
// ContractEnforcer
// ---------------------------------------------------------------------------

/// Checks contracts at function boundaries using runtime state.
///
/// `args` and `state` are key-value maps of variable names to their
/// string-encoded runtime values.
pub(crate) struct ContractEnforcer;

impl ContractEnforcer {
    /// Check all preconditions of a contract against function arguments.
    ///
    /// Fail-closed: both `Fail` and `Unknown` clause results are treated as
    /// violations. Unknown means the clause could not be evaluated (missing
    /// variables or unrecognized expression), which is reported rather than
    /// silently passed.
    ///
    /// # Errors
    /// Returns `ContractError::PreconditionViolated` on the first failing
    /// or unevaluable clause.
    pub(crate) fn check_precondition(
        contract: &Contract,
        args: &FxHashMap<String, String>,
    ) -> Result<(), ContractError> {
        for clause in &contract.preconditions {
            if evaluate_clause(clause, args).is_violation() {
                return Err(ContractError::PreconditionViolated {
                    violation: ContractViolation {
                        clause: clause.description.clone(),
                        actual: format_state_for_clause(clause, args),
                        expected: clause.expression.clone(),
                        function: contract.function.clone(),
                    },
                });
            }
        }
        Ok(())
    }

    /// Check all postconditions of a contract against the result and old state.
    ///
    /// `result` contains the function return value(s). `old_state` contains
    /// values captured before the call (see `old_value_capture`).
    ///
    /// Fail-closed: `Unknown` clause results are treated as violations.
    ///
    /// # Errors
    /// Returns `ContractError::PostconditionViolated` on the first failing
    /// or unevaluable clause.
    pub(crate) fn check_postcondition(
        contract: &Contract,
        result: &FxHashMap<String, String>,
        old_state: &FxHashMap<String, String>,
    ) -> Result<(), ContractError> {
        // Merge old_state and result for evaluation; result takes precedence.
        let mut combined = old_state.clone();
        combined.extend(result.iter().map(|(k, v)| (k.clone(), v.clone())));

        for clause in &contract.postconditions {
            if evaluate_clause(clause, &combined).is_violation() {
                return Err(ContractError::PostconditionViolated {
                    violation: ContractViolation {
                        clause: clause.description.clone(),
                        actual: format_state_for_clause(clause, &combined),
                        expected: clause.expression.clone(),
                        function: contract.function.clone(),
                    },
                });
            }
        }
        Ok(())
    }

    /// Check all invariants of a contract against the current state.
    ///
    /// Fail-closed: `Unknown` clause results are treated as violations.
    ///
    /// # Errors
    /// Returns `ContractError::InvariantViolated` on the first failing
    /// or unevaluable clause.
    pub(crate) fn check_invariant(
        contract: &Contract,
        state: &FxHashMap<String, String>,
    ) -> Result<(), ContractError> {
        for clause in &contract.invariants {
            if evaluate_clause(clause, state).is_violation() {
                return Err(ContractError::InvariantViolated {
                    violation: ContractViolation {
                        clause: clause.description.clone(),
                        actual: format_state_for_clause(clause, state),
                        expected: clause.expression.clone(),
                        function: contract.function.clone(),
                    },
                });
            }
        }
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// Clause evaluation result (tri-state)
// ---------------------------------------------------------------------------

/// Result of evaluating a contract clause.
///
/// Fail-closed: callers should treat `Unknown` as a violation unless
/// explicitly configured for fail-open behavior.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ClauseResult {
    /// The clause condition held.
    Pass,
    /// The clause condition was violated.
    Fail,
    /// The clause could not be evaluated (unrecognized expression,
    /// missing variables, or unresolvable values).
    Unknown,
}

impl ClauseResult {
    /// Returns `true` only if the clause definitively passed.
    #[must_use]
    pub(crate) fn is_pass(self) -> bool {
        self == ClauseResult::Pass
    }

    /// Returns `true` if the clause failed or could not be evaluated.
    /// This is the fail-closed interpretation.
    #[must_use]
    pub(crate) fn is_violation(self) -> bool {
        self != ClauseResult::Pass
    }
}

// ---------------------------------------------------------------------------
// Clause evaluation
// ---------------------------------------------------------------------------

/// Evaluate a contract clause against runtime state.
///
/// Supports a small set of comparison operators in the expression string:
/// - `var > N`, `var >= N`, `var < N`, `var <= N`, `var == N`, `var != N`
/// - `var != 0` (nonzero check)
///
/// Returns `ClauseResult::Unknown` for unrecognized expressions or missing
/// variables (fail-closed: callers treat Unknown as a violation).
fn evaluate_clause(
    clause: &ContractClause,
    state: &FxHashMap<String, String>,
) -> ClauseResult {
    let expr = clause.expression.trim();

    // Try to parse simple binary comparisons: "lhs op rhs"
    for op in &[">=", "<=", "!=", "==", ">", "<"] {
        if let Some((lhs_str, rhs_str)) = expr.split_once(op) {
            let lhs_str = lhs_str.trim();
            let rhs_str = rhs_str.trim();

            let lhs_val = resolve_value(lhs_str, state);
            let rhs_val = resolve_value(rhs_str, state);

            match (lhs_val, rhs_val) {
                (Some(lhs), Some(rhs)) => {
                    let passed = match *op {
                        ">=" => lhs >= rhs,
                        "<=" => lhs <= rhs,
                        "!=" => lhs != rhs,
                        "==" => lhs == rhs,
                        ">" => lhs > rhs,
                        "<" => lhs < rhs,
                        _ => return ClauseResult::Unknown,
                    };
                    return if passed {
                        ClauseResult::Pass
                    } else {
                        ClauseResult::Fail
                    };
                }
                // Cannot resolve variables => Unknown (fail-closed).
                _ => return ClauseResult::Unknown,
            }
        }
    }

    // Expression not recognized => Unknown (fail-closed).
    ClauseResult::Unknown
}

/// Resolve a token as either a variable lookup or a literal integer.
fn resolve_value(token: &str, state: &FxHashMap<String, String>) -> Option<i64> {
    // Try as variable name first.
    if let Some(val_str) = state.get(token)
        && let Ok(v) = val_str.parse::<i64>() {
            return Some(v);
        }
    // Try as literal.
    token.parse::<i64>().ok()
}

/// Format state values for a clause's variables for diagnostics.
fn format_state_for_clause(
    clause: &ContractClause,
    state: &FxHashMap<String, String>,
) -> String {
    clause
        .variables
        .iter()
        .filter_map(|var| state.get(var).map(|val| format!("{var}={val}")))
        .collect::<Vec<_>>()
        .join(", ")
}

// ---------------------------------------------------------------------------
// Old-value capture
// ---------------------------------------------------------------------------

/// Determine which values need to be captured before a function call
/// for postcondition checking.
///
/// Returns pairs of (variable_name, capture_expression) where
/// `capture_expression` is a Rust expression to snapshot the value.
#[must_use]
pub(crate) fn old_value_capture(contract: &Contract) -> Vec<(String, String)> {
    let mut captures = Vec::new();
    let mut seen = FxHashSet::default();

    for clause in &contract.postconditions {
        for var in &clause.variables {
            // Variables prefixed with "old_" in postconditions indicate
            // values that need to be captured before the call.
            if var.starts_with("old_") && seen.insert(var.clone()) {
                let source_var = var.strip_prefix("old_").expect("invariant: starts_with checked");
                captures.push((
                    var.clone(),
                    format!("{source_var}.clone()"),
                ));
            }
        }
    }

    captures
}

// ---------------------------------------------------------------------------
// Code generation
// ---------------------------------------------------------------------------

/// Generate a Rust wrapper function that enforces the contract at function
/// boundaries.
///
/// `fn_sig` is the function signature (e.g., `fn safe_div(a: i32, b: i32) -> i32`).
#[must_use]
pub(crate) fn generate_contract_wrapper(fn_sig: &str, contract: &Contract) -> String {
    let mut code = String::new();

    let _ = writeln!(code, 
        "// tRust: Contract wrapper for `{}`",
        contract.function
    );
    code.push_str("#[cfg(trust_runtime)]\n");
    let _ = writeln!(code, "{fn_sig} {{");

    // Precondition checks.
    for (i, pre) in contract.preconditions.iter().enumerate() {
        let _ = writeln!(code, 
            "    // Precondition {}: {}",
            i, pre.description
        );
        let _ = writeln!(code, 
            "    assert!({}, \"tRust: precondition violated: {}\");",
            pre.expression,
            pre.description.replace('"', "\\\"")
        );
    }

    // Invariant checks (before).
    for (i, inv) in contract.invariants.iter().enumerate() {
        let _ = writeln!(code, 
            "    // Invariant {} (pre): {}",
            i, inv.description
        );
        let _ = writeln!(code, 
            "    assert!({}, \"tRust: invariant violated (pre): {}\");",
            inv.expression,
            inv.description.replace('"', "\\\"")
        );
    }

    // Old-value capture.
    let captures = old_value_capture(contract);
    for (var, expr) in &captures {
        let _ = writeln!(code, "    let {var} = {expr};");
    }

    // Call original function.
    let _ = write!(code, 
        "    let __trust_result = __trust_original_{}(",
        contract.function
    );
    // We leave argument forwarding as a placeholder since we don't parse fn_sig.
    code.push_str("/* args */);\n");

    // Postcondition checks.
    for (i, post) in contract.postconditions.iter().enumerate() {
        let _ = writeln!(code, 
            "    // Postcondition {}: {}",
            i, post.description
        );
        let _ = writeln!(code, 
            "    assert!({}, \"tRust: postcondition violated: {}\");",
            post.expression,
            post.description.replace('"', "\\\"")
        );
    }

    // Invariant checks (after).
    for (i, inv) in contract.invariants.iter().enumerate() {
        let _ = writeln!(code, 
            "    // Invariant {} (post): {}",
            i, inv.description
        );
        let _ = writeln!(code, 
            "    assert!({}, \"tRust: invariant violated (post): {}\");",
            inv.expression,
            inv.description.replace('"', "\\\"")
        );
    }

    code.push_str("    __trust_result\n");
    code.push_str("}\n");
    code
}

// ---------------------------------------------------------------------------
// Conversion from SpecSuggestion
// ---------------------------------------------------------------------------

/// Convert a `SpecSuggestion` from the strengthen phase into a runtime
/// `Contract`.
///
/// Extracts the liveness property and evidence from the suggestion to build
/// contract clauses. The property name becomes the contract function, and
/// each piece of evidence becomes a precondition clause.
#[must_use]
pub(crate) fn from_spec_suggestion(spec: &SpecSuggestion) -> Contract {
    let function_name = spec.id.clone();
    let mut contract = Contract::new(&function_name);

    // The liveness property predicate becomes a precondition.
    let pre = ContractClause::new(
        format!("liveness predicate: {}", spec.property.name),
        spec.property.predicate.clone(),
        vec![spec.property.predicate.clone()],
    );
    contract.preconditions.push(pre);

    // If there is a consequent, it becomes a postcondition.
    if let Some(consequent) = &spec.property.consequent {
        let post = ContractClause::new(
            format!("liveness consequent: {}", spec.property.name),
            consequent.clone(),
            vec![consequent.clone()],
        );
        contract.postconditions.push(post);
    }

    // Each fairness constraint becomes an invariant.
    for fairness in &spec.property.fairness {
        let (desc, vars) = match fairness {
            trust_types::FairnessConstraint::Weak { action, vars } => {
                (format!("weak fairness: {action}"), vars.clone())
            }
            trust_types::FairnessConstraint::Strong { action, vars } => {
                (format!("strong fairness: {action}"), vars.clone())
            }
            _ => continue,
        };
        if let Some(first_var) = vars.first() {
            let inv = ContractClause::new(
                desc,
                format!("{first_var} >= 0"),
                vars,
            );
            contract.invariants.push(inv);
        }
    }

    contract
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn state(pairs: &[(&str, &str)]) -> FxHashMap<String, String> {
        pairs
            .iter()
            .map(|(k, v)| (k.to_string(), v.to_string()))
            .collect()
    }

    fn simple_contract() -> Contract {
        Contract::new("safe_div")
            .with_precondition(ContractClause::new(
                "divisor must be nonzero",
                "b != 0",
                vec!["b".to_string()],
            ))
            .with_postcondition(ContractClause::new(
                "result times divisor equals dividend",
                "result <= a",
                vec!["result".to_string(), "a".to_string(), "old_a".to_string()],
            ))
            .with_invariant(ContractClause::new(
                "divisor range",
                "b > 0",
                vec!["b".to_string()],
            ))
    }

    // -----------------------------------------------------------------------
    // Contract construction
    // -----------------------------------------------------------------------

    #[test]
    fn test_contract_new_is_empty() {
        let c = Contract::new("f");
        assert!(c.is_empty());
        assert_eq!(c.clause_count(), 0);
        assert_eq!(c.function, "f");
    }

    #[test]
    fn test_contract_builder() {
        let c = simple_contract();
        assert_eq!(c.function, "safe_div");
        assert_eq!(c.preconditions.len(), 1);
        assert_eq!(c.postconditions.len(), 1);
        assert_eq!(c.invariants.len(), 1);
        assert_eq!(c.clause_count(), 3);
        assert!(!c.is_empty());
    }

    // -----------------------------------------------------------------------
    // Precondition checking
    // -----------------------------------------------------------------------

    #[test]
    fn test_check_precondition_pass() {
        let c = simple_contract();
        let args = state(&[("b", "5")]);
        ContractEnforcer::check_precondition(&c, &args).expect("should pass");
    }

    #[test]
    fn test_check_precondition_fail() {
        let c = simple_contract();
        let args = state(&[("b", "0")]);
        let err = ContractEnforcer::check_precondition(&c, &args).unwrap_err();
        assert!(matches!(err, ContractError::PreconditionViolated { .. }));
        let msg = format!("{err}");
        assert!(msg.contains("precondition violated"));
    }

    #[test]
    fn test_check_precondition_missing_variable_fails_closed() {
        let c = simple_contract();
        let args = state(&[]); // missing 'b'
        // Missing variable => Unknown => fail-closed (treated as violation).
        let err = ContractEnforcer::check_precondition(&c, &args).unwrap_err();
        assert!(matches!(err, ContractError::PreconditionViolated { .. }));
    }

    #[test]
    fn test_check_precondition_empty_contract() {
        let c = Contract::new("f");
        let args = state(&[]);
        ContractEnforcer::check_precondition(&c, &args).expect("empty contract always passes");
    }

    // -----------------------------------------------------------------------
    // Postcondition checking
    // -----------------------------------------------------------------------

    #[test]
    fn test_check_postcondition_pass() {
        let c = simple_contract();
        let result = state(&[("result", "3")]);
        let old = state(&[("a", "10")]);
        ContractEnforcer::check_postcondition(&c, &result, &old).expect("should pass");
    }

    #[test]
    fn test_check_postcondition_fail() {
        let c = simple_contract();
        let result = state(&[("result", "20")]);
        let old = state(&[("a", "10")]);
        let err = ContractEnforcer::check_postcondition(&c, &result, &old).unwrap_err();
        assert!(matches!(err, ContractError::PostconditionViolated { .. }));
    }

    #[test]
    fn test_check_postcondition_result_overrides_old() {
        // If result has key 'a', it overrides old_state's 'a'.
        let c = Contract::new("f").with_postcondition(ContractClause::new(
            "check a",
            "a > 0",
            vec!["a".to_string()],
        ));
        let result = state(&[("a", "5")]);
        let old = state(&[("a", "-1")]);
        ContractEnforcer::check_postcondition(&c, &result, &old).expect("result should override");
    }

    // -----------------------------------------------------------------------
    // Invariant checking
    // -----------------------------------------------------------------------

    #[test]
    fn test_check_invariant_pass() {
        let c = simple_contract();
        let s = state(&[("b", "5")]);
        ContractEnforcer::check_invariant(&c, &s).expect("should pass");
    }

    #[test]
    fn test_check_invariant_fail() {
        let c = simple_contract();
        let s = state(&[("b", "-3")]);
        let err = ContractEnforcer::check_invariant(&c, &s).unwrap_err();
        assert!(matches!(err, ContractError::InvariantViolated { .. }));
    }

    // -----------------------------------------------------------------------
    // Clause evaluation: comparison operators
    // -----------------------------------------------------------------------

    #[test]
    fn test_evaluate_clause_gt() {
        let clause = ContractClause::new("x > 5", "x > 5", vec!["x".to_string()]);
        let s = state(&[("x", "10")]);
        assert_eq!(evaluate_clause(&clause, &s), ClauseResult::Pass);

        let s = state(&[("x", "3")]);
        assert_eq!(evaluate_clause(&clause, &s), ClauseResult::Fail);
    }

    #[test]
    fn test_evaluate_clause_ge() {
        let clause = ContractClause::new("x >= 5", "x >= 5", vec!["x".to_string()]);
        let s = state(&[("x", "5")]);
        assert_eq!(evaluate_clause(&clause, &s), ClauseResult::Pass);
    }

    #[test]
    fn test_evaluate_clause_lt() {
        let clause = ContractClause::new("x < 5", "x < 5", vec!["x".to_string()]);
        let s = state(&[("x", "3")]);
        assert_eq!(evaluate_clause(&clause, &s), ClauseResult::Pass);
    }

    #[test]
    fn test_evaluate_clause_le() {
        let clause = ContractClause::new("x <= 5", "x <= 5", vec!["x".to_string()]);
        let s = state(&[("x", "5")]);
        assert_eq!(evaluate_clause(&clause, &s), ClauseResult::Pass);
    }

    #[test]
    fn test_evaluate_clause_eq() {
        let clause = ContractClause::new("x == 5", "x == 5", vec!["x".to_string()]);
        let s = state(&[("x", "5")]);
        assert_eq!(evaluate_clause(&clause, &s), ClauseResult::Pass);

        let s = state(&[("x", "6")]);
        assert_eq!(evaluate_clause(&clause, &s), ClauseResult::Fail);
    }

    #[test]
    fn test_evaluate_clause_ne() {
        let clause = ContractClause::new("x != 0", "x != 0", vec!["x".to_string()]);
        let s = state(&[("x", "5")]);
        assert_eq!(evaluate_clause(&clause, &s), ClauseResult::Pass);

        let s = state(&[("x", "0")]);
        assert_eq!(evaluate_clause(&clause, &s), ClauseResult::Fail);
    }

    #[test]
    fn test_evaluate_clause_var_vs_var() {
        let clause = ContractClause::new(
            "index < len",
            "index < len",
            vec!["index".to_string(), "len".to_string()],
        );
        let s = state(&[("index", "3"), ("len", "10")]);
        assert_eq!(evaluate_clause(&clause, &s), ClauseResult::Pass);

        let s = state(&[("index", "10"), ("len", "5")]);
        assert_eq!(evaluate_clause(&clause, &s), ClauseResult::Fail);
    }

    #[test]
    fn test_evaluate_clause_unrecognized_expression_returns_unknown() {
        let clause = ContractClause::new("complex", "foo(x, y)", vec![]);
        let s = state(&[]);
        // Unrecognized => Unknown (fail-closed).
        assert_eq!(evaluate_clause(&clause, &s), ClauseResult::Unknown);
    }

    #[test]
    fn test_evaluate_clause_missing_variable_returns_unknown() {
        let clause = ContractClause::new("x > 5", "x > 5", vec!["x".to_string()]);
        let s = state(&[]); // missing 'x'
        // Missing variable => Unknown (fail-closed).
        assert_eq!(evaluate_clause(&clause, &s), ClauseResult::Unknown);
    }

    // -----------------------------------------------------------------------
    // ContractViolation
    // -----------------------------------------------------------------------

    #[test]
    fn test_violation_display() {
        let v = ContractViolation {
            clause: "x > 0".to_string(),
            actual: "x=-1".to_string(),
            expected: "x > 0".to_string(),
            function: "f".to_string(),
        };
        let msg = format!("{v}");
        assert!(msg.contains("`x > 0`"));
        assert!(msg.contains("`f`"));
        assert!(msg.contains("actual=x=-1"));
    }

    // -----------------------------------------------------------------------
    // Old-value capture
    // -----------------------------------------------------------------------

    #[test]
    fn test_old_value_capture() {
        let c = Contract::new("f")
            .with_postcondition(ContractClause::new(
                "result >= old_x",
                "result >= old_x",
                vec!["result".to_string(), "old_x".to_string()],
            ))
            .with_postcondition(ContractClause::new(
                "old_y unchanged",
                "old_y == y",
                vec!["old_y".to_string(), "y".to_string()],
            ));

        let captures = old_value_capture(&c);
        assert_eq!(captures.len(), 2);
        assert_eq!(captures[0].0, "old_x");
        assert_eq!(captures[0].1, "x.clone()");
        assert_eq!(captures[1].0, "old_y");
        assert_eq!(captures[1].1, "y.clone()");
    }

    #[test]
    fn test_old_value_capture_no_duplicates() {
        let c = Contract::new("f")
            .with_postcondition(ContractClause::new(
                "check1",
                "old_x >= 0",
                vec!["old_x".to_string()],
            ))
            .with_postcondition(ContractClause::new(
                "check2",
                "result > old_x",
                vec!["result".to_string(), "old_x".to_string()],
            ));

        let captures = old_value_capture(&c);
        assert_eq!(captures.len(), 1); // old_x appears only once
    }

    #[test]
    fn test_old_value_capture_empty() {
        let c = Contract::new("f").with_postcondition(ContractClause::new(
            "no old values",
            "result > 0",
            vec!["result".to_string()],
        ));

        let captures = old_value_capture(&c);
        assert!(captures.is_empty());
    }

    // -----------------------------------------------------------------------
    // Code generation
    // -----------------------------------------------------------------------

    #[test]
    fn test_generate_contract_wrapper() {
        let c = simple_contract();
        let code = generate_contract_wrapper("fn safe_div(a: i32, b: i32) -> i32", &c);

        assert!(code.contains("#[cfg(trust_runtime)]"));
        assert!(code.contains("fn safe_div(a: i32, b: i32) -> i32"));
        assert!(code.contains("precondition"));
        assert!(code.contains("b != 0"));
        assert!(code.contains("postcondition"));
        assert!(code.contains("invariant"));
        assert!(code.contains("__trust_result"));
        assert!(code.contains("__trust_original_safe_div"));
    }

    #[test]
    fn test_generate_contract_wrapper_empty_contract() {
        let c = Contract::new("f");
        let code = generate_contract_wrapper("fn f()", &c);
        assert!(code.contains("fn f()"));
        assert!(code.contains("__trust_result"));
        // No assert! lines for empty contract.
        assert!(!code.contains("precondition violated"));
    }

    #[test]
    fn test_generate_contract_wrapper_old_capture() {
        let c = Contract::new("inc")
            .with_postcondition(ContractClause::new(
                "increased",
                "result > old_x",
                vec!["result".to_string(), "old_x".to_string()],
            ));
        let code = generate_contract_wrapper("fn inc(x: i32) -> i32", &c);
        assert!(code.contains("let old_x = x.clone()"));
    }

    // -----------------------------------------------------------------------
    // from_spec_suggestion
    // -----------------------------------------------------------------------

    #[test]
    fn test_from_spec_suggestion_basic() {
        let spec = SpecSuggestion::new(
            "request_responds",
            trust_types::LivenessProperty {
                name: "request_responds".into(),
                operator: trust_types::TemporalOperator::LeadsTo,
                predicate: "request".into(),
                consequent: Some("response".into()),
                fairness: vec![],
            },
            0.9,
            vec!["matched pattern".into()],
            trust_types::PatternKind::request_response(),
            None,
        );

        let c = from_spec_suggestion(&spec);
        assert_eq!(c.function, "request_responds");
        assert_eq!(c.preconditions.len(), 1);
        assert!(c.preconditions[0].description.contains("request_responds"));
        assert_eq!(c.postconditions.len(), 1);
        assert!(c.postconditions[0].expression.contains("response"));
    }

    #[test]
    fn test_from_spec_suggestion_no_consequent() {
        let spec = SpecSuggestion::new(
            "eventually_idle",
            trust_types::LivenessProperty {
                name: "eventually_idle".into(),
                operator: trust_types::TemporalOperator::Eventually,
                predicate: "idle".into(),
                consequent: None,
                fairness: vec![],
            },
            0.85,
            vec![],
            trust_types::PatternKind::connection_pool(),
            None,
        );

        let c = from_spec_suggestion(&spec);
        assert_eq!(c.preconditions.len(), 1);
        assert!(c.postconditions.is_empty());
    }

    #[test]
    fn test_from_spec_suggestion_with_fairness() {
        let spec = SpecSuggestion::new(
            "consume_fair",
            trust_types::LivenessProperty {
                name: "consume_fair".into(),
                operator: trust_types::TemporalOperator::LeadsTo,
                predicate: "produce".into(),
                consequent: Some("consume".into()),
                fairness: vec![
                    trust_types::FairnessConstraint::Weak {
                        action: "consume".into(),
                        vars: vec!["buffer".into(), "count".into()],
                    },
                    trust_types::FairnessConstraint::Strong {
                        action: "drain".into(),
                        vars: vec!["queue".into()],
                    },
                ],
            },
            0.8,
            vec![],
            trust_types::PatternKind::producer_consumer(),
            None,
        );

        let c = from_spec_suggestion(&spec);
        assert_eq!(c.invariants.len(), 2);
        assert!(c.invariants[0].description.contains("weak fairness"));
        assert!(c.invariants[1].description.contains("strong fairness"));
        assert_eq!(c.invariants[0].variables, vec!["buffer", "count"]);
    }

    // -----------------------------------------------------------------------
    // Serialization
    // -----------------------------------------------------------------------

    #[test]
    fn test_contract_serialization_roundtrip() {
        let c = simple_contract();
        let json = serde_json::to_string(&c).expect("serialize");
        let roundtrip: Contract = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(roundtrip, c);
    }

    #[test]
    fn test_violation_serialization_roundtrip() {
        let v = ContractViolation {
            clause: "x > 0".to_string(),
            actual: "x=-1".to_string(),
            expected: "x > 0".to_string(),
            function: "f".to_string(),
        };
        let json = serde_json::to_string(&v).expect("serialize");
        let roundtrip: ContractViolation = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(roundtrip, v);
    }

    #[test]
    fn test_clause_serialization_roundtrip() {
        let clause = ContractClause::new("test", "x > 0", vec!["x".to_string()]);
        let json = serde_json::to_string(&clause).expect("serialize");
        let roundtrip: ContractClause = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(roundtrip, clause);
    }
}
