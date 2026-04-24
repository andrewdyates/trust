// trust-cegar: Predicate abstraction refinement for CEGAR loops
//
// Discovers new predicates from spurious counterexamples. Implements the
// refinement half of the CEGAR cycle: given a spurious counterexample path,
// extract predicates that distinguish the spurious path from feasible ones.
//
// Reference: CPAchecker's predicate refinement
//   refs/cpachecker/src/org/sosy_lab/cpachecker/cpa/predicate/
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;

use serde::{Deserialize, Serialize};

/// A predicate over program state used in predicate abstraction.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Predicate {
    /// Unique identifier for this predicate.
    pub id: usize,
    /// String expression representing the predicate (e.g., "x > 0").
    pub expression: String,
    /// Variables referenced by this predicate.
    pub variables: Vec<String>,
}

/// A collection of predicates used for abstraction.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PredicateSet {
    /// The predicates in this set.
    pub predicates: Vec<Predicate>,
}

impl PredicateSet {
    /// Create an empty predicate set.
    #[must_use]
    pub fn new() -> Self {
        Self { predicates: Vec::new() }
    }

    /// Number of predicates in this set.
    #[must_use]
    pub fn len(&self) -> usize {
        self.predicates.len()
    }

    /// Whether this set is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.predicates.is_empty()
    }

    /// Add a predicate to the set if it is not already present (by expression).
    pub fn add(&mut self, predicate: Predicate) {
        if !self.predicates.iter().any(|p| p.expression == predicate.expression) {
            self.predicates.push(predicate);
        }
    }

    /// Check whether a predicate with the given expression exists.
    #[must_use]
    pub fn contains_expression(&self, expr: &str) -> bool {
        self.predicates.iter().any(|p| p.expression == expr)
    }
}

impl Default for PredicateSet {
    fn default() -> Self {
        Self::new()
    }
}

/// Abstract state: a valuation of predicates.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AbstractionState {
    /// Map from predicate id to its Boolean valuation.
    pub predicate_values: FxHashMap<usize, bool>,
    /// Whether this state represents an error location.
    pub is_error: bool,
}

impl AbstractionState {
    /// Create a new non-error abstraction state with no predicate valuations.
    #[must_use]
    pub fn new() -> Self {
        Self { predicate_values: FxHashMap::default(), is_error: false }
    }

    /// Number of predicates evaluated in this state.
    #[must_use]
    pub fn num_evaluated(&self) -> usize {
        self.predicate_values.len()
    }

    /// Get the valuation of a specific predicate, if evaluated.
    #[must_use]
    pub fn get(&self, predicate_id: usize) -> Option<bool> {
        self.predicate_values.get(&predicate_id).copied()
    }
}

impl Default for AbstractionState {
    fn default() -> Self {
        Self::new()
    }
}

/// A spurious counterexample discovered during CEGAR.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SpuriousCex {
    /// Sequence of program locations (e.g., basic block names) along the path.
    pub path: Vec<String>,
    /// Description of the failing state at the end of the path.
    pub failing_state: String,
    /// Reason the counterexample was determined to be spurious.
    pub reason: String,
}

/// Result of a predicate refinement step.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RefinementResult {
    /// Newly discovered predicates.
    pub new_predicates: Vec<Predicate>,
    /// Number of predicates removed during minimization.
    pub predicates_removed: usize,
    /// Number of refinement iterations performed.
    pub iterations: usize,
    /// Whether refinement converged (no more predicates to add).
    pub converged: bool,
}

/// Predicate discovery engine: extracts and refines predicates from
/// spurious counterexamples in a CEGAR loop.
#[derive(Debug, Clone)]
pub struct PredicateDiscovery {
    /// Counter for generating unique predicate IDs.
    next_id: usize,
}

impl PredicateDiscovery {
    /// Create a new predicate discovery engine.
    #[must_use]
    pub fn new() -> Self {
        Self { next_id: 0 }
    }

    /// Abstract a concrete state description into a predicate valuation.
    ///
    /// Evaluates each predicate in the set against the concrete state and
    /// returns the resulting abstract state.
    #[must_use]
    pub fn abstract_state(
        &self,
        concrete_state: &str,
        predicates: &PredicateSet,
    ) -> AbstractionState {
        let mut state = AbstractionState::new();
        for pred in &predicates.predicates {
            if let Some(val) = self.evaluate_predicate(pred, concrete_state) {
                state.predicate_values.insert(pred.id, val);
            }
        }
        // Mark error if the concrete state contains "error" or "panic"
        state.is_error = concrete_state.contains("error") || concrete_state.contains("panic");
        state
    }

    /// Check whether a path through the abstract model is feasible.
    ///
    /// A path is feasible if there exists a concrete execution that follows it.
    /// Returns `true` if feasible, `false` if spurious.
    #[must_use]
    pub fn check_feasibility(&self, path: &[String]) -> bool {
        // A path with an "unreachable" step is infeasible
        if path.iter().any(|step| step.contains("unreachable")) {
            return false;
        }
        // A path with contradictory conditions is infeasible
        for step in path {
            if step.contains("contradiction") {
                return false;
            }
        }
        // Empty paths are trivially feasible
        if path.is_empty() {
            return true;
        }
        // Default: assume feasible (real implementation would query SMT solver)
        true
    }

    /// Refine predicates based on a spurious counterexample.
    ///
    /// Extracts new predicates from the counterexample, adds them to the
    /// current set, and minimizes the result.
    pub fn refine_predicates(&self, cex: &SpuriousCex, current: &PredicateSet) -> RefinementResult {
        let new_preds = self.extract_predicates_from_cex(cex);
        let mut combined = current.clone();
        let _initial_count = combined.len();

        for pred in &new_preds {
            combined.add(pred.clone());
        }

        let minimized = self.minimize_predicate_set(&combined);
        let predicates_removed = combined.len().saturating_sub(minimized.len());

        let actually_new: Vec<Predicate> =
            new_preds.into_iter().filter(|p| !current.contains_expression(&p.expression)).collect();

        let converged = actually_new.is_empty();

        RefinementResult {
            new_predicates: actually_new,
            predicates_removed,
            iterations: if converged { 0 } else { 1 },
            converged,
        }
    }

    /// Extract predicates from a spurious counterexample.
    ///
    /// Analyzes the path and failing state to discover predicates that
    /// distinguish the spurious path from feasible executions.
    #[must_use]
    pub fn extract_predicates_from_cex(&self, cex: &SpuriousCex) -> Vec<Predicate> {
        let mut predicates = Vec::new();
        let mut id = self.next_id;

        // Extract predicates from path conditions
        for step in &cex.path {
            if let Some(pred) = self.predicate_from_path_step(step, &mut id) {
                predicates.push(pred);
            }
        }

        // Extract predicates from the failing state
        for token in cex.failing_state.split_whitespace() {
            if token.contains('=') || token.contains('<') || token.contains('>') {
                let vars = extract_variable_names(token);
                if !vars.is_empty() {
                    predicates.push(Predicate {
                        id,
                        expression: token.to_string(),
                        variables: vars,
                    });
                    id += 1;
                }
            }
        }

        // Extract from reason if it contains variable conditions
        if cex.reason.contains("!=") || cex.reason.contains("==") {
            let vars = extract_variable_names(&cex.reason);
            if !vars.is_empty() {
                predicates.push(Predicate { id, expression: cex.reason.clone(), variables: vars });
            }
        }

        predicates
    }

    /// Minimize a predicate set by removing redundant predicates.
    ///
    /// Two predicates are considered redundant if they reference the exact
    /// same set of variables and have the same expression (deduplication).
    #[must_use]
    pub fn minimize_predicate_set(&self, predicates: &PredicateSet) -> PredicateSet {
        let mut seen_expressions: Vec<String> = Vec::new();
        let mut minimized = PredicateSet::new();

        for pred in &predicates.predicates {
            if !seen_expressions.contains(&pred.expression) {
                seen_expressions.push(pred.expression.clone());
                minimized.predicates.push(pred.clone());
            }
        }

        minimized
    }

    /// Evaluate a predicate against a concrete state description.
    ///
    /// Returns `Some(true)` if the predicate holds, `Some(false)` if it
    /// does not, and `None` if evaluation is indeterminate.
    #[must_use]
    pub fn evaluate_predicate(&self, predicate: &Predicate, state: &str) -> Option<bool> {
        // Check if all variables in the predicate are mentioned in the state
        let all_present = predicate.variables.iter().all(|v| state.contains(v.as_str()));
        if !all_present {
            return None;
        }

        // Simple heuristic evaluation for common patterns
        if let Some(val) = try_evaluate_comparison(&predicate.expression, state) {
            return Some(val);
        }

        // If the state explicitly contains the predicate expression, it holds
        if state.contains(&predicate.expression) {
            return Some(true);
        }

        None
    }

    /// Check whether a counterexample path is spurious (infeasible).
    #[must_use]
    pub fn is_spurious(&self, path: &[String]) -> bool {
        !self.check_feasibility(path)
    }

    /// Extract a predicate from a single path step, if it contains a condition.
    fn predicate_from_path_step(&self, step: &str, id: &mut usize) -> Option<Predicate> {
        // Look for comparison patterns in the step
        let operators = [">=", "<=", "!=", "==", ">", "<"];
        for op in &operators {
            if step.contains(op) {
                let vars = extract_variable_names(step);
                if !vars.is_empty() {
                    let pred = Predicate { id: *id, expression: step.to_string(), variables: vars };
                    *id += 1;
                    return Some(pred);
                }
            }
        }
        None
    }
}

impl Default for PredicateDiscovery {
    fn default() -> Self {
        Self::new()
    }
}

/// Extract variable-like identifiers from a string expression.
///
/// Identifies tokens that look like variable names: start with a letter or
/// underscore and contain only alphanumeric characters and underscores.
fn extract_variable_names(expr: &str) -> Vec<String> {
    let mut vars = Vec::new();
    let mut current = String::new();

    for ch in expr.chars() {
        if ch.is_alphanumeric() || ch == '_' {
            current.push(ch);
        } else {
            if !current.is_empty() && is_variable_name(&current) {
                vars.push(current.clone());
            }
            current.clear();
        }
    }
    if !current.is_empty() && is_variable_name(&current) {
        vars.push(current);
    }

    vars.sort();
    vars.dedup();
    vars
}

/// Check if a token looks like a variable name (starts with letter/underscore,
/// not a pure number, not a keyword).
fn is_variable_name(token: &str) -> bool {
    let first = match token.chars().next() {
        Some(c) => c,
        None => return false,
    };
    if !first.is_alphabetic() && first != '_' {
        return false;
    }
    // Filter out common non-variable tokens
    !matches!(
        token,
        "true" | "false" | "if" | "else" | "while" | "for" | "let" | "mut" | "fn" | "return"
    )
}

/// Try to evaluate a simple comparison expression against a concrete state.
///
/// Handles patterns like "x > 0" when the state contains "x = 5".
fn try_evaluate_comparison(expr: &str, state: &str) -> Option<bool> {
    // Parse "var op value" pattern
    let operators = [
        (">=", Ordering::GtEq),
        ("<=", Ordering::LtEq),
        ("!=", Ordering::NotEq),
        ("==", Ordering::Eq),
        (">", Ordering::Gt),
        ("<", Ordering::Lt),
    ];

    for (op_str, op) in &operators {
        if let Some(pos) = expr.find(op_str) {
            let lhs = expr[..pos].trim();
            let rhs = expr[pos + op_str.len()..].trim();

            // Try to find the value of lhs in the state
            let lhs_val = find_value_in_state(lhs, state)?;
            let rhs_val: i64 = rhs.parse().ok()?;

            return Some(match op {
                Ordering::Lt => lhs_val < rhs_val,
                Ordering::LtEq => lhs_val <= rhs_val,
                Ordering::Gt => lhs_val > rhs_val,
                Ordering::GtEq => lhs_val >= rhs_val,
                Ordering::Eq => lhs_val == rhs_val,
                Ordering::NotEq => lhs_val != rhs_val,
            });
        }
    }
    None
}

/// Comparison ordering for predicate evaluation.
#[derive(Debug, Clone, Copy)]
enum Ordering {
    Lt,
    LtEq,
    Gt,
    GtEq,
    Eq,
    NotEq,
}

/// Find the integer value of a variable in a state description.
///
/// Looks for patterns like "var = N" or "var=N" in the state string.
fn find_value_in_state(var: &str, state: &str) -> Option<i64> {
    // Look for "var = N" or "var=N"
    let patterns = [format!("{var} = "), format!("{var}=")];
    for pat in &patterns {
        if let Some(pos) = state.find(pat.as_str()) {
            let after = &state[pos + pat.len()..];
            let num_str: String =
                after.chars().take_while(|c| c.is_ascii_digit() || *c == '-').collect();
            if let Ok(val) = num_str.parse::<i64>() {
                return Some(val);
            }
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_predicate_creation() {
        let pred =
            Predicate { id: 0, expression: "x > 0".to_string(), variables: vec!["x".to_string()] };
        assert_eq!(pred.id, 0);
        assert_eq!(pred.expression, "x > 0");
        assert_eq!(pred.variables, vec!["x"]);
    }

    #[test]
    fn test_predicate_set_new_is_empty() {
        let set = PredicateSet::new();
        assert!(set.is_empty());
        assert_eq!(set.len(), 0);
    }

    #[test]
    fn test_predicate_set_add_and_dedup() {
        let mut set = PredicateSet::new();
        let p1 =
            Predicate { id: 0, expression: "x > 0".to_string(), variables: vec!["x".to_string()] };
        let p2 = Predicate {
            id: 1,
            expression: "x > 0".to_string(), // duplicate expression
            variables: vec!["x".to_string()],
        };
        let p3 =
            Predicate { id: 2, expression: "y < 10".to_string(), variables: vec!["y".to_string()] };

        set.add(p1);
        set.add(p2); // should be ignored
        set.add(p3);

        assert_eq!(set.len(), 2);
        assert!(set.contains_expression("x > 0"));
        assert!(set.contains_expression("y < 10"));
        assert!(!set.contains_expression("z == 0"));
    }

    #[test]
    fn test_abstraction_state_default() {
        let state = AbstractionState::new();
        assert!(!state.is_error);
        assert_eq!(state.num_evaluated(), 0);
        assert_eq!(state.get(0), None);
    }

    #[test]
    fn test_abstraction_state_with_values() {
        let mut state = AbstractionState::new();
        state.predicate_values.insert(0, true);
        state.predicate_values.insert(1, false);

        assert_eq!(state.num_evaluated(), 2);
        assert_eq!(state.get(0), Some(true));
        assert_eq!(state.get(1), Some(false));
        assert_eq!(state.get(2), None);
    }

    #[test]
    fn test_spurious_cex_creation() {
        let cex = SpuriousCex {
            path: vec!["bb0".to_string(), "bb1".to_string(), "bb2".to_string()],
            failing_state: "x=0 y=-1".to_string(),
            reason: "path condition unsatisfiable".to_string(),
        };
        assert_eq!(cex.path.len(), 3);
        assert_eq!(cex.failing_state, "x=0 y=-1");
    }

    #[test]
    fn test_check_feasibility_empty_path() {
        let disc = PredicateDiscovery::new();
        assert!(disc.check_feasibility(&[]));
    }

    #[test]
    fn test_check_feasibility_unreachable() {
        let disc = PredicateDiscovery::new();
        let path = vec!["bb0".to_string(), "unreachable".to_string()];
        assert!(!disc.check_feasibility(&path));
    }

    #[test]
    fn test_check_feasibility_contradiction() {
        let disc = PredicateDiscovery::new();
        let path = vec!["bb0".to_string(), "contradiction: x > 0 && x < 0".to_string()];
        assert!(!disc.check_feasibility(&path));
    }

    #[test]
    fn test_check_feasibility_normal_path() {
        let disc = PredicateDiscovery::new();
        let path = vec!["bb0".to_string(), "bb1".to_string()];
        assert!(disc.check_feasibility(&path));
    }

    #[test]
    fn test_is_spurious_inverse_of_feasibility() {
        let disc = PredicateDiscovery::new();
        let feasible = vec!["bb0".to_string()];
        let infeasible = vec!["unreachable".to_string()];

        assert!(!disc.is_spurious(&feasible));
        assert!(disc.is_spurious(&infeasible));
    }

    #[test]
    fn test_abstract_state_evaluates_predicates() {
        let disc = PredicateDiscovery::new();
        let mut set = PredicateSet::new();
        set.add(Predicate {
            id: 0,
            expression: "x > 0".to_string(),
            variables: vec!["x".to_string()],
        });
        set.add(Predicate {
            id: 1,
            expression: "y < 10".to_string(),
            variables: vec!["y".to_string()],
        });

        let state = disc.abstract_state("x = 5, y = 3", &set);
        assert_eq!(state.get(0), Some(true)); // x=5 > 0
        assert_eq!(state.get(1), Some(true)); // y=3 < 10
        assert!(!state.is_error);
    }

    #[test]
    fn test_abstract_state_error_detection() {
        let disc = PredicateDiscovery::new();
        let set = PredicateSet::new();

        let state = disc.abstract_state("error: index out of bounds", &set);
        assert!(state.is_error);

        let state2 = disc.abstract_state("panic at line 42", &set);
        assert!(state2.is_error);

        let state3 = disc.abstract_state("x = 5", &set);
        assert!(!state3.is_error);
    }

    #[test]
    fn test_extract_predicates_from_cex_path_conditions() {
        let disc = PredicateDiscovery::new();
        let cex = SpuriousCex {
            path: vec![
                "x > 0".to_string(),
                "y <= 10".to_string(),
                "bb3".to_string(), // no condition
            ],
            failing_state: String::new(),
            reason: String::new(),
        };

        let preds = disc.extract_predicates_from_cex(&cex);
        assert!(preds.len() >= 2);
        assert!(preds.iter().any(|p| p.expression == "x > 0"));
        assert!(preds.iter().any(|p| p.expression == "y <= 10"));
    }

    #[test]
    fn test_extract_predicates_from_cex_failing_state() {
        let disc = PredicateDiscovery::new();
        let cex = SpuriousCex {
            path: Vec::new(),
            failing_state: "x=0 y<10".to_string(),
            reason: String::new(),
        };

        let preds = disc.extract_predicates_from_cex(&cex);
        assert!(!preds.is_empty());
    }

    #[test]
    fn test_extract_predicates_from_cex_reason() {
        let disc = PredicateDiscovery::new();
        let cex = SpuriousCex {
            path: Vec::new(),
            failing_state: String::new(),
            reason: "x != y implies divergence".to_string(),
        };

        let preds = disc.extract_predicates_from_cex(&cex);
        assert!(!preds.is_empty());
        assert!(preds.iter().any(|p| p.expression.contains("!=")));
    }

    #[test]
    fn test_minimize_predicate_set_removes_duplicates() {
        let disc = PredicateDiscovery::new();
        let set = PredicateSet {
            predicates: vec![
                Predicate {
                    id: 0,
                    expression: "x > 0".to_string(),
                    variables: vec!["x".to_string()],
                },
                Predicate {
                    id: 1,
                    expression: "x > 0".to_string(),
                    variables: vec!["x".to_string()],
                },
                Predicate {
                    id: 2,
                    expression: "y < 5".to_string(),
                    variables: vec!["y".to_string()],
                },
            ],
        };

        let minimized = disc.minimize_predicate_set(&set);
        assert_eq!(minimized.len(), 2);
    }

    #[test]
    fn test_refine_predicates_adds_new() {
        let disc = PredicateDiscovery::new();
        let current = PredicateSet::new();
        let cex = SpuriousCex {
            path: vec!["x > 0".to_string()],
            failing_state: String::new(),
            reason: String::new(),
        };

        let result = disc.refine_predicates(&cex, &current);
        assert!(!result.new_predicates.is_empty());
        assert!(!result.converged);
        assert_eq!(result.iterations, 1);
    }

    #[test]
    fn test_refine_predicates_converges_on_duplicate() {
        let disc = PredicateDiscovery::new();
        let mut current = PredicateSet::new();
        current.add(Predicate {
            id: 0,
            expression: "x > 0".to_string(),
            variables: vec!["x".to_string()],
        });

        // Cex that only produces a predicate we already have
        let cex = SpuriousCex {
            path: vec!["x > 0".to_string()],
            failing_state: String::new(),
            reason: String::new(),
        };

        let result = disc.refine_predicates(&cex, &current);
        assert!(result.new_predicates.is_empty());
        assert!(result.converged);
        assert_eq!(result.iterations, 0);
    }

    #[test]
    fn test_evaluate_predicate_holds() {
        let disc = PredicateDiscovery::new();
        let pred =
            Predicate { id: 0, expression: "x > 0".to_string(), variables: vec!["x".to_string()] };

        assert_eq!(disc.evaluate_predicate(&pred, "x = 5"), Some(true));
        assert_eq!(disc.evaluate_predicate(&pred, "x = -1"), Some(false));
    }

    #[test]
    fn test_evaluate_predicate_missing_variable() {
        let disc = PredicateDiscovery::new();
        let pred =
            Predicate { id: 0, expression: "x > 0".to_string(), variables: vec!["x".to_string()] };

        // Variable not in state -> indeterminate
        assert_eq!(disc.evaluate_predicate(&pred, "y = 5"), None);
    }

    #[test]
    fn test_extract_variable_names() {
        let vars = extract_variable_names("x > 0 && y <= z");
        assert!(vars.contains(&"x".to_string()));
        assert!(vars.contains(&"y".to_string()));
        assert!(vars.contains(&"z".to_string()));
        assert!(!vars.contains(&"0".to_string()));
    }

    #[test]
    fn test_extract_variable_names_filters_keywords() {
        let vars = extract_variable_names("if x > 0 else y");
        assert!(vars.contains(&"x".to_string()));
        assert!(vars.contains(&"y".to_string()));
        assert!(!vars.contains(&"if".to_string()));
        assert!(!vars.contains(&"else".to_string()));
    }

    #[test]
    fn test_refinement_result_fields() {
        let result = RefinementResult {
            new_predicates: vec![Predicate {
                id: 0,
                expression: "a > 1".to_string(),
                variables: vec!["a".to_string()],
            }],
            predicates_removed: 2,
            iterations: 3,
            converged: false,
        };
        assert_eq!(result.new_predicates.len(), 1);
        assert_eq!(result.predicates_removed, 2);
        assert_eq!(result.iterations, 3);
        assert!(!result.converged);
    }

    #[test]
    fn test_predicate_set_default() {
        let set = PredicateSet::default();
        assert!(set.is_empty());
    }

    #[test]
    fn test_predicate_discovery_default() {
        let disc = PredicateDiscovery::default();
        // Should be usable immediately
        assert!(disc.check_feasibility(&[]));
    }
}
