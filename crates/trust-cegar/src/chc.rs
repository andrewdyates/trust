// tRust: Constrained Horn Clause (CHC) encoding for loop invariant inference
//
// Encodes verification conditions involving loops as CHC systems that can be
// solved by z4's Spacer engine (IC3/PDR for software).
//
// Theory: A loop with header predicate Inv(x) produces Horn clauses:
//   - Init:      pre(x)                         => Inv(x)   (entry clause)
//   - Step:      Inv(x) /\ body(x, x')          => Inv(x')  (inductive clause)
//   - Property:  Inv(x) /\ exit_cond(x)         => post(x)  (safety clause)
//
// If Spacer finds a solution for Inv, that solution IS the loop invariant.
//
// Reference: Bjorner, Gurfinkel, McMillan, Rybalchenko,
//   "Horn Clause Solvers for Program Verification" (2015)
// Reference: refs/cpachecker/src/org/sosy_lab/cpachecker/cpa/predicate/
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};
use trust_types::{Formula, Sort};

use crate::error::CegarError;

// ---------------------------------------------------------------------------
// Core types
// ---------------------------------------------------------------------------

/// A CHC predicate symbol with its argument sorts.
///
/// In the loop invariant setting, each loop header gets one predicate symbol.
/// The arguments are the live variables at the loop header.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ChcPredicate {
    /// Name of the predicate (e.g., "Inv_loop_0").
    pub name: String,
    /// Argument sorts — one per live variable at the loop header.
    pub arg_sorts: Vec<Sort>,
}

impl ChcPredicate {
    /// Create a new CHC predicate.
    #[must_use]
    pub fn new(name: impl Into<String>, arg_sorts: Vec<Sort>) -> Self {
        Self { name: name.into(), arg_sorts }
    }

    /// The arity (number of arguments) of this predicate.
    #[must_use]
    pub fn arity(&self) -> usize {
        self.arg_sorts.len()
    }
}

/// A predicate application: predicate symbol applied to argument terms.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PredicateApp {
    /// Name of the predicate being applied.
    pub predicate: String,
    /// Argument terms (must match the predicate's arity).
    pub args: Vec<Formula>,
}

impl PredicateApp {
    /// Create a new predicate application.
    #[must_use]
    pub fn new(predicate: impl Into<String>, args: Vec<Formula>) -> Self {
        Self { predicate: predicate.into(), args }
    }
}

/// The kind of Horn clause in a CHC system.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ClauseKind {
    /// Entry clause: precondition => Inv(x).
    /// No predicate in the body.
    Init,
    /// Inductive step: Inv(x) /\ body_constraint(x, x') => Inv(x').
    /// One predicate application in the body.
    Step,
    /// Safety/property clause: Inv(x) /\ exit_cond(x) => postcondition.
    /// One predicate in the body, no predicate in the head.
    Property,
}

/// A single Constrained Horn Clause.
///
/// General form: body_preds /\ constraint => head
///
/// Where:
/// - `body_preds`: zero or more predicate applications
/// - `constraint`: a quantifier-free formula over the variables
/// - `head`: either a predicate application (Init/Step) or a formula (Property)
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct HornClause {
    /// What kind of clause this is.
    pub kind: ClauseKind,
    /// Predicate applications in the body (empty for Init clauses).
    pub body_predicates: Vec<PredicateApp>,
    /// The constraint (quantifier-free formula) in the body.
    pub constraint: Formula,
    /// The head: either a predicate application or None for property/query clauses.
    /// When None, the constraint must imply the postcondition directly.
    pub head: Option<PredicateApp>,
    /// For property clauses: the postcondition that must hold.
    pub postcondition: Option<Formula>,
}

impl HornClause {
    /// Create an Init clause: `constraint => Inv(args)`.
    #[must_use]
    pub fn init(constraint: Formula, head: PredicateApp) -> Self {
        Self {
            kind: ClauseKind::Init,
            body_predicates: Vec::new(),
            constraint,
            head: Some(head),
            postcondition: None,
        }
    }

    /// Create a Step clause: `Inv(args) /\ constraint => Inv(args')`.
    #[must_use]
    pub fn step(body_pred: PredicateApp, constraint: Formula, head: PredicateApp) -> Self {
        Self {
            kind: ClauseKind::Step,
            body_predicates: vec![body_pred],
            constraint,
            head: Some(head),
            postcondition: None,
        }
    }

    /// Create a Property clause: `Inv(args) /\ constraint => post`.
    #[must_use]
    pub fn property(body_pred: PredicateApp, constraint: Formula, postcondition: Formula) -> Self {
        Self {
            kind: ClauseKind::Property,
            body_predicates: vec![body_pred],
            constraint,
            head: None,
            postcondition: Some(postcondition),
        }
    }
}

/// A complete CHC system for one or more loops.
///
/// Contains predicate declarations and Horn clauses. Solvable by Spacer.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ChcSystem {
    /// Predicate symbols declared in this system.
    pub predicates: Vec<ChcPredicate>,
    /// Horn clauses.
    pub clauses: Vec<HornClause>,
}

impl ChcSystem {
    /// Create an empty CHC system.
    #[must_use]
    pub fn new() -> Self {
        Self { predicates: Vec::new(), clauses: Vec::new() }
    }

    /// Add a predicate declaration to the system.
    pub fn add_predicate(&mut self, pred: ChcPredicate) {
        self.predicates.push(pred);
    }

    /// Add a Horn clause to the system.
    pub fn add_clause(&mut self, clause: HornClause) {
        self.clauses.push(clause);
    }

    /// Number of predicates in this system.
    #[must_use]
    pub fn num_predicates(&self) -> usize {
        self.predicates.len()
    }

    /// Number of clauses in this system.
    #[must_use]
    pub fn num_clauses(&self) -> usize {
        self.clauses.len()
    }

    /// Whether this system is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.clauses.is_empty()
    }

    /// Validate that all predicate references in clauses refer to declared predicates,
    /// and that arities match.
    ///
    /// # Errors
    /// Returns `CegarError::InconsistentAbstraction` on validation failure.
    pub fn validate(&self) -> Result<(), CegarError> {
        for clause in &self.clauses {
            // Check body predicates.
            for app in &clause.body_predicates {
                self.validate_app(app)?;
            }
            // Check head predicate.
            if let Some(head) = &clause.head {
                self.validate_app(head)?;
            }
        }
        Ok(())
    }

    /// Validate a single predicate application.
    fn validate_app(&self, app: &PredicateApp) -> Result<(), CegarError> {
        let decl = self.predicates.iter().find(|p| p.name == app.predicate);
        match decl {
            None => Err(CegarError::InconsistentAbstraction {
                reason: format!("predicate `{}` used in clause but not declared", app.predicate),
            }),
            Some(pred) if pred.arity() != app.args.len() => {
                Err(CegarError::InconsistentAbstraction {
                    reason: format!(
                        "predicate `{}` has arity {} but applied with {} arguments",
                        app.predicate,
                        pred.arity(),
                        app.args.len()
                    ),
                })
            }
            Some(_) => Ok(()),
        }
    }
}

impl Default for ChcSystem {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// CHC encoding from loop structure
// ---------------------------------------------------------------------------

/// Parameters for encoding a single loop as a CHC system.
///
/// Represents the logical structure of a loop:
/// - precondition: what holds on entry
/// - loop body constraint: the transition relation (maps pre-state to post-state)
/// - exit condition: when the loop terminates
/// - postcondition: what must hold after the loop
pub struct LoopEncoding {
    /// Name for the loop invariant predicate (e.g., "Inv_loop_0").
    pub invariant_name: String,
    /// Variables live at the loop header, with their sorts.
    pub variables: Vec<(String, Sort)>,
    /// Primed variable names (post-state versions), same order as `variables`.
    pub primed_variables: Vec<(String, Sort)>,
    /// Precondition: formula over `variables` that holds on loop entry.
    pub precondition: Formula,
    /// Loop body transition constraint: formula relating `variables` to `primed_variables`.
    pub body_constraint: Formula,
    /// Loop exit condition: formula over `variables` that triggers loop exit.
    pub exit_condition: Formula,
    /// Postcondition: formula over `variables` that must hold after loop exit.
    pub postcondition: Formula,
}

/// Encode a loop into a CHC system.
///
/// Produces a 3-clause system:
/// 1. Init:     `precondition(x) => Inv(x)`
/// 2. Step:     `Inv(x) /\ body(x, x') => Inv(x')`
/// 3. Property: `Inv(x) /\ exit(x) => post(x)`
///
/// # Errors
/// Returns `CegarError::InconsistentAbstraction` if variables/primed_variables mismatch.
pub fn encode_loop(encoding: &LoopEncoding) -> Result<ChcSystem, CegarError> {
    // Validate variable lists match.
    if encoding.variables.len() != encoding.primed_variables.len() {
        return Err(CegarError::InconsistentAbstraction {
            reason: format!(
                "variables ({}) and primed_variables ({}) have different lengths",
                encoding.variables.len(),
                encoding.primed_variables.len()
            ),
        });
    }

    let mut system = ChcSystem::new();

    // Declare the invariant predicate.
    let arg_sorts: Vec<Sort> = encoding.variables.iter().map(|(_, s)| s.clone()).collect();
    let pred = ChcPredicate::new(&encoding.invariant_name, arg_sorts);
    system.add_predicate(pred);

    // Build variable term lists.
    let var_terms: Vec<Formula> = encoding
        .variables
        .iter()
        .map(|(name, sort)| Formula::Var(name.clone(), sort.clone()))
        .collect();

    let primed_terms: Vec<Formula> = encoding
        .primed_variables
        .iter()
        .map(|(name, sort)| Formula::Var(name.clone(), sort.clone()))
        .collect();

    // Clause 1: Init — precondition(x) => Inv(x)
    let init_head = PredicateApp::new(&encoding.invariant_name, var_terms.clone());
    system.add_clause(HornClause::init(encoding.precondition.clone(), init_head));

    // Clause 2: Step — Inv(x) /\ body(x, x') => Inv(x')
    let step_body = PredicateApp::new(&encoding.invariant_name, var_terms.clone());
    let step_head = PredicateApp::new(&encoding.invariant_name, primed_terms);
    system.add_clause(HornClause::step(step_body, encoding.body_constraint.clone(), step_head));

    // Clause 3: Property — Inv(x) /\ exit(x) => post(x)
    let prop_body = PredicateApp::new(&encoding.invariant_name, var_terms);
    system.add_clause(HornClause::property(
        prop_body,
        encoding.exit_condition.clone(),
        encoding.postcondition.clone(),
    ));

    // Validate the constructed system.
    system.validate()?;

    Ok(system)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_chc_predicate_basic() {
        let pred = ChcPredicate::new("Inv", vec![Sort::Int, Sort::Int]);
        assert_eq!(pred.name, "Inv");
        assert_eq!(pred.arity(), 2);
    }

    #[test]
    fn test_predicate_app_basic() {
        let app = PredicateApp::new(
            "Inv",
            vec![Formula::Var("x".into(), Sort::Int), Formula::Var("y".into(), Sort::Int)],
        );
        assert_eq!(app.predicate, "Inv");
        assert_eq!(app.args.len(), 2);
    }

    #[test]
    fn test_horn_clause_init() {
        let head = PredicateApp::new("Inv", vec![Formula::Var("x".into(), Sort::Int)]);
        let clause = HornClause::init(
            Formula::Ge(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(0))),
            head,
        );
        assert_eq!(clause.kind, ClauseKind::Init);
        assert!(clause.body_predicates.is_empty());
        assert!(clause.head.is_some());
        assert!(clause.postcondition.is_none());
    }

    #[test]
    fn test_horn_clause_step() {
        let body = PredicateApp::new("Inv", vec![Formula::Var("x".into(), Sort::Int)]);
        let head = PredicateApp::new("Inv", vec![Formula::Var("x_prime".into(), Sort::Int)]);
        let clause = HornClause::step(
            body,
            Formula::Eq(
                Box::new(Formula::Var("x_prime".into(), Sort::Int)),
                Box::new(Formula::Add(
                    Box::new(Formula::Var("x".into(), Sort::Int)),
                    Box::new(Formula::Int(1)),
                )),
            ),
            head,
        );
        assert_eq!(clause.kind, ClauseKind::Step);
        assert_eq!(clause.body_predicates.len(), 1);
        assert!(clause.head.is_some());
    }

    #[test]
    fn test_horn_clause_property() {
        let body = PredicateApp::new("Inv", vec![Formula::Var("x".into(), Sort::Int)]);
        let clause = HornClause::property(
            body,
            Formula::Ge(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(10))),
            Formula::Le(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(100))),
        );
        assert_eq!(clause.kind, ClauseKind::Property);
        assert!(clause.head.is_none());
        assert!(clause.postcondition.is_some());
    }

    #[test]
    fn test_chc_system_empty() {
        let system = ChcSystem::new();
        assert!(system.is_empty());
        assert_eq!(system.num_predicates(), 0);
        assert_eq!(system.num_clauses(), 0);
        system.validate().expect("empty system should validate");
    }

    #[test]
    fn test_chc_system_validation_undeclared_predicate() {
        let mut system = ChcSystem::new();
        let head = PredicateApp::new("Inv", vec![Formula::Int(0)]);
        system.add_clause(HornClause::init(Formula::Bool(true), head));
        let result = system.validate();
        assert!(matches!(result, Err(CegarError::InconsistentAbstraction { .. })));
    }

    #[test]
    fn test_chc_system_validation_arity_mismatch() {
        let mut system = ChcSystem::new();
        system.add_predicate(ChcPredicate::new("Inv", vec![Sort::Int]));
        // Apply with 2 args when arity is 1.
        let head = PredicateApp::new("Inv", vec![Formula::Int(0), Formula::Int(1)]);
        system.add_clause(HornClause::init(Formula::Bool(true), head));
        let result = system.validate();
        assert!(matches!(result, Err(CegarError::InconsistentAbstraction { .. })));
    }

    #[test]
    fn test_encode_loop_counting() {
        // Loop: x starts at 0, increments by 1, exits when x >= 10
        // Postcondition: x == 10
        let encoding = LoopEncoding {
            invariant_name: "Inv_loop_0".into(),
            variables: vec![("x".into(), Sort::Int)],
            primed_variables: vec![("x_prime".into(), Sort::Int)],
            precondition: Formula::Eq(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            body_constraint: Formula::And(vec![
                // x < 10 (loop condition)
                Formula::Lt(
                    Box::new(Formula::Var("x".into(), Sort::Int)),
                    Box::new(Formula::Int(10)),
                ),
                // x' = x + 1 (body)
                Formula::Eq(
                    Box::new(Formula::Var("x_prime".into(), Sort::Int)),
                    Box::new(Formula::Add(
                        Box::new(Formula::Var("x".into(), Sort::Int)),
                        Box::new(Formula::Int(1)),
                    )),
                ),
            ]),
            exit_condition: Formula::Ge(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(10)),
            ),
            postcondition: Formula::Eq(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(10)),
            ),
        };

        let system = encode_loop(&encoding).expect("should encode");
        assert_eq!(system.num_predicates(), 1);
        assert_eq!(system.num_clauses(), 3);
        assert_eq!(system.predicates[0].name, "Inv_loop_0");
        assert_eq!(system.predicates[0].arity(), 1);
        system.validate().expect("encoded system should validate");
    }

    #[test]
    fn test_encode_loop_variable_mismatch() {
        let encoding = LoopEncoding {
            invariant_name: "Inv".into(),
            variables: vec![("x".into(), Sort::Int)],
            primed_variables: vec![], // Mismatch!
            precondition: Formula::Bool(true),
            body_constraint: Formula::Bool(true),
            exit_condition: Formula::Bool(true),
            postcondition: Formula::Bool(true),
        };
        let result = encode_loop(&encoding);
        assert!(matches!(result, Err(CegarError::InconsistentAbstraction { .. })));
    }

    #[test]
    fn test_encode_loop_multiple_variables() {
        // Loop with two variables: x and y
        let encoding = LoopEncoding {
            invariant_name: "Inv_2var".into(),
            variables: vec![("x".into(), Sort::Int), ("y".into(), Sort::Int)],
            primed_variables: vec![("x_prime".into(), Sort::Int), ("y_prime".into(), Sort::Int)],
            precondition: Formula::And(vec![
                Formula::Eq(
                    Box::new(Formula::Var("x".into(), Sort::Int)),
                    Box::new(Formula::Int(0)),
                ),
                Formula::Eq(
                    Box::new(Formula::Var("y".into(), Sort::Int)),
                    Box::new(Formula::Int(100)),
                ),
            ]),
            body_constraint: Formula::Bool(true),
            exit_condition: Formula::Bool(true),
            postcondition: Formula::Bool(true),
        };

        let system = encode_loop(&encoding).expect("should encode");
        assert_eq!(system.predicates[0].arity(), 2);
        system.validate().expect("should validate");
    }

    #[test]
    fn test_chc_system_default() {
        let system = ChcSystem::default();
        assert!(system.is_empty());
    }
}
