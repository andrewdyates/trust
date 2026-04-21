// trust-vcgen/predicate_abstraction.rs: Predicate abstraction for verification
//
// Computes abstract states from concrete predicates over program variables.
// Used by CEGAR to build abstract transition systems where states are
// conjunctions of predicate truth values.
//
// Inspired by CPAchecker's predicate abstraction CPA
// (refs/cpachecker/src/org/sosy_lab/cpachecker/cpa/predicate/).
//
// Part of #298
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::{FxHashMap, FxHashSet};

use trust_types::{Formula, Sort};

/// A named predicate: a boolean formula over program variables.
///
/// Predicates are the building blocks of predicate abstraction. Each predicate
/// represents a property of the program state (e.g., "x > 0", "i < len").
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Predicate {
    /// Human-readable name for the predicate (e.g., "x_positive").
    pub name: String,
    /// The boolean formula this predicate represents.
    pub formula: Formula,
}

impl Predicate {
    /// Create a new predicate with the given name and formula.
    #[must_use]
    pub fn new(name: impl Into<String>, formula: Formula) -> Self {
        Self {
            name: name.into(),
            formula,
        }
    }

    /// Return the negation of this predicate's formula.
    #[must_use]
    pub fn negated_formula(&self) -> Formula {
        Formula::Not(Box::new(self.formula.clone()))
    }
}

/// The truth value of a predicate in an abstract state.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PredicateValue {
    /// The predicate is known to be true.
    True,
    /// The predicate is known to be false.
    False,
    /// The predicate's value is unknown (top).
    Unknown,
}

/// An abstract state: a mapping from predicate indices to truth values.
///
/// Represents a conjunction of predicate truth values. If predicate i has
/// value `True`, the concrete states in this abstract state satisfy predicate i.
/// If `False`, they violate it. If `Unknown`, the predicate is unconstrained.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AbstractState {
    /// Truth values indexed by predicate position in the `PredicateAbstractor`.
    values: Vec<PredicateValue>,
}

impl AbstractState {
    /// Create a new abstract state with all predicates unknown (top).
    #[must_use]
    pub fn top(num_predicates: usize) -> Self {
        Self {
            values: vec![PredicateValue::Unknown; num_predicates],
        }
    }

    /// Create a new abstract state with all predicates set to given values.
    #[must_use]
    pub fn from_values(values: Vec<PredicateValue>) -> Self {
        Self { values }
    }

    /// Get the truth value of the predicate at the given index.
    #[must_use]
    pub fn get(&self, index: usize) -> Option<PredicateValue> {
        self.values.get(index).copied()
    }

    /// Set the truth value of the predicate at the given index.
    pub fn set(&mut self, index: usize, value: PredicateValue) {
        if index < self.values.len() {
            self.values[index] = value;
        }
    }

    /// Return the number of predicates in this abstract state.
    #[must_use]
    pub fn len(&self) -> usize {
        self.values.len()
    }

    /// Return whether the abstract state has no predicates.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.values.is_empty()
    }

    /// Return whether all predicates are unknown (this is top).
    #[must_use]
    pub fn is_top(&self) -> bool {
        self.values.iter().all(|v| *v == PredicateValue::Unknown)
    }

    /// Join two abstract states (widening toward top).
    ///
    /// For each predicate, if both states agree, keep the value.
    /// Otherwise, the result is `Unknown`.
    #[must_use]
    pub fn join(&self, other: &Self) -> Self {
        assert_eq!(self.values.len(), other.values.len(), "abstract state dimension mismatch");
        let values = self
            .values
            .iter()
            .zip(other.values.iter())
            .map(|(a, b)| if a == b { *a } else { PredicateValue::Unknown })
            .collect();
        Self { values }
    }

    /// Meet two abstract states (narrowing toward bottom).
    ///
    /// For each predicate, if either state is known (True/False), use that value.
    /// If both are known but disagree, the result is unsatisfiable (we keep the
    /// first state's value as a convention).
    #[must_use]
    pub fn meet(&self, other: &Self) -> Self {
        assert_eq!(self.values.len(), other.values.len(), "abstract state dimension mismatch");
        let values = self
            .values
            .iter()
            .zip(other.values.iter())
            .map(|(a, b)| match (a, b) {
                (PredicateValue::Unknown, v) | (v, PredicateValue::Unknown) => *v,
                (a, _) => *a, // Both known: keep first (may be inconsistent)
            })
            .collect();
        Self { values }
    }

    /// Check if this state is subsumed by (less precise than or equal to) another.
    ///
    /// State A is subsumed by state B if every known predicate in A has the
    /// same value in B. Unknown predicates in A are unconstrained.
    #[must_use]
    pub fn is_subsumed_by(&self, other: &Self) -> bool {
        assert_eq!(self.values.len(), other.values.len(), "abstract state dimension mismatch");
        self.values.iter().zip(other.values.iter()).all(|(a, b)| {
            *b == PredicateValue::Unknown || a == b
        })
    }

    /// Return the indices of predicates with known (non-Unknown) values.
    #[must_use]
    pub fn known_indices(&self) -> Vec<usize> {
        self.values
            .iter()
            .enumerate()
            .filter(|(_, v)| **v != PredicateValue::Unknown)
            .map(|(i, _)| i)
            .collect()
    }
}

/// A transition in the abstract domain: maps source predicates to target predicates.
///
/// Represents how a program statement transforms the truth values of predicates.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AbstractTransition {
    /// The concrete formula representing the transition relation.
    pub formula: Formula,
    /// Variables modified by this transition.
    pub modified_vars: FxHashSet<String>,
}

impl AbstractTransition {
    /// Create a new abstract transition.
    #[must_use]
    pub fn new(formula: Formula, modified_vars: FxHashSet<String>) -> Self {
        Self { formula, modified_vars }
    }
}

/// Engine for predicate abstraction.
///
/// Maintains a set of predicates and computes abstract transitions,
/// abstract post-images, and abstract pre-images.
#[derive(Debug, Clone)]
pub struct PredicateAbstractor {
    /// The set of predicates used for abstraction.
    predicates: Vec<Predicate>,
    /// Map from predicate name to index for fast lookup.
    name_to_index: FxHashMap<String, usize>,
}

impl PredicateAbstractor {
    /// Create a new predicate abstractor with the given predicates.
    #[must_use]
    pub fn new(predicates: Vec<Predicate>) -> Self {
        let name_to_index = predicates
            .iter()
            .enumerate()
            .map(|(i, p)| (p.name.clone(), i))
            .collect();
        Self { predicates, name_to_index }
    }

    /// Return the number of predicates.
    #[must_use]
    pub fn num_predicates(&self) -> usize {
        self.predicates.len()
    }

    /// Get a predicate by index.
    #[must_use]
    pub fn get_predicate(&self, index: usize) -> Option<&Predicate> {
        self.predicates.get(index)
    }

    /// Get a predicate index by name.
    #[must_use]
    pub fn index_of(&self, name: &str) -> Option<usize> {
        self.name_to_index.get(name).copied()
    }

    /// Create the top abstract state (all predicates unknown).
    #[must_use]
    pub fn top_state(&self) -> AbstractState {
        AbstractState::top(self.predicates.len())
    }

    /// Compute the abstract post-image of a transition from a given abstract state.
    ///
    /// For each predicate, checks whether the transition preserves, invalidates,
    /// or makes the predicate unknown. A predicate whose variables are not
    /// modified by the transition retains its value. A predicate whose variables
    /// are modified becomes unknown unless the transition formula implies it.
    #[must_use]
    pub fn abstract_post(
        &self,
        state: &AbstractState,
        transition: &AbstractTransition,
    ) -> AbstractState {
        let mut result = state.clone();
        for (i, pred) in self.predicates.iter().enumerate() {
            let pred_vars = collect_formula_vars(&pred.formula);
            let has_modified = pred_vars.iter().any(|v| transition.modified_vars.contains(v));
            if has_modified {
                // Predicate mentions a modified variable -- becomes unknown
                // unless the transition formula structurally implies it.
                result.set(i, if formula_implies_structurally(&transition.formula, &pred.formula) {
                    PredicateValue::True
                } else if formula_implies_structurally(
                    &transition.formula,
                    &Formula::Not(Box::new(pred.formula.clone())),
                ) {
                    PredicateValue::False
                } else {
                    PredicateValue::Unknown
                });
            }
            // If no modified variable is mentioned, keep the current value.
        }
        result
    }

    /// Compute the abstract pre-image of a transition from a given abstract state.
    ///
    /// For predicates not modified by the transition, the pre-image retains
    /// the same value. For modified predicates, they become unknown unless
    /// the transition formula provides enough information.
    #[must_use]
    pub fn abstract_pre(
        &self,
        state: &AbstractState,
        transition: &AbstractTransition,
    ) -> AbstractState {
        let mut result = state.clone();
        for (i, pred) in self.predicates.iter().enumerate() {
            let pred_vars = collect_formula_vars(&pred.formula);
            let has_modified = pred_vars.iter().any(|v| transition.modified_vars.contains(v));
            if has_modified {
                // Pre-image: a predicate over modified vars becomes unknown
                // since we don't know what the pre-state looked like.
                result.set(i, PredicateValue::Unknown);
            }
        }
        result
    }

    /// Concretize an abstract state back to a concrete formula.
    ///
    /// The resulting formula is the conjunction of all known predicates
    /// (positive or negated based on their truth value).
    #[must_use]
    pub fn concretize(&self, state: &AbstractState) -> Formula {
        let mut conjuncts = Vec::new();
        for (i, pred) in self.predicates.iter().enumerate() {
            match state.get(i) {
                Some(PredicateValue::True) => {
                    conjuncts.push(pred.formula.clone());
                }
                Some(PredicateValue::False) => {
                    conjuncts.push(pred.negated_formula());
                }
                _ => {} // Unknown or out of bounds: no constraint
            }
        }
        match conjuncts.len() {
            0 => Formula::Bool(true),
            // SAFETY: match arm guarantees len == 1, so .next() returns Some.
            1 => conjuncts.into_iter().next()
                .unwrap_or_else(|| unreachable!("empty iter despite len == 1")),
            _ => Formula::And(conjuncts),
        }
    }

    /// Refine the predicate set by adding new predicates extracted from a
    /// spurious counterexample.
    ///
    /// Given a counterexample path (sequence of formulas along the path)
    /// and the property that was violated, extract interpolants as new predicates.
    /// Returns the indices of newly added predicates.
    pub fn refine_predicates(
        &mut self,
        path_formulas: &[Formula],
        property: &Formula,
    ) -> Vec<usize> {
        let mut new_indices = Vec::new();

        // Extract candidate predicates from path formulas by collecting
        // atomic comparisons that appear in the path.
        for (step, formula) in path_formulas.iter().enumerate() {
            let atoms = extract_atomic_predicates(formula);
            for atom in atoms {
                let name = format!("interp_{}_{}", step, new_indices.len());
                if !self.name_to_index.contains_key(&name)
                    && !self.contains_equivalent(&atom)
                {
                    let idx = self.predicates.len();
                    self.name_to_index.insert(name.clone(), idx);
                    self.predicates.push(Predicate::new(name, atom));
                    new_indices.push(idx);
                }
            }
        }

        // Also add predicates from the property itself.
        let prop_atoms = extract_atomic_predicates(property);
        for atom in prop_atoms {
            let name = format!("prop_{}", new_indices.len());
            if !self.name_to_index.contains_key(&name)
                && !self.contains_equivalent(&atom)
            {
                let idx = self.predicates.len();
                self.name_to_index.insert(name.clone(), idx);
                self.predicates.push(Predicate::new(name, atom));
                new_indices.push(idx);
            }
        }

        new_indices
    }

    /// Check if an equivalent formula already exists in the predicate set.
    fn contains_equivalent(&self, formula: &Formula) -> bool {
        self.predicates.iter().any(|p| p.formula == *formula)
    }
}

/// Collect all variable names mentioned in a formula.
#[must_use]
pub fn collect_formula_vars(formula: &Formula) -> FxHashSet<String> {
    let mut vars = FxHashSet::default();
    collect_vars_recursive(formula, &mut vars);
    vars
}

fn collect_vars_recursive(formula: &Formula, vars: &mut FxHashSet<String>) {
    match formula {
        Formula::Var(name, _) => {
            vars.insert(name.clone());
        }
        _ => {
            for child in formula.children() {
                collect_vars_recursive(child, vars);
            }
        }
    }
}

/// Check if `premise` structurally implies `conclusion`.
///
/// This is a conservative syntactic check, not a full SMT query.
/// Returns true only when implication is obvious from structure.
fn formula_implies_structurally(premise: &Formula, conclusion: &Formula) -> bool {
    // Direct equality
    if premise == conclusion {
        return true;
    }
    // If premise is a conjunction, check if any conjunct implies conclusion
    if let Formula::And(conjuncts) = premise {
        return conjuncts.iter().any(|c| formula_implies_structurally(c, conclusion));
    }
    false
}

/// Extract atomic (non-decomposable) predicate formulas from a formula.
///
/// Collects comparisons (Eq, Lt, Le, Gt, Ge) and their negations
/// from the formula tree.
#[must_use]
pub fn extract_atomic_predicates(formula: &Formula) -> Vec<Formula> {
    let mut atoms = Vec::new();
    extract_atoms_recursive(formula, &mut atoms);
    atoms
}

fn extract_atoms_recursive(formula: &Formula, atoms: &mut Vec<Formula>) {
    match formula {
        // Atomic comparisons are predicates
        Formula::Eq(..) | Formula::Lt(..) | Formula::Le(..) | Formula::Gt(..) | Formula::Ge(..) => {
            atoms.push(formula.clone());
        }
        // Boolean variables are atomic predicates
        Formula::Var(_, Sort::Bool) => {
            atoms.push(formula.clone());
        }
        // Recurse into connectives
        Formula::And(children) | Formula::Or(children) => {
            for child in children {
                extract_atoms_recursive(child, atoms);
            }
        }
        Formula::Not(inner) => {
            extract_atoms_recursive(inner, atoms);
        }
        Formula::Implies(lhs, rhs) => {
            extract_atoms_recursive(lhs, atoms);
            extract_atoms_recursive(rhs, atoms);
        }
        // Other formula types: no atoms to extract
        _ => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn var_int(name: &str) -> Formula {
        Formula::Var(name.to_string(), Sort::Int)
    }

    fn var_bool(name: &str) -> Formula {
        Formula::Var(name.to_string(), Sort::Bool)
    }

    fn pred_gt_zero(name: &str, var: &str) -> Predicate {
        Predicate::new(
            name,
            Formula::Gt(Box::new(var_int(var)), Box::new(Formula::Int(0))),
        )
    }

    fn pred_lt(name: &str, var_a: &str, var_b: &str) -> Predicate {
        Predicate::new(
            name,
            Formula::Lt(Box::new(var_int(var_a)), Box::new(var_int(var_b))),
        )
    }

    #[test]
    fn test_predicate_creation_and_negation() {
        let p = pred_gt_zero("x_pos", "x");
        assert_eq!(p.name, "x_pos");
        let neg = p.negated_formula();
        assert!(matches!(neg, Formula::Not(_)));
        if let Formula::Not(inner) = &neg {
            assert_eq!(**inner, p.formula);
        }
    }

    #[test]
    fn test_abstract_state_top() {
        let state = AbstractState::top(3);
        assert_eq!(state.len(), 3);
        assert!(state.is_top());
        assert!(!state.is_empty());
        for i in 0..3 {
            assert_eq!(state.get(i), Some(PredicateValue::Unknown));
        }
    }

    #[test]
    fn test_abstract_state_set_and_get() {
        let mut state = AbstractState::top(3);
        state.set(0, PredicateValue::True);
        state.set(2, PredicateValue::False);
        assert_eq!(state.get(0), Some(PredicateValue::True));
        assert_eq!(state.get(1), Some(PredicateValue::Unknown));
        assert_eq!(state.get(2), Some(PredicateValue::False));
        assert!(!state.is_top());
    }

    #[test]
    fn test_abstract_state_join() {
        let mut a = AbstractState::top(3);
        a.set(0, PredicateValue::True);
        a.set(1, PredicateValue::True);
        a.set(2, PredicateValue::False);

        let mut b = AbstractState::top(3);
        b.set(0, PredicateValue::True);
        b.set(1, PredicateValue::False);
        b.set(2, PredicateValue::False);

        let joined = a.join(&b);
        assert_eq!(joined.get(0), Some(PredicateValue::True));   // Agree
        assert_eq!(joined.get(1), Some(PredicateValue::Unknown)); // Disagree
        assert_eq!(joined.get(2), Some(PredicateValue::False));   // Agree
    }

    #[test]
    fn test_abstract_state_meet() {
        let mut a = AbstractState::top(3);
        a.set(0, PredicateValue::True);

        let mut b = AbstractState::top(3);
        b.set(1, PredicateValue::False);
        b.set(2, PredicateValue::True);

        let met = a.meet(&b);
        assert_eq!(met.get(0), Some(PredicateValue::True));
        assert_eq!(met.get(1), Some(PredicateValue::False));
        assert_eq!(met.get(2), Some(PredicateValue::True));
    }

    #[test]
    fn test_abstract_state_subsumption() {
        let mut specific = AbstractState::top(3);
        specific.set(0, PredicateValue::True);
        specific.set(1, PredicateValue::False);

        let mut general = AbstractState::top(3);
        general.set(0, PredicateValue::True);

        // specific is subsumed by general (general is less constrained)
        assert!(specific.is_subsumed_by(&general));
        // general is NOT subsumed by specific (specific constrains pred 1)
        assert!(!general.is_subsumed_by(&specific));
    }

    #[test]
    fn test_abstract_state_known_indices() {
        let mut state = AbstractState::top(4);
        state.set(1, PredicateValue::True);
        state.set(3, PredicateValue::False);
        assert_eq!(state.known_indices(), vec![1, 3]);
    }

    #[test]
    fn test_concretize_all_unknown_is_true() {
        let preds = vec![pred_gt_zero("x_pos", "x")];
        let abstractor = PredicateAbstractor::new(preds);
        let state = abstractor.top_state();
        let formula = abstractor.concretize(&state);
        assert_eq!(formula, Formula::Bool(true));
    }

    #[test]
    fn test_concretize_single_true_predicate() {
        let preds = vec![pred_gt_zero("x_pos", "x")];
        let abstractor = PredicateAbstractor::new(preds.clone());
        let state = AbstractState::from_values(vec![PredicateValue::True]);
        let formula = abstractor.concretize(&state);
        assert_eq!(formula, preds[0].formula);
    }

    #[test]
    fn test_concretize_mixed_predicates() {
        let preds = vec![
            pred_gt_zero("x_pos", "x"),
            pred_lt("i_lt_n", "i", "n"),
        ];
        let abstractor = PredicateAbstractor::new(preds);
        let state = AbstractState::from_values(vec![
            PredicateValue::True,
            PredicateValue::False,
        ]);
        let formula = abstractor.concretize(&state);
        match &formula {
            Formula::And(conjuncts) => {
                assert_eq!(conjuncts.len(), 2);
                // First should be x > 0
                assert!(matches!(&conjuncts[0], Formula::Gt(..)));
                // Second should be NOT(i < n)
                assert!(matches!(&conjuncts[1], Formula::Not(_)));
            }
            _ => panic!("expected And formula, got: {formula:?}"),
        }
    }

    #[test]
    fn test_abstract_post_unmodified_var_preserves() {
        let preds = vec![
            pred_gt_zero("x_pos", "x"),
            pred_gt_zero("y_pos", "y"),
        ];
        let abstractor = PredicateAbstractor::new(preds);

        let mut state = abstractor.top_state();
        state.set(0, PredicateValue::True);
        state.set(1, PredicateValue::True);

        // Transition modifies only y
        let transition = AbstractTransition::new(
            Formula::Eq(
                Box::new(var_int("y")),
                Box::new(Formula::Int(5)),
            ),
            ["y".to_string()].into_iter().collect(),
        );

        let post = abstractor.abstract_post(&state, &transition);
        // x_pos should be preserved (x not modified)
        assert_eq!(post.get(0), Some(PredicateValue::True));
        // y_pos becomes unknown (y modified, no structural implication of y > 0)
        assert_eq!(post.get(1), Some(PredicateValue::Unknown));
    }

    #[test]
    fn test_abstract_pre_modified_var_becomes_unknown() {
        let preds = vec![
            pred_gt_zero("x_pos", "x"),
            pred_gt_zero("y_pos", "y"),
        ];
        let abstractor = PredicateAbstractor::new(preds);

        let mut state = abstractor.top_state();
        state.set(0, PredicateValue::True);
        state.set(1, PredicateValue::True);

        let transition = AbstractTransition::new(
            Formula::Bool(true),
            ["x".to_string()].into_iter().collect(),
        );

        let pre = abstractor.abstract_pre(&state, &transition);
        assert_eq!(pre.get(0), Some(PredicateValue::Unknown)); // x modified
        assert_eq!(pre.get(1), Some(PredicateValue::True));     // y preserved
    }

    #[test]
    fn test_refine_predicates_from_path() {
        let preds = vec![pred_gt_zero("x_pos", "x")];
        let mut abstractor = PredicateAbstractor::new(preds);
        assert_eq!(abstractor.num_predicates(), 1);

        let path = vec![
            Formula::Lt(
                Box::new(var_int("i")),
                Box::new(var_int("n")),
            ),
        ];
        let property = Formula::Ge(
            Box::new(var_int("i")),
            Box::new(Formula::Int(0)),
        );

        let new_indices = abstractor.refine_predicates(&path, &property);
        assert!(!new_indices.is_empty(), "refinement should add new predicates");
        assert!(abstractor.num_predicates() > 1, "predicate count should increase");

        // Verify the new predicates contain the atomic comparisons from the path/property
        let has_lt = abstractor.predicates.iter().any(|p| matches!(&p.formula, Formula::Lt(..)));
        let has_ge = abstractor.predicates.iter().any(|p| matches!(&p.formula, Formula::Ge(..)));
        assert!(has_lt, "should have extracted Lt predicate from path");
        assert!(has_ge, "should have extracted Ge predicate from property");
    }

    #[test]
    fn test_refine_predicates_no_duplicates() {
        let initial = vec![
            Predicate::new(
                "i_lt_n",
                Formula::Lt(Box::new(var_int("i")), Box::new(var_int("n"))),
            ),
        ];
        let mut abstractor = PredicateAbstractor::new(initial);

        // Path contains the same formula that already exists
        let path = vec![
            Formula::Lt(Box::new(var_int("i")), Box::new(var_int("n"))),
        ];
        let property = Formula::Bool(true);

        let new_indices = abstractor.refine_predicates(&path, &property);
        // Should not add a duplicate
        assert_eq!(abstractor.num_predicates(), 1, "should not add duplicate predicate");
        assert!(new_indices.is_empty(), "no new indices for duplicate");
    }

    #[test]
    fn test_collect_formula_vars() {
        let formula = Formula::And(vec![
            Formula::Gt(Box::new(var_int("x")), Box::new(Formula::Int(0))),
            Formula::Lt(Box::new(var_int("y")), Box::new(var_int("z"))),
        ]);
        let vars = collect_formula_vars(&formula);
        assert_eq!(vars.len(), 3);
        assert!(vars.contains("x"));
        assert!(vars.contains("y"));
        assert!(vars.contains("z"));
    }

    #[test]
    fn test_extract_atomic_predicates() {
        let formula = Formula::And(vec![
            Formula::Gt(Box::new(var_int("x")), Box::new(Formula::Int(0))),
            Formula::Or(vec![
                Formula::Lt(Box::new(var_int("i")), Box::new(var_int("n"))),
                var_bool("flag"),
            ]),
        ]);
        let atoms = extract_atomic_predicates(&formula);
        assert_eq!(atoms.len(), 3);
        assert!(atoms.iter().any(|a| matches!(a, Formula::Gt(..))));
        assert!(atoms.iter().any(|a| matches!(a, Formula::Lt(..))));
        assert!(atoms.iter().any(|a| matches!(a, Formula::Var(n, Sort::Bool) if n == "flag")));
    }

    #[test]
    fn test_predicate_abstractor_index_lookup() {
        let preds = vec![
            pred_gt_zero("x_pos", "x"),
            pred_lt("i_lt_n", "i", "n"),
        ];
        let abstractor = PredicateAbstractor::new(preds);
        assert_eq!(abstractor.index_of("x_pos"), Some(0));
        assert_eq!(abstractor.index_of("i_lt_n"), Some(1));
        assert_eq!(abstractor.index_of("nonexistent"), None);
        assert_eq!(abstractor.num_predicates(), 2);
    }

    #[test]
    fn test_abstract_post_structural_implication() {
        // If the transition formula directly states x > 0, the predicate
        // x > 0 should be True after the transition.
        let gt_zero = Formula::Gt(Box::new(var_int("x")), Box::new(Formula::Int(0)));
        let preds = vec![Predicate::new("x_pos", gt_zero.clone())];
        let abstractor = PredicateAbstractor::new(preds);

        let state = abstractor.top_state();
        let transition = AbstractTransition::new(
            Formula::And(vec![
                gt_zero.clone(),
                Formula::Eq(Box::new(var_int("x")), Box::new(Formula::Int(5))),
            ]),
            ["x".to_string()].into_iter().collect(),
        );

        let post = abstractor.abstract_post(&state, &transition);
        assert_eq!(post.get(0), Some(PredicateValue::True),
            "predicate x > 0 should be True when transition implies x > 0");
    }

    #[test]
    fn test_empty_abstract_state() {
        let state = AbstractState::top(0);
        assert!(state.is_empty());
        assert!(state.is_top());
        assert_eq!(state.known_indices(), Vec::<usize>::new());
    }
}
