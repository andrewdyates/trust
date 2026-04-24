// trust-cegar: Abstract domains for predicate abstraction
//
// Implements abstract domain operations (top, bottom, join, meet, widen, narrow)
// for predicate-based abstraction. Provides both boolean abstraction (full
// predicate tracking) and Cartesian abstraction (independent per-predicate
// tracking) from CPAchecker.
//
// Reference: CPAchecker's predicate abstraction domain
//   refs/cpachecker/src/org/sosy_lab/cpachecker/cpa/predicate/
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};
use trust_types::Formula;

use crate::predicate::{AbstractState, CmpOp, Predicate};
use crate::predicate_discovery::PredicateSet;

/// Sentinel name used to represent the bottom element of the abstract lattice.
///
/// tRust #163: Replaces magic string `"__bottom__"` with a named constant.
const BOTTOM_SENTINEL_NAME: &str = "__bottom__";

/// Construct a sentinel predicate representing the bottom lattice element.
#[must_use]
pub fn bottom_sentinel() -> Predicate {
    Predicate::Custom(BOTTOM_SENTINEL_NAME.into())
}

/// Check whether an abstract state is bottom (unreachable).
#[must_use]
pub fn is_bottom(state: &AbstractState) -> bool {
    state.contains(&Predicate::Custom(BOTTOM_SENTINEL_NAME.into()))
}

/// Abstract domain operations for CEGAR.
///
/// Any abstract domain must support the standard lattice operations:
/// top (most abstract), bottom (unreachable), join (merge at control-flow
/// merge points), meet (conjunction), and optionally widening/narrowing
/// for convergence acceleration.
pub trait AbstractDomain: std::fmt::Debug {
    /// The top element: no information (all concrete states).
    fn top(&self) -> AbstractState;

    /// The bottom element: unreachable (no concrete states).
    fn bottom(&self) -> AbstractState;

    /// Join two abstract states (least upper bound).
    ///
    /// At control-flow merge points, the join ensures that any predicate
    /// in the result holds on both incoming paths.
    fn join(&self, a: &AbstractState, b: &AbstractState) -> AbstractState;

    /// Meet two abstract states (greatest lower bound).
    ///
    /// Conjunction of two states: all predicates from both are assumed.
    fn meet(&self, a: &AbstractState, b: &AbstractState) -> AbstractState;

    /// Widen to accelerate convergence in loops.
    ///
    /// Default: same as join. Implementations may drop predicates that
    /// are not stable across iterations.
    fn widen(&self, prev: &AbstractState, next: &AbstractState) -> AbstractState {
        self.join(prev, next)
    }

    /// Narrow to recover precision after widening.
    ///
    /// Default: same as meet. Implementations may re-add predicates that
    /// were dropped by widening.
    fn narrow(&self, wide: &AbstractState, precise: &AbstractState) -> AbstractState {
        self.meet(wide, precise)
    }
}

/// Predicate abstraction: map concrete states to boolean combinations
/// over a set of tracked predicates.
///
/// This is the core abstraction used in CPAchecker's predicate CPA.
/// An abstract state is a conjunction of predicates known to hold.
#[derive(Debug, Clone)]
pub struct PredicateAbstraction {
    /// The universe of predicates being tracked.
    predicates: PredicateSet,
}

impl PredicateAbstraction {
    /// Create a new predicate abstraction over the given predicate set.
    #[must_use]
    pub fn new(predicates: PredicateSet) -> Self {
        Self { predicates }
    }

    /// Access the tracked predicates.
    #[must_use]
    pub fn predicates(&self) -> &PredicateSet {
        &self.predicates
    }

    /// Add a predicate to the tracked set.
    pub fn add_predicate(&mut self, pred: Predicate) {
        self.predicates.insert(pred);
    }
}

impl AbstractDomain for PredicateAbstraction {
    fn top(&self) -> AbstractState {
        AbstractState::top()
    }

    fn bottom(&self) -> AbstractState {
        // Bottom = all predicates and their negations hold (contradiction).
        // We represent bottom as a state containing a sentinel predicate.
        let mut state = AbstractState::top();
        state.add(bottom_sentinel());
        state
    }

    fn join(&self, a: &AbstractState, b: &AbstractState) -> AbstractState {
        // Check for bottom elements using the sentinel helper.
        if is_bottom(a) {
            return b.clone();
        }
        if is_bottom(b) {
            return a.clone();
        }
        a.join(b)
    }

    fn meet(&self, a: &AbstractState, b: &AbstractState) -> AbstractState {
        a.meet(b)
    }

    fn widen(&self, prev: &AbstractState, next: &AbstractState) -> AbstractState {
        // Widening: keep only predicates that held in both prev and next.
        // This is the same as join for predicate abstraction. A more
        // aggressive widening would drop unstable predicates.
        self.join(prev, next)
    }

    fn narrow(&self, wide: &AbstractState, precise: &AbstractState) -> AbstractState {
        // Narrowing: add back predicates from precise that are consistent
        // with wide. For predicate abstraction, this is just meet.
        self.meet(wide, precise)
    }
}

/// Compute the abstract state from a concrete formula under a predicate set.
///
/// For each predicate in the set, check if the formula implies the predicate.
/// This is an approximation: we check structural matches rather than
/// semantic entailment (which would require an SMT call).
#[must_use]
pub fn abstract_state(concrete: &Formula, predicates: &PredicateSet) -> AbstractState {
    let mut state = AbstractState::top();

    for pred in predicates.iter() {
        if formula_implies_predicate(concrete, pred) {
            state.add(pred.clone());
        }
    }

    state
}

/// Concretize an abstract state back to a formula.
///
/// The formula is the conjunction of all predicates in the abstract state.
#[must_use]
pub fn concretize(abstract_state: &AbstractState) -> Formula {
    if abstract_state.is_empty() {
        return Formula::Bool(true);
    }

    let conjuncts: Vec<Formula> =
        abstract_state.predicates.iter().map(predicate_to_formula).collect();

    if conjuncts.len() == 1 {
        conjuncts.into_iter().next().expect("checked len == 1")
    } else {
        Formula::And(conjuncts)
    }
}

/// Convert a predicate back to a Formula.
fn predicate_to_formula(pred: &Predicate) -> Formula {
    match pred {
        Predicate::Comparison { lhs, op, rhs } => {
            let lhs_f = name_to_formula(lhs);
            let rhs_f = name_to_formula(rhs);
            match op {
                CmpOp::Lt => Formula::Lt(Box::new(lhs_f), Box::new(rhs_f)),
                CmpOp::Le => Formula::Le(Box::new(lhs_f), Box::new(rhs_f)),
                CmpOp::Gt => Formula::Gt(Box::new(lhs_f), Box::new(rhs_f)),
                CmpOp::Ge => Formula::Ge(Box::new(lhs_f), Box::new(rhs_f)),
                CmpOp::Eq => Formula::Eq(Box::new(lhs_f), Box::new(rhs_f)),
                CmpOp::Ne => Formula::Not(Box::new(Formula::Eq(Box::new(lhs_f), Box::new(rhs_f)))),
            }
        }
        Predicate::Range { var, lo, hi } => {
            let var_f = name_to_formula(var);
            Formula::And(vec![
                Formula::Ge(Box::new(var_f.clone()), Box::new(Formula::Int(*lo))),
                Formula::Le(Box::new(var_f), Box::new(Formula::Int(*hi))),
            ])
        }
        Predicate::NonNull(var) => {
            let var_f = name_to_formula(var);
            Formula::Not(Box::new(Formula::Eq(Box::new(var_f), Box::new(Formula::Int(0)))))
        }
        Predicate::Custom(s) => {
            // Custom predicates cannot be faithfully converted; use a sentinel var.
            Formula::Var(format!("__custom_{s}"), trust_types::Sort::Bool)
        }
    }
}

/// Convert a name string to a Formula (variable or integer literal).
fn name_to_formula(name: &str) -> Formula {
    if let Ok(n) = name.parse::<i128>() {
        Formula::Int(n)
    } else {
        Formula::Var(name.to_string(), trust_types::Sort::Int)
    }
}

/// Check if a formula structurally implies a predicate.
///
/// Uses structural matching that recognizes equivalent forms beyond pure
/// syntactic equality: flipped operands (a < b implies b > a), commutativity
/// of Eq, recursive descent into And/Or/Implies, and arithmetic simplification.
///
/// tRust #412: Improved from purely syntactic string matching to structural
/// semantic entailment.
fn formula_implies_predicate(formula: &Formula, pred: &Predicate) -> bool {
    match pred {
        Predicate::Comparison { lhs, op, rhs } => {
            formula_contains_comparison(formula, lhs, *op, rhs)
        }
        Predicate::Range { var, lo, hi } => {
            // Check if formula contains both var >= lo and var <= hi.
            formula_contains_comparison(formula, var, CmpOp::Ge, &lo.to_string())
                && formula_contains_comparison(formula, var, CmpOp::Le, &hi.to_string())
        }
        Predicate::NonNull(var) => {
            // Check if formula contains var != 0.
            formula_contains_comparison(formula, var, CmpOp::Ne, "0")
        }
        Predicate::Custom(_) => false, // Cannot check custom predicates structurally.
    }
}

/// Check if a formula contains a specific comparison.
///
/// tRust #412: Structural matching that recognizes equivalent forms:
/// - Flipped operands: `a < b` in formula matches predicate `b > a`
/// - Commutativity: `Eq(a, b)` matches predicate `a == b` or `b == a`
/// - Recursive descent into `And`, `Or`, and `Implies` consequents
fn formula_contains_comparison(formula: &Formula, lhs: &str, op: CmpOp, rhs: &str) -> bool {
    // Direct match: formula node matches predicate exactly
    if formula_node_matches(formula, lhs, op, rhs) {
        return true;
    }

    // Structural descent into compound formulas
    match formula {
        Formula::And(children) => {
            children.iter().any(|c| formula_contains_comparison(c, lhs, op, rhs))
        }
        Formula::Or(children) => {
            // If ALL branches contain the comparison, the disjunction implies it
            !children.is_empty()
                && children.iter().all(|c| formula_contains_comparison(c, lhs, op, rhs))
        }
        Formula::Implies(_antecedent, _consequent) => {
            // #778: Cannot extract the consequent unconditionally from P => Q.
            // The consequent Q only holds when P holds. Treating Q as
            // unconditionally true under-approximates reachable states,
            // which is unsound for reachability analysis (may discard
            // reachable error states and produce false proofs).
            false
        }
        _ => false,
    }
}

/// Check if a single formula node matches a comparison, considering structural
/// equivalences like flipped operands and Eq commutativity.
fn formula_node_matches(formula: &Formula, lhs: &str, op: CmpOp, rhs: &str) -> bool {
    match formula {
        // Direct form: Lt(a, b) matches a < b
        Formula::Lt(a, b) if op == CmpOp::Lt => matches_names(a, lhs) && matches_names(b, rhs),
        // Flipped: Lt(a, b) also matches b > a
        Formula::Lt(a, b) if op == CmpOp::Gt => matches_names(a, rhs) && matches_names(b, lhs),
        Formula::Le(a, b) if op == CmpOp::Le => matches_names(a, lhs) && matches_names(b, rhs),
        // Flipped: Le(a, b) also matches b >= a
        Formula::Le(a, b) if op == CmpOp::Ge => matches_names(a, rhs) && matches_names(b, lhs),
        Formula::Gt(a, b) if op == CmpOp::Gt => matches_names(a, lhs) && matches_names(b, rhs),
        // Flipped: Gt(a, b) also matches b < a
        Formula::Gt(a, b) if op == CmpOp::Lt => matches_names(a, rhs) && matches_names(b, lhs),
        Formula::Ge(a, b) if op == CmpOp::Ge => matches_names(a, lhs) && matches_names(b, rhs),
        // Flipped: Ge(a, b) also matches b <= a
        Formula::Ge(a, b) if op == CmpOp::Le => matches_names(a, rhs) && matches_names(b, lhs),
        // Eq is commutative: Eq(a, b) matches both a == b and b == a
        Formula::Eq(a, b) if op == CmpOp::Eq => {
            (matches_names(a, lhs) && matches_names(b, rhs))
                || (matches_names(a, rhs) && matches_names(b, lhs))
        }
        // Ne via Not(Eq): commutative
        Formula::Not(inner) if op == CmpOp::Ne => {
            if let Formula::Eq(a, b) = inner.as_ref() {
                (matches_names(a, lhs) && matches_names(b, rhs))
                    || (matches_names(a, rhs) && matches_names(b, lhs))
            } else {
                false
            }
        }
        _ => false,
    }
}

/// Check if a formula leaf matches a name string.
fn matches_names(formula: &Formula, name: &str) -> bool {
    match formula {
        Formula::Var(n, _) => n == name,
        Formula::Int(n) => name.parse::<i128>().ok() == Some(*n),
        Formula::Bool(b) => (name == "1" && *b) || (name == "0" && !*b),
        _ => false,
    }
}

/// Boolean abstraction: map concrete states to boolean vectors over predicates.
///
/// Each predicate is assigned a boolean value (true/false/unknown). The
/// abstract state is the conjunction of predicates that evaluate to true.
/// This is the most precise form of predicate abstraction.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BooleanAbstraction {
    /// Boolean vector: one entry per predicate in the set.
    /// `None` = unknown, `Some(true)` = holds, `Some(false)` = negation holds.
    values: Vec<Option<bool>>,
}

impl BooleanAbstraction {
    /// Create a new boolean abstraction with all predicates unknown.
    #[must_use]
    pub fn new_unknown(num_predicates: usize) -> Self {
        Self { values: vec![None; num_predicates] }
    }

    /// Create a boolean abstraction from explicit values.
    #[must_use]
    pub fn from_values(values: Vec<Option<bool>>) -> Self {
        Self { values }
    }

    /// Set a predicate value by index.
    pub fn set(&mut self, index: usize, value: Option<bool>) {
        if index < self.values.len() {
            self.values[index] = value;
        }
    }

    /// Get a predicate value by index.
    #[must_use]
    pub fn get(&self, index: usize) -> Option<bool> {
        self.values.get(index).copied().flatten()
    }

    /// Number of predicates tracked.
    #[must_use]
    pub fn len(&self) -> usize {
        self.values.len()
    }

    /// Whether no predicates are tracked.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.values.is_empty()
    }

    /// Count predicates with known values.
    #[must_use]
    pub fn known_count(&self) -> usize {
        self.values.iter().filter(|v| v.is_some()).count()
    }

    /// Join two boolean abstractions (meet of boolean vectors).
    ///
    /// At merge points: if both agree, keep the value. Otherwise, unknown.
    #[must_use]
    pub fn join(&self, other: &Self) -> Self {
        let len = self.values.len().max(other.values.len());
        let mut result = Vec::with_capacity(len);
        for i in 0..len {
            let a = self.values.get(i).copied().flatten();
            let b = other.values.get(i).copied().flatten();
            result.push(match (a, b) {
                (Some(x), Some(y)) if x == y => Some(x),
                _ => None,
            });
        }
        Self { values: result }
    }

    /// Meet two boolean abstractions (union of known values).
    ///
    /// If either side knows a value, it is propagated.
    #[must_use]
    pub fn meet(&self, other: &Self) -> Self {
        let len = self.values.len().max(other.values.len());
        let mut result = Vec::with_capacity(len);
        for i in 0..len {
            let a = self.values.get(i).copied().flatten();
            let b = other.values.get(i).copied().flatten();
            result.push(a.or(b));
        }
        Self { values: result }
    }

    /// Convert to an AbstractState given a predicate set.
    #[must_use]
    pub fn to_abstract_state(&self, predicates: &PredicateSet) -> AbstractState {
        let mut state = AbstractState::top();
        for (i, val) in self.values.iter().enumerate() {
            if *val == Some(true)
                && let Some(pred) = predicates.get(i)
            {
                state.add(pred.clone());
            }
        }
        state
    }
}

/// Cartesian abstraction: track each predicate independently.
///
/// From CPAchecker: instead of tracking full boolean combinations of
/// predicates (exponential), track each predicate independently. This is
/// less precise but much cheaper. The abstract state is a vector of
/// per-predicate truth values.
///
/// Precision loss: cannot represent correlations between predicates.
/// Example: cannot distinguish "x > 0 AND y > 0" from "x > 0 OR y > 0".
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CartesianAbstraction {
    /// Per-predicate truth value: true, false, or unknown (top).
    values: Vec<CartesianValue>,
}

/// Value in a Cartesian abstraction.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum CartesianValue {
    /// Predicate definitely holds.
    True,
    /// Predicate definitely does not hold.
    False,
    /// Unknown (both possible).
    Unknown,
}

impl CartesianAbstraction {
    /// Create a new Cartesian abstraction with all predicates unknown.
    #[must_use]
    pub fn new_unknown(num_predicates: usize) -> Self {
        Self { values: vec![CartesianValue::Unknown; num_predicates] }
    }

    /// Create from explicit values.
    #[must_use]
    pub fn from_values(values: Vec<CartesianValue>) -> Self {
        Self { values }
    }

    /// Set a predicate value.
    pub fn set(&mut self, index: usize, value: CartesianValue) {
        if index < self.values.len() {
            self.values[index] = value;
        }
    }

    /// Get a predicate value.
    #[must_use]
    pub fn get(&self, index: usize) -> CartesianValue {
        self.values.get(index).copied().unwrap_or(CartesianValue::Unknown)
    }

    /// Number of predicates.
    #[must_use]
    pub fn len(&self) -> usize {
        self.values.len()
    }

    /// Whether no predicates are tracked.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.values.is_empty()
    }

    /// Count of predicates known to be true.
    #[must_use]
    pub fn true_count(&self) -> usize {
        self.values.iter().filter(|v| **v == CartesianValue::True).count()
    }

    /// Join two Cartesian abstractions.
    ///
    /// For each predicate: if both agree, keep the value; otherwise, unknown.
    #[must_use]
    pub fn join(&self, other: &Self) -> Self {
        let len = self.values.len().max(other.values.len());
        let mut result = Vec::with_capacity(len);
        for i in 0..len {
            let a = self.values.get(i).copied().unwrap_or(CartesianValue::Unknown);
            let b = other.values.get(i).copied().unwrap_or(CartesianValue::Unknown);
            result.push(if a == b { a } else { CartesianValue::Unknown });
        }
        Self { values: result }
    }

    /// Meet two Cartesian abstractions.
    ///
    /// Prefer known values over unknown.
    #[must_use]
    pub fn meet(&self, other: &Self) -> Self {
        let len = self.values.len().max(other.values.len());
        let mut result = Vec::with_capacity(len);
        for i in 0..len {
            let a = self.values.get(i).copied().unwrap_or(CartesianValue::Unknown);
            let b = other.values.get(i).copied().unwrap_or(CartesianValue::Unknown);
            result.push(match (a, b) {
                (CartesianValue::Unknown, x) | (x, CartesianValue::Unknown) => x,
                (x, y) if x == y => x,
                // Conflict: True meets False = bottom (contradiction).
                _ => CartesianValue::False,
            });
        }
        Self { values: result }
    }

    /// Convert to an AbstractState given a predicate set.
    #[must_use]
    pub fn to_abstract_state(&self, predicates: &PredicateSet) -> AbstractState {
        let mut state = AbstractState::top();
        for (i, val) in self.values.iter().enumerate() {
            if *val == CartesianValue::True
                && let Some(pred) = predicates.get(i)
            {
                state.add(pred.clone());
            }
        }
        state
    }
}

#[cfg(test)]
mod tests {
    use trust_types::Sort;

    use super::*;

    fn sample_predicates() -> PredicateSet {
        PredicateSet::from_predicates(vec![
            Predicate::comparison("x", CmpOp::Ge, "0"),
            Predicate::comparison("y", CmpOp::Lt, "10"),
            Predicate::non_null("ptr"),
        ])
    }

    // --- PredicateAbstraction tests ---

    #[test]
    fn test_predicate_abstraction_top() {
        let abs = PredicateAbstraction::new(sample_predicates());
        let top = abs.top();
        assert!(top.is_empty());
    }

    #[test]
    fn test_predicate_abstraction_bottom() {
        let abs = PredicateAbstraction::new(sample_predicates());
        let bot = abs.bottom();
        assert!(bot.contains(&Predicate::Custom("__bottom__".into())));
    }

    #[test]
    fn test_predicate_abstraction_join() {
        let abs = PredicateAbstraction::new(sample_predicates());
        let mut a = AbstractState::top();
        let mut b = AbstractState::top();
        let p1 = Predicate::comparison("x", CmpOp::Ge, "0");
        let p2 = Predicate::comparison("y", CmpOp::Lt, "10");
        a.add(p1.clone());
        a.add(p2.clone());
        b.add(p1.clone());
        let joined = abs.join(&a, &b);
        assert!(joined.contains(&p1));
        assert!(!joined.contains(&p2));
    }

    #[test]
    fn test_predicate_abstraction_join_with_bottom() {
        let abs = PredicateAbstraction::new(sample_predicates());
        let bot = abs.bottom();
        let mut a = AbstractState::top();
        a.add(Predicate::comparison("x", CmpOp::Ge, "0"));
        // join(bottom, a) = a
        let result = abs.join(&bot, &a);
        assert!(result.contains(&Predicate::comparison("x", CmpOp::Ge, "0")));
        assert!(!result.contains(&Predicate::Custom("__bottom__".into())));
    }

    #[test]
    fn test_predicate_abstraction_meet() {
        let abs = PredicateAbstraction::new(sample_predicates());
        let mut a = AbstractState::top();
        let mut b = AbstractState::top();
        a.add(Predicate::comparison("x", CmpOp::Ge, "0"));
        b.add(Predicate::comparison("y", CmpOp::Lt, "10"));
        let met = abs.meet(&a, &b);
        assert_eq!(met.len(), 2);
    }

    // --- abstract_state and concretize tests ---

    #[test]
    fn test_abstract_state_from_formula() {
        let preds = PredicateSet::from_predicates(vec![
            Predicate::comparison("x", CmpOp::Ge, "0"),
            Predicate::comparison("y", CmpOp::Lt, "10"),
        ]);
        let formula = Formula::And(vec![Formula::Ge(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        )]);
        let state = abstract_state(&formula, &preds);
        assert!(state.contains(&Predicate::comparison("x", CmpOp::Ge, "0")));
        assert!(!state.contains(&Predicate::comparison("y", CmpOp::Lt, "10")));
    }

    #[test]
    fn test_concretize_empty_state() {
        let state = AbstractState::top();
        let formula = concretize(&state);
        assert_eq!(formula, Formula::Bool(true));
    }

    #[test]
    fn test_concretize_single_predicate() {
        let mut state = AbstractState::top();
        state.add(Predicate::comparison("x", CmpOp::Ge, "0"));
        let formula = concretize(&state);
        // Should produce x >= 0.
        assert!(matches!(formula, Formula::Ge(..)));
    }

    #[test]
    fn test_concretize_multiple_predicates() {
        let mut state = AbstractState::top();
        state.add(Predicate::comparison("x", CmpOp::Ge, "0"));
        state.add(Predicate::comparison("y", CmpOp::Lt, "10"));
        let formula = concretize(&state);
        // Should produce (x >= 0) AND (y < 10).
        assert!(matches!(formula, Formula::And(..)));
    }

    #[test]
    fn test_concretize_range_predicate() {
        let mut state = AbstractState::top();
        state.add(Predicate::range("i", 0, 100));
        let formula = concretize(&state);
        // Range produces an And of two comparisons.
        assert!(matches!(formula, Formula::And(..)));
    }

    // --- BooleanAbstraction tests ---

    #[test]
    fn test_boolean_abstraction_unknown() {
        let ba = BooleanAbstraction::new_unknown(3);
        assert_eq!(ba.len(), 3);
        assert_eq!(ba.known_count(), 0);
        assert_eq!(ba.get(0), None);
    }

    #[test]
    fn test_boolean_abstraction_set_get() {
        let mut ba = BooleanAbstraction::new_unknown(3);
        ba.set(0, Some(true));
        ba.set(1, Some(false));
        assert_eq!(ba.get(0), Some(true));
        assert_eq!(ba.get(1), Some(false));
        assert_eq!(ba.get(2), None);
        assert_eq!(ba.known_count(), 2);
    }

    #[test]
    fn test_boolean_abstraction_join() {
        let a = BooleanAbstraction::from_values(vec![Some(true), Some(false), Some(true)]);
        let b = BooleanAbstraction::from_values(vec![Some(true), Some(true), Some(true)]);
        let joined = a.join(&b);
        assert_eq!(joined.get(0), Some(true)); // both true
        assert_eq!(joined.get(1), None); // disagree
        assert_eq!(joined.get(2), Some(true)); // both true
    }

    #[test]
    fn test_boolean_abstraction_meet() {
        let a = BooleanAbstraction::from_values(vec![Some(true), None, Some(false)]);
        let b = BooleanAbstraction::from_values(vec![None, Some(true), None]);
        let met = a.meet(&b);
        assert_eq!(met.get(0), Some(true));
        assert_eq!(met.get(1), Some(true));
        assert_eq!(met.get(2), Some(false));
    }

    #[test]
    fn test_boolean_abstraction_to_abstract_state() {
        let preds = sample_predicates();
        let ba = BooleanAbstraction::from_values(vec![Some(true), Some(false), Some(true)]);
        let state = ba.to_abstract_state(&preds);
        assert!(state.contains(&Predicate::comparison("x", CmpOp::Ge, "0")));
        assert!(!state.contains(&Predicate::comparison("y", CmpOp::Lt, "10")));
        assert!(state.contains(&Predicate::non_null("ptr")));
    }

    // --- CartesianAbstraction tests ---

    #[test]
    fn test_cartesian_unknown() {
        let ca = CartesianAbstraction::new_unknown(3);
        assert_eq!(ca.len(), 3);
        assert_eq!(ca.true_count(), 0);
        assert_eq!(ca.get(0), CartesianValue::Unknown);
    }

    #[test]
    fn test_cartesian_set_get() {
        let mut ca = CartesianAbstraction::new_unknown(3);
        ca.set(0, CartesianValue::True);
        ca.set(1, CartesianValue::False);
        assert_eq!(ca.get(0), CartesianValue::True);
        assert_eq!(ca.get(1), CartesianValue::False);
        assert_eq!(ca.get(2), CartesianValue::Unknown);
        assert_eq!(ca.true_count(), 1);
    }

    #[test]
    fn test_cartesian_join_agree() {
        let a = CartesianAbstraction::from_values(vec![
            CartesianValue::True,
            CartesianValue::False,
            CartesianValue::True,
        ]);
        let b = CartesianAbstraction::from_values(vec![
            CartesianValue::True,
            CartesianValue::True,
            CartesianValue::True,
        ]);
        let joined = a.join(&b);
        assert_eq!(joined.get(0), CartesianValue::True);
        assert_eq!(joined.get(1), CartesianValue::Unknown); // disagree
        assert_eq!(joined.get(2), CartesianValue::True);
    }

    #[test]
    fn test_cartesian_meet_prefer_known() {
        let a = CartesianAbstraction::from_values(vec![
            CartesianValue::True,
            CartesianValue::Unknown,
            CartesianValue::False,
        ]);
        let b = CartesianAbstraction::from_values(vec![
            CartesianValue::Unknown,
            CartesianValue::True,
            CartesianValue::Unknown,
        ]);
        let met = a.meet(&b);
        assert_eq!(met.get(0), CartesianValue::True);
        assert_eq!(met.get(1), CartesianValue::True);
        assert_eq!(met.get(2), CartesianValue::False);
    }

    #[test]
    fn test_cartesian_meet_conflict() {
        let a = CartesianAbstraction::from_values(vec![CartesianValue::True]);
        let b = CartesianAbstraction::from_values(vec![CartesianValue::False]);
        let met = a.meet(&b);
        assert_eq!(met.get(0), CartesianValue::False); // conflict -> bottom
    }

    #[test]
    fn test_cartesian_to_abstract_state() {
        let preds = sample_predicates();
        let ca = CartesianAbstraction::from_values(vec![
            CartesianValue::True,
            CartesianValue::Unknown,
            CartesianValue::True,
        ]);
        let state = ca.to_abstract_state(&preds);
        assert!(state.contains(&Predicate::comparison("x", CmpOp::Ge, "0")));
        assert!(!state.contains(&Predicate::comparison("y", CmpOp::Lt, "10")));
        assert!(state.contains(&Predicate::non_null("ptr")));
    }

    #[test]
    fn test_cartesian_different_lengths() {
        let a = CartesianAbstraction::from_values(vec![CartesianValue::True]);
        let b =
            CartesianAbstraction::from_values(vec![CartesianValue::True, CartesianValue::False]);
        let joined = a.join(&b);
        assert_eq!(joined.len(), 2);
        assert_eq!(joined.get(0), CartesianValue::True);
        assert_eq!(joined.get(1), CartesianValue::Unknown);
    }

    // --- Structural implication tests ---

    #[test]
    fn test_formula_implies_comparison() {
        let formula =
            Formula::Ge(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(0)));
        let pred = Predicate::comparison("x", CmpOp::Ge, "0");
        assert!(formula_implies_predicate(&formula, &pred));
    }

    #[test]
    fn test_formula_does_not_imply_unrelated() {
        let formula =
            Formula::Ge(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(0)));
        let pred = Predicate::comparison("y", CmpOp::Lt, "10");
        assert!(!formula_implies_predicate(&formula, &pred));
    }

    // --- Structural matching tests (tRust #412) ---

    #[test]
    fn test_formula_flipped_lt_matches_gt_predicate() {
        // Formula: Lt(x, 10) should match predicate 10 > x
        let formula =
            Formula::Lt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(10)));
        let pred = Predicate::comparison("10", CmpOp::Gt, "x");
        assert!(formula_implies_predicate(&formula, &pred));
    }

    #[test]
    fn test_formula_flipped_ge_matches_le_predicate() {
        // Formula: Ge(x, 0) should match predicate 0 <= x
        let formula =
            Formula::Ge(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(0)));
        let pred = Predicate::comparison("0", CmpOp::Le, "x");
        assert!(formula_implies_predicate(&formula, &pred));
    }

    #[test]
    fn test_formula_eq_commutative() {
        // Formula: Eq(x, 5) should match predicate 5 == x
        let formula =
            Formula::Eq(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(5)));
        let pred = Predicate::comparison("5", CmpOp::Eq, "x");
        assert!(formula_implies_predicate(&formula, &pred));
    }

    #[test]
    fn test_formula_ne_commutative() {
        // Formula: Not(Eq(x, 0)) should match predicate 0 != x
        let formula = Formula::Not(Box::new(Formula::Eq(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        )));
        let pred = Predicate::comparison("0", CmpOp::Ne, "x");
        assert!(formula_implies_predicate(&formula, &pred));
    }

    #[test]
    fn test_formula_or_all_branches_imply() {
        // Or(x >= 0, x >= 0) => implies x >= 0
        let formula = Formula::Or(vec![
            Formula::Ge(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(0))),
            Formula::Ge(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(0))),
        ]);
        assert!(formula_implies_predicate(&formula, &Predicate::comparison("x", CmpOp::Ge, "0"),));
    }

    #[test]
    fn test_formula_or_not_all_branches() {
        // Or(x >= 0, y < 10) does NOT imply x >= 0
        let formula = Formula::Or(vec![
            Formula::Ge(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(0))),
            Formula::Lt(Box::new(Formula::Var("y".into(), Sort::Int)), Box::new(Formula::Int(10))),
        ]);
        assert!(!formula_implies_predicate(&formula, &Predicate::comparison("x", CmpOp::Ge, "0"),));
    }

    #[test]
    fn test_formula_implies_does_not_extract_consequent() {
        // #778: Implies(P, Q) does NOT unconditionally contain Q.
        // Q only holds when P holds. Treating Q as unconditional was
        // a soundness bug that could discard reachable error states.
        let formula = Formula::Implies(
            Box::new(Formula::Bool(true)),
            Box::new(Formula::Ge(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            )),
        );
        assert!(!formula_implies_predicate(&formula, &Predicate::comparison("x", CmpOp::Ge, "0"),));
    }

    #[test]
    fn test_formula_implies_in_conjunction() {
        let formula = Formula::And(vec![
            Formula::Ge(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(0))),
            Formula::Lt(Box::new(Formula::Var("y".into(), Sort::Int)), Box::new(Formula::Int(10))),
        ]);
        assert!(formula_implies_predicate(&formula, &Predicate::comparison("x", CmpOp::Ge, "0"),));
        assert!(formula_implies_predicate(&formula, &Predicate::comparison("y", CmpOp::Lt, "10"),));
    }
}
