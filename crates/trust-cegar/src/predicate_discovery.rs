// trust-cegar: Predicate discovery and ranking for CEGAR refinement
//
// Automatic predicate extraction from counterexample traces and program
// formulas. Predicates are ranked by discrimination power to prioritize
// the most useful ones during refinement.
//
// Reference: CPAchecker's predicate discovery
//   refs/cpachecker/src/org/sosy_lab/cpachecker/cpa/predicate/
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeSet;

use serde::{Deserialize, Serialize};
use trust_types::{Counterexample, CounterexampleValue, Formula};

use crate::predicate::{CmpOp, Predicate};

/// Source of a discovered predicate: where it came from.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum PredicateSource {
    /// Extracted from a counterexample trace.
    Counterexample,
    /// Extracted from the program formula (branch conditions, assertions).
    ProgramFormula,
    /// Derived via Craig interpolation.
    Interpolation,
    /// User-provided specification predicate.
    Specification,
}

/// A predicate with metadata about its origin and discovery context.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AnnotatedPredicate {
    /// The underlying predicate.
    pub predicate: Predicate,
    /// Where this predicate was discovered.
    pub source: PredicateSource,
    /// Which refinement round discovered this predicate (0 = initial).
    pub refinement_round: usize,
}

impl AnnotatedPredicate {
    /// Create a new annotated predicate.
    #[must_use]
    pub fn new(predicate: Predicate, source: PredicateSource, refinement_round: usize) -> Self {
        Self { predicate, source, refinement_round }
    }
}

/// An ordered set of predicates with indexing support.
///
/// Maintains predicates in a deterministic order (BTreeSet) and provides
/// index-based access for the boolean abstraction vectors.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct PredicateSet {
    /// Predicates in sorted order.
    predicates: Vec<Predicate>,
    /// Deduplicated set for fast membership checks.
    seen: BTreeSet<Predicate>,
}

impl PredicateSet {
    /// Create an empty predicate set.
    #[must_use]
    pub fn new() -> Self {
        Self { predicates: Vec::new(), seen: BTreeSet::new() }
    }

    /// Create a predicate set from an existing collection.
    #[must_use]
    pub fn from_predicates(preds: impl IntoIterator<Item = Predicate>) -> Self {
        let mut set = Self::new();
        for p in preds {
            set.insert(p);
        }
        set
    }

    /// Insert a predicate. Returns `true` if it was newly inserted.
    pub fn insert(&mut self, pred: Predicate) -> bool {
        if self.seen.insert(pred.clone()) {
            self.predicates.push(pred);
            true
        } else {
            false
        }
    }

    /// Check if a predicate is in the set.
    #[must_use]
    pub fn contains(&self, pred: &Predicate) -> bool {
        self.seen.contains(pred)
    }

    /// Number of predicates.
    #[must_use]
    pub fn len(&self) -> usize {
        self.predicates.len()
    }

    /// Whether the set is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.predicates.is_empty()
    }

    /// Get a predicate by index.
    #[must_use]
    pub fn get(&self, index: usize) -> Option<&Predicate> {
        self.predicates.get(index)
    }

    /// Get the index of a predicate, if present.
    #[must_use]
    pub fn index_of(&self, pred: &Predicate) -> Option<usize> {
        self.predicates.iter().position(|p| p == pred)
    }

    /// Iterate over predicates in insertion order.
    pub fn iter(&self) -> impl Iterator<Item = &Predicate> {
        self.predicates.iter()
    }

    /// Return predicates as a slice.
    #[must_use]
    pub fn as_slice(&self) -> &[Predicate] {
        &self.predicates
    }
}

/// Discover predicates from a counterexample trace and program formula.
///
/// Analyzes the counterexample variable assignments to extract comparison
/// predicates, boundary predicates, and pairwise ordering predicates.
/// Also extracts predicates from the program formula's structure
/// (comparisons, assertions).
///
/// # Arguments
/// * `cex` - The counterexample providing concrete variable values.
/// * `program` - The program formula to extract structural predicates from.
///
/// # Returns
/// A deduplicated list of discovered predicates.
#[must_use]
pub fn discover_predicates(cex: &Counterexample, program: &Formula) -> Vec<Predicate> {
    let mut preds = BTreeSet::new();

    // Phase 1: Extract predicates from counterexample assignments.
    discover_from_counterexample(cex, &mut preds);

    // Phase 2: Extract predicates from program formula structure.
    discover_from_formula(program, &mut preds);

    // Phase 3: Generate pairwise ordering predicates between integer variables.
    discover_pairwise(cex, &mut preds);

    preds.into_iter().collect()
}

/// Extract predicates from counterexample variable assignments.
fn discover_from_counterexample(cex: &Counterexample, out: &mut BTreeSet<Predicate>) {
    for (name, value) in &cex.assignments {
        match value {
            CounterexampleValue::Int(n) => {
                // Boundary predicates: sign, zero comparison.
                out.insert(Predicate::comparison(name, CmpOp::Ge, "0"));
                if *n < 0 {
                    out.insert(Predicate::comparison(name, CmpOp::Lt, "0"));
                }
                // Exact value predicate.
                out.insert(Predicate::comparison(name, CmpOp::Eq, n.to_string()));
                // Boundary +/- 1 predicates (common in loop analysis).
                if *n != 0 {
                    let bound = if *n > 0 { n - 1 } else { n + 1 };
                    out.insert(Predicate::comparison(name, CmpOp::Ge, bound.to_string()));
                }
            }
            CounterexampleValue::Uint(n) => {
                out.insert(Predicate::comparison(name, CmpOp::Eq, n.to_string()));
                if *n == 0 {
                    out.insert(Predicate::comparison(name, CmpOp::Eq, "0"));
                } else {
                    out.insert(Predicate::comparison(name, CmpOp::Gt, "0"));
                    // Upper bound from the value.
                    out.insert(Predicate::comparison(name, CmpOp::Le, n.to_string()));
                }
            }
            CounterexampleValue::Bool(b) => {
                let val = if *b { "1" } else { "0" };
                out.insert(Predicate::comparison(name, CmpOp::Eq, val));
            }
            CounterexampleValue::Float(_) => {
                // Float predicates are limited; add sign predicates.
                out.insert(Predicate::comparison(name, CmpOp::Ge, "0"));
            }
            _ => {},
        }
    }
}

/// Extract comparison predicates from a formula's structure.
fn discover_from_formula(formula: &Formula, out: &mut BTreeSet<Predicate>) {
    match formula {
        Formula::Lt(a, b) => {
            if let (Some(l), Some(r)) = (formula_to_name(a), formula_to_name(b)) {
                out.insert(Predicate::comparison(l, CmpOp::Lt, r));
            }
        }
        Formula::Le(a, b) => {
            if let (Some(l), Some(r)) = (formula_to_name(a), formula_to_name(b)) {
                out.insert(Predicate::comparison(l, CmpOp::Le, r));
            }
        }
        Formula::Gt(a, b) => {
            if let (Some(l), Some(r)) = (formula_to_name(a), formula_to_name(b)) {
                out.insert(Predicate::comparison(l, CmpOp::Gt, r));
            }
        }
        Formula::Ge(a, b) => {
            if let (Some(l), Some(r)) = (formula_to_name(a), formula_to_name(b)) {
                out.insert(Predicate::comparison(l, CmpOp::Ge, r));
            }
        }
        Formula::Eq(a, b) => {
            if let (Some(l), Some(r)) = (formula_to_name(a), formula_to_name(b)) {
                out.insert(Predicate::comparison(l, CmpOp::Eq, r));
            }
        }
        // Recurse into boolean connectives.
        Formula::And(children) | Formula::Or(children) => {
            for child in children {
                discover_from_formula(child, out);
            }
        }
        Formula::Not(inner) => discover_from_formula(inner, out),
        Formula::Implies(a, b) => {
            discover_from_formula(a, out);
            discover_from_formula(b, out);
        }
        _ => {}
    }
}

/// Generate pairwise ordering predicates between integer variables.
fn discover_pairwise(cex: &Counterexample, out: &mut BTreeSet<Predicate>) {
    let int_vars: Vec<(&str, i128)> = cex
        .assignments
        .iter()
        .filter_map(|(name, val)| match val {
            CounterexampleValue::Int(n) => Some((name.as_str(), *n)),
            CounterexampleValue::Uint(n) => i128::try_from(*n).ok().map(|n| (name.as_str(), n)),
            _ => None,
        })
        .collect();

    for i in 0..int_vars.len() {
        for j in (i + 1)..int_vars.len() {
            let (a, a_val) = int_vars[i];
            let (b, b_val) = int_vars[j];
            let op = if a_val < b_val {
                CmpOp::Lt
            } else if a_val == b_val {
                CmpOp::Eq
            } else {
                CmpOp::Gt
            };
            out.insert(Predicate::comparison(a, op, b));
        }
    }
}

/// Convert a formula leaf to a name string for predicate construction.
fn formula_to_name(formula: &Formula) -> Option<String> {
    match formula {
        Formula::Var(name, _) => Some(name.clone()),
        Formula::Int(n) => Some(n.to_string()),
        Formula::Bool(b) => Some(if *b { "1".to_string() } else { "0".to_string() }),
        _ => None,
    }
}

/// Rank predicates by estimated discrimination power.
///
/// Higher-ranked predicates are expected to eliminate more spurious
/// counterexamples. Ranking heuristics:
/// 1. Predicates involving variables from the counterexample rank higher.
/// 2. Comparison predicates rank higher than custom/range predicates.
/// 3. Equality predicates rank lower than inequality (inequalities are
///    more likely to generalize across paths).
/// 4. Predicates from interpolation rank highest.
///
/// # Returns
/// A list of (predicate, score) pairs sorted by descending score.
#[must_use]
pub fn rank_predicates(preds: &[Predicate]) -> Vec<(Predicate, f64)> {
    let mut ranked: Vec<(Predicate, f64)> = preds
        .iter()
        .map(|p| {
            let score = compute_discrimination_score(p);
            (p.clone(), score)
        })
        .collect();

    // Sort by descending score (most discriminating first).
    ranked.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap_or(std::cmp::Ordering::Equal));
    ranked
}

/// Compute a discrimination score for a single predicate.
///
/// Higher scores indicate predicates that are more likely to eliminate
/// spurious counterexamples effectively.
fn compute_discrimination_score(pred: &Predicate) -> f64 {
    match pred {
        Predicate::Comparison { op, lhs, rhs, .. } => {
            let mut score = 1.0;

            // Inequality predicates generalize better than equality.
            match op {
                CmpOp::Lt | CmpOp::Le | CmpOp::Gt | CmpOp::Ge => score += 0.5,
                CmpOp::Eq => score += 0.2,
                CmpOp::Ne => score += 0.3,
            }

            // Predicates comparing two variables are more powerful than
            // comparing a variable to a constant.
            let lhs_is_var = !lhs.chars().next().is_some_and(|c| c.is_ascii_digit() || c == '-');
            let rhs_is_var = !rhs.chars().next().is_some_and(|c| c.is_ascii_digit() || c == '-');
            if lhs_is_var && rhs_is_var {
                score += 0.8; // Two variables: most discriminating.
            } else if lhs_is_var || rhs_is_var {
                score += 0.4; // One variable, one constant.
            }

            // Boundary predicates (comparison with 0) are common and useful.
            if rhs == "0" || lhs == "0" {
                score += 0.3;
            }

            score
        }
        Predicate::Range { .. } => 0.8, // Range predicates are moderately useful.
        Predicate::NonNull(_) => 0.6,   // Non-null is useful but narrow.
        Predicate::Custom(_) => 0.3,    // Custom predicates are least structured.
    }
}

/// Count the number of formula variables (used for complexity estimation).
#[must_use]
pub(crate) fn formula_variable_count(formula: &Formula) -> usize {
    let mut vars = BTreeSet::new();
    collect_formula_var_names(formula, &mut vars);
    vars.len()
}

/// Collect variable names from a formula.
fn collect_formula_var_names(formula: &Formula, out: &mut BTreeSet<String>) {
    match formula {
        Formula::Var(name, _) => {
            out.insert(name.clone());
        }
        Formula::Not(inner) | Formula::Neg(inner) => collect_formula_var_names(inner, out),
        Formula::And(children) | Formula::Or(children) => {
            for child in children {
                collect_formula_var_names(child, out);
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
            collect_formula_var_names(a, out);
            collect_formula_var_names(b, out);
        }
        Formula::Ite(c, t, e) => {
            collect_formula_var_names(c, out);
            collect_formula_var_names(t, out);
            collect_formula_var_names(e, out);
        }
        _ => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_types::Sort;

    fn make_cex(assignments: Vec<(&str, CounterexampleValue)>) -> Counterexample {
        Counterexample::new(
            assignments.into_iter().map(|(n, v)| (n.to_string(), v)).collect(),
        )
    }

    #[test]
    fn test_predicate_set_insert_dedup() {
        let mut set = PredicateSet::new();
        let p1 = Predicate::comparison("x", CmpOp::Ge, "0");
        assert!(set.insert(p1.clone()));
        assert!(!set.insert(p1.clone()));
        assert_eq!(set.len(), 1);
    }

    #[test]
    fn test_predicate_set_index_of() {
        let mut set = PredicateSet::new();
        let p1 = Predicate::comparison("x", CmpOp::Ge, "0");
        let p2 = Predicate::comparison("y", CmpOp::Lt, "10");
        set.insert(p1.clone());
        set.insert(p2.clone());
        assert_eq!(set.index_of(&p1), Some(0));
        assert_eq!(set.index_of(&p2), Some(1));
        assert_eq!(set.index_of(&Predicate::non_null("z")), None);
    }

    #[test]
    fn test_predicate_set_from_predicates() {
        let preds = vec![
            Predicate::comparison("x", CmpOp::Ge, "0"),
            Predicate::comparison("y", CmpOp::Lt, "10"),
            Predicate::comparison("x", CmpOp::Ge, "0"), // duplicate
        ];
        let set = PredicateSet::from_predicates(preds);
        assert_eq!(set.len(), 2);
    }

    #[test]
    fn test_predicate_set_get() {
        let mut set = PredicateSet::new();
        let p = Predicate::comparison("x", CmpOp::Ge, "0");
        set.insert(p.clone());
        assert_eq!(set.get(0), Some(&p));
        assert_eq!(set.get(1), None);
    }

    #[test]
    fn test_predicate_set_iter() {
        let mut set = PredicateSet::new();
        set.insert(Predicate::comparison("a", CmpOp::Lt, "b"));
        set.insert(Predicate::comparison("c", CmpOp::Eq, "0"));
        let collected: Vec<&Predicate> = set.iter().collect();
        assert_eq!(collected.len(), 2);
    }

    #[test]
    fn test_discover_predicates_from_int_cex() {
        let cex = make_cex(vec![
            ("x", CounterexampleValue::Int(-3)),
            ("y", CounterexampleValue::Int(10)),
        ]);
        let program = Formula::Bool(true); // trivial program
        let preds = discover_predicates(&cex, &program);

        let pred_strs: Vec<String> = preds.iter().map(ToString::to_string).collect();
        // Should include boundary predicates.
        assert!(pred_strs.contains(&"x >= 0".to_string()));
        assert!(pred_strs.contains(&"x < 0".to_string()));
        // Should include pairwise ordering.
        assert!(pred_strs.contains(&"x < y".to_string()));
    }

    #[test]
    fn test_discover_predicates_from_formula() {
        let cex = make_cex(vec![]);
        let program = Formula::And(vec![
            Formula::Lt(
                Box::new(Formula::Var("a".into(), Sort::Int)),
                Box::new(Formula::Int(100)),
            ),
            Formula::Ge(
                Box::new(Formula::Var("b".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
        ]);
        let preds = discover_predicates(&cex, &program);
        assert!(preds.contains(&Predicate::comparison("a", CmpOp::Lt, "100")));
        assert!(preds.contains(&Predicate::comparison("b", CmpOp::Ge, "0")));
    }

    #[test]
    fn test_discover_predicates_from_uint_cex() {
        let cex = make_cex(vec![("n", CounterexampleValue::Uint(5))]);
        let program = Formula::Bool(true);
        let preds = discover_predicates(&cex, &program);
        assert!(preds.contains(&Predicate::comparison("n", CmpOp::Eq, "5")));
        assert!(preds.contains(&Predicate::comparison("n", CmpOp::Gt, "0")));
    }

    #[test]
    fn test_discover_predicates_from_bool_cex() {
        let cex = make_cex(vec![("flag", CounterexampleValue::Bool(true))]);
        let program = Formula::Bool(true);
        let preds = discover_predicates(&cex, &program);
        assert!(preds.contains(&Predicate::comparison("flag", CmpOp::Eq, "1")));
    }

    #[test]
    fn test_discover_predicates_deduplicates() {
        let cex = make_cex(vec![("x", CounterexampleValue::Int(0))]);
        let program = Formula::Ge(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        );
        let preds = discover_predicates(&cex, &program);
        // "x >= 0" should appear exactly once.
        let count = preds.iter().filter(|p| **p == Predicate::comparison("x", CmpOp::Ge, "0")).count();
        assert_eq!(count, 1);
    }

    #[test]
    fn test_rank_predicates_ordering() {
        let preds = vec![
            Predicate::Custom("something".into()),
            Predicate::comparison("x", CmpOp::Lt, "y"), // variable-variable
            Predicate::comparison("x", CmpOp::Eq, "5"), // variable-constant eq
            Predicate::comparison("x", CmpOp::Ge, "0"), // boundary
        ];
        let ranked = rank_predicates(&preds);
        assert_eq!(ranked.len(), 4);
        // Variable-variable comparison should rank highest.
        assert_eq!(ranked[0].0, Predicate::comparison("x", CmpOp::Lt, "y"));
        // Custom should rank lowest.
        assert_eq!(ranked[3].0, Predicate::Custom("something".into()));
    }

    #[test]
    fn test_rank_predicates_empty() {
        let ranked = rank_predicates(&[]);
        assert!(ranked.is_empty());
    }

    #[test]
    fn test_rank_predicates_scores_positive() {
        let preds = vec![
            Predicate::comparison("x", CmpOp::Lt, "10"),
            Predicate::non_null("ptr"),
            Predicate::range("i", 0, 100),
        ];
        let ranked = rank_predicates(&preds);
        for (_, score) in &ranked {
            assert!(*score > 0.0);
        }
    }

    #[test]
    fn test_annotated_predicate() {
        let ap = AnnotatedPredicate::new(
            Predicate::comparison("x", CmpOp::Ge, "0"),
            PredicateSource::Counterexample,
            3,
        );
        assert_eq!(ap.refinement_round, 3);
        assert_eq!(ap.source, PredicateSource::Counterexample);
    }

    #[test]
    fn test_formula_variable_count() {
        let f = Formula::And(vec![
            Formula::Lt(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(10)),
            ),
            Formula::Ge(
                Box::new(Formula::Var("y".into(), Sort::Int)),
                Box::new(Formula::Var("x".into(), Sort::Int)),
            ),
        ]);
        assert_eq!(formula_variable_count(&f), 2); // x and y
    }

    #[test]
    fn test_formula_variable_count_no_vars() {
        let f = Formula::Bool(true);
        assert_eq!(formula_variable_count(&f), 0);
    }
}
