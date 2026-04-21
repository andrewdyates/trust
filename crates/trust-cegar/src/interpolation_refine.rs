// trust-cegar: Interpolation-based CEGAR predicate refinement
//
// Builds on the basic Craig interpolation in `interpolation.rs` to provide:
//   - Structured interpolants bridging pre/post conditions
//   - Query partitioning into A/B clause sets
//   - Multi-step (sequence) interpolation for path refinement
//   - Memoization cache for interpolation results
//   - Predicate refinement from interpolants
//
// Theory: Given a spurious counterexample path p0 -> p1 -> ... -> pN,
// sequence interpolation produces interpolants I1, ..., I(N-1) such that
// each Ii separates the prefix p0..pi from the suffix p(i+1)..pN.
// These interpolants become new predicates that refine the abstraction.
//
// Reference: CPAchecker's lazy abstraction with interpolants
//   refs/cpachecker/src/org/sosy_lab/cpachecker/cpa/predicate/
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::{FxHashMap, FxHashSet};

use trust_types::Formula;

use crate::error::CegarError;
use crate::interpolation::{UnsatCore, craig_interpolant, formula_variables};
use crate::predicate::Predicate;

// ---------------------------------------------------------------------------
// Core types
// ---------------------------------------------------------------------------

/// A Craig interpolant: a formula that bridges pre and post conditions.
///
/// Given partitions A and B where A /\ B is unsatisfiable:
///   - A |= interpolant
///   - interpolant /\ B is unsatisfiable
///   - interpolant uses only symbols common to A and B
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct Interpolant {
    /// The interpolant formula.
    pub(crate) formula: Formula,
    /// Variables appearing in the interpolant (subset of shared variables).
    pub(crate) variables: Vec<String>,
    /// Predicates extracted from this interpolant.
    pub(crate) predicates: Vec<Predicate>,
}

impl Interpolant {
    /// Create an interpolant from a formula, automatically extracting variables
    /// and predicates.
    #[must_use]
    pub(crate) fn new(formula: Formula, predicates: Vec<Predicate>) -> Self {
        let variables = formula_variables(&formula);
        Self { formula, variables, predicates }
    }

    /// Whether this interpolant is trivially true.
    #[must_use]
    pub(crate) fn is_trivial(&self) -> bool {
        matches!(self.formula, Formula::Bool(true)) || self.predicates.is_empty()
    }

    /// Number of predicates extracted from this interpolant.
    #[must_use]
    pub(crate) fn predicate_count(&self) -> usize {
        self.predicates.len()
    }
}

/// A partition of clauses into A (prefix) and B (suffix) for interpolation.
///
/// The partition represents a cut point along a counterexample path.
#[derive(Debug, Clone)]
pub(crate) struct InterpolationQuery {
    /// Named formulas for the prefix (A-side).
    pub(crate) a_clauses: Vec<(String, Formula)>,
    /// Named formulas for the suffix (B-side).
    pub(crate) b_clauses: Vec<(String, Formula)>,
}

impl InterpolationQuery {
    /// Create a new interpolation query from A and B clause sets.
    #[must_use]
    pub(crate) fn new(
        a_clauses: Vec<(String, Formula)>,
        b_clauses: Vec<(String, Formula)>,
    ) -> Self {
        Self { a_clauses, b_clauses }
    }

    /// Variables shared between A and B clauses.
    #[must_use]
    pub(crate) fn shared_variables(&self) -> Vec<String> {
        let a_vars: FxHashSet<String> = self
            .a_clauses
            .iter()
            .flat_map(|(_, f)| formula_variables(f))
            .collect();
        let b_vars: FxHashSet<String> = self
            .b_clauses
            .iter()
            .flat_map(|(_, f)| formula_variables(f))
            .collect();
        let mut shared: Vec<String> = a_vars.intersection(&b_vars).cloned().collect();
        shared.sort();
        shared
    }

    /// Total number of clauses in both partitions.
    #[must_use]
    pub(crate) fn clause_count(&self) -> usize {
        self.a_clauses.len() + self.b_clauses.len()
    }

    /// A stable cache key derived from the query structure.
    #[must_use]
    fn cache_key(&self) -> InterpolationCacheKey {
        let a_labels: Vec<String> = self.a_clauses.iter().map(|(l, _)| l.clone()).collect();
        let b_labels: Vec<String> = self.b_clauses.iter().map(|(l, _)| l.clone()).collect();
        InterpolationCacheKey { a_labels, b_labels }
    }
}

/// Result of an interpolation computation.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub(crate) enum InterpolationResult {
    /// An interpolant was successfully computed.
    Found(Interpolant),
    /// No interpolant exists (A /\ B is satisfiable).
    NoInterpolant,
    /// The computation timed out.
    Timeout,
}

impl InterpolationResult {
    /// Whether an interpolant was found.
    #[must_use]
    pub(crate) fn is_found(&self) -> bool {
        matches!(self, Self::Found(_))
    }

    /// Extract the interpolant if found.
    #[must_use]
    pub(crate) fn interpolant(&self) -> Option<&Interpolant> {
        match self {
            Self::Found(i) => Some(i),
            _ => None,
        }
    }
}

// ---------------------------------------------------------------------------
// Cache
// ---------------------------------------------------------------------------

/// Cache key based on clause label sets.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct InterpolationCacheKey {
    a_labels: Vec<String>,
    b_labels: Vec<String>,
}

/// Memoization cache for interpolation results.
///
/// Avoids redundant solver calls when the same partition is queried multiple
/// times during iterative refinement.
#[derive(Debug, Clone)]
pub(crate) struct InterpolationCache {
    entries: FxHashMap<InterpolationCacheKey, InterpolationResult>,
    hits: usize,
    misses: usize,
}

impl Default for InterpolationCache {
    fn default() -> Self {
        Self::new()
    }
}

impl InterpolationCache {
    /// Create an empty cache.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self { entries: FxHashMap::default(), hits: 0, misses: 0 }
    }

    /// Look up a cached result for the given query.
    pub(crate) fn get(&mut self, query: &InterpolationQuery) -> Option<&InterpolationResult> {
        let key = query.cache_key();
        if self.entries.contains_key(&key) {
            self.hits += 1;
            self.entries.get(&key)
        } else {
            self.misses += 1;
            None
        }
    }

    /// Insert a result into the cache.
    pub(crate) fn insert(&mut self, query: &InterpolationQuery, result: InterpolationResult) {
        let key = query.cache_key();
        self.entries.insert(key, result);
    }

    /// Number of cached entries.
    #[must_use]
    pub(crate) fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether the cache is empty.
    #[must_use]
    pub(crate) fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Cache hit count.
    #[must_use]
    pub(crate) fn hit_count(&self) -> usize {
        self.hits
    }

    /// Cache miss count.
    #[must_use]
    pub(crate) fn miss_count(&self) -> usize {
        self.misses
    }

    /// Hit rate as a fraction in [0.0, 1.0].
    #[must_use]
    pub(crate) fn hit_rate(&self) -> f64 {
        let total = self.hits + self.misses;
        if total == 0 { 0.0 } else { self.hits as f64 / total as f64 }
    }

    /// Clear all cached entries and reset counters.
    pub(crate) fn clear(&mut self) {
        self.entries.clear();
        self.hits = 0;
        self.misses = 0;
    }
}

// ---------------------------------------------------------------------------
// Core interpolation functions
// ---------------------------------------------------------------------------

/// Compute an interpolant for a given query using an unsat core.
///
/// Delegates to `craig_interpolant` from the base interpolation module,
/// wrapping the result in the structured `InterpolationResult` type.
///
/// # Arguments
/// * `query` - The A/B clause partition.
/// * `unsat_core` - The unsat core from checking A /\ B.
///
/// # Errors
/// Returns `CegarError::SolverError` if the unsat core references unknown labels.
pub(crate) fn compute_interpolant(
    query: &InterpolationQuery,
    unsat_core: &UnsatCore,
) -> Result<InterpolationResult, CegarError> {
    if unsat_core.is_empty() {
        return Ok(InterpolationResult::NoInterpolant);
    }

    let predicates = craig_interpolant(&query.a_clauses, &query.b_clauses, unsat_core)?;

    if predicates.is_empty() {
        return Ok(InterpolationResult::NoInterpolant);
    }

    // Build an interpolant formula from the extracted predicates.
    let formula = predicates_to_formula(&predicates);
    let interpolant = Interpolant::new(formula, predicates);

    Ok(InterpolationResult::Found(interpolant))
}

/// Refine the current predicate set using interpolants.
///
/// Given existing predicates and a set of interpolation results, extract
/// new predicates that are not already tracked. Returns only the newly
/// discovered predicates.
///
/// # Arguments
/// * `existing` - Predicates already in the abstract domain.
/// * `interpolants` - Interpolation results from counterexample analysis.
#[must_use]
pub(crate) fn refine_predicates(
    existing: &[Predicate],
    interpolants: &[InterpolationResult],
) -> Vec<Predicate> {
    let existing_set: FxHashSet<&Predicate> = existing.iter().collect();

    let mut new_predicates: Vec<Predicate> = interpolants
        .iter()
        .filter_map(InterpolationResult::interpolant)
        .flat_map(|interp| interp.predicates.iter())
        .filter(|p| !existing_set.contains(p))
        .cloned()
        .collect();

    new_predicates.sort();
    new_predicates.dedup();
    new_predicates
}

/// Perform sequence interpolation over a counterexample path.
///
/// Given a path of N steps (formulas), compute interpolants at each cut point
/// between consecutive steps. This produces N-1 interpolants I1, ..., I(N-1)
/// such that:
///   - step_0 |= I1
///   - Ii /\ step_i |= I(i+1) for each i
///   - I(N-1) /\ step_(N-1) is unsatisfiable
///
/// Each step is given as `(label, formula)`. The unsat cores for each partition
/// are supplied externally (one per cut point).
///
/// # Arguments
/// * `path_steps` - Ordered sequence of `(label, formula)` pairs along the path.
/// * `unsat_cores` - One unsat core per cut point (length = path_steps.len() - 1).
///
/// # Errors
/// Returns `CegarError::SolverError` on label mismatches or if `unsat_cores`
/// length does not match `path_steps.len() - 1`.
pub(crate) fn sequence_interpolation(
    path_steps: &[(String, Formula)],
    unsat_cores: &[UnsatCore],
) -> Result<Vec<InterpolationResult>, CegarError> {
    let n = path_steps.len();
    if n < 2 {
        return Ok(Vec::new());
    }

    let expected_cores = n - 1;
    if unsat_cores.len() != expected_cores {
        return Err(CegarError::SolverError {
            detail: format!(
                "sequence_interpolation: expected {expected_cores} unsat cores, got {}",
                unsat_cores.len()
            ),
        });
    }

    let mut results = Vec::with_capacity(expected_cores);

    for cut in 0..expected_cores {
        // A = steps[0..=cut], B = steps[cut+1..]
        let a_clauses: Vec<(String, Formula)> = path_steps[..=cut].to_vec();
        let b_clauses: Vec<(String, Formula)> = path_steps[cut + 1..].to_vec();

        let query = InterpolationQuery::new(a_clauses, b_clauses);
        let result = compute_interpolant(&query, &unsat_cores[cut])?;
        results.push(result);
    }

    Ok(results)
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Convert a list of predicates into a conjunction formula.
fn predicates_to_formula(predicates: &[Predicate]) -> Formula {
    if predicates.is_empty() {
        return Formula::Bool(true);
    }
    if predicates.len() == 1 {
        return predicate_to_formula(&predicates[0]);
    }
    Formula::And(predicates.iter().map(predicate_to_formula).collect())
}

/// Convert a single predicate to a formula.
fn predicate_to_formula(pred: &Predicate) -> Formula {
    use trust_types::Sort;

    match pred {
        Predicate::Comparison { lhs, op, rhs } => {
            let l = name_to_formula(lhs);
            let r = name_to_formula(rhs);
            match op {
                crate::predicate::CmpOp::Lt => Formula::Lt(Box::new(l), Box::new(r)),
                crate::predicate::CmpOp::Le => Formula::Le(Box::new(l), Box::new(r)),
                crate::predicate::CmpOp::Gt => Formula::Gt(Box::new(l), Box::new(r)),
                crate::predicate::CmpOp::Ge => Formula::Ge(Box::new(l), Box::new(r)),
                crate::predicate::CmpOp::Eq => Formula::Eq(Box::new(l), Box::new(r)),
                crate::predicate::CmpOp::Ne => {
                    Formula::Not(Box::new(Formula::Eq(Box::new(l), Box::new(r))))
                }
            }
        }
        Predicate::Range { var, lo, hi } => {
            let v = Formula::Var(var.clone(), Sort::Int);
            Formula::And(vec![
                Formula::Le(Box::new(Formula::Int(*lo)), Box::new(v.clone())),
                Formula::Le(Box::new(v), Box::new(Formula::Int(*hi))),
            ])
        }
        Predicate::NonNull(var) => Formula::Not(Box::new(Formula::Eq(
            Box::new(Formula::Var(var.clone(), Sort::Int)),
            Box::new(Formula::Int(0)),
        ))),
        Predicate::Custom(s) => {
            // Custom predicates are opaque; represent as a named boolean.
            Formula::Var(s.clone(), Sort::Bool)
        }
    }
}

/// Convert a name string to a formula node (variable or literal).
fn name_to_formula(name: &str) -> Formula {
    use trust_types::Sort;

    if let Ok(n) = name.parse::<i128>() {
        Formula::Int(n)
    } else {
        Formula::Var(name.to_string(), Sort::Int)
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use trust_types::Sort;

    use super::*;
    use crate::predicate::CmpOp;

    fn var(name: &str) -> Formula {
        Formula::Var(name.into(), Sort::Int)
    }

    fn int(n: i128) -> Formula {
        Formula::Int(n)
    }

    // -- Interpolant --

    #[test]
    fn test_interpolant_new_extracts_variables() {
        let formula = Formula::Lt(Box::new(var("x")), Box::new(int(10)));
        let preds = vec![Predicate::comparison("x", CmpOp::Lt, "10")];
        let interp = Interpolant::new(formula, preds);

        assert_eq!(interp.variables, vec!["x".to_string()]);
        assert_eq!(interp.predicate_count(), 1);
        assert!(!interp.is_trivial());
    }

    #[test]
    fn test_interpolant_trivial_bool_true() {
        let interp = Interpolant::new(Formula::Bool(true), vec![]);
        assert!(interp.is_trivial());
        assert_eq!(interp.predicate_count(), 0);
    }

    #[test]
    fn test_interpolant_trivial_empty_predicates() {
        let formula = Formula::Lt(Box::new(var("x")), Box::new(int(5)));
        let interp = Interpolant::new(formula, vec![]);
        assert!(interp.is_trivial());
    }

    // -- InterpolationQuery --

    #[test]
    fn test_query_shared_variables() {
        let a = vec![
            ("a0".into(), Formula::Lt(Box::new(var("x")), Box::new(int(10)))),
            ("a1".into(), Formula::Gt(Box::new(var("y")), Box::new(int(0)))),
        ];
        let b = vec![
            ("b0".into(), Formula::Ge(Box::new(var("x")), Box::new(int(20)))),
            ("b1".into(), Formula::Le(Box::new(var("z")), Box::new(int(5)))),
        ];
        let query = InterpolationQuery::new(a, b);

        let shared = query.shared_variables();
        assert_eq!(shared, vec!["x".to_string()]);
        assert_eq!(query.clause_count(), 4);
    }

    #[test]
    fn test_query_no_shared_variables() {
        let a = vec![("a0".into(), Formula::Lt(Box::new(var("x")), Box::new(int(10))))];
        let b = vec![("b0".into(), Formula::Gt(Box::new(var("y")), Box::new(int(0))))];
        let query = InterpolationQuery::new(a, b);

        assert!(query.shared_variables().is_empty());
    }

    // -- compute_interpolant --

    #[test]
    fn test_compute_interpolant_found() {
        let a = vec![("a0".into(), Formula::Lt(Box::new(var("x")), Box::new(int(10))))];
        let b = vec![("b0".into(), Formula::Ge(Box::new(var("x")), Box::new(int(20))))];
        let query = InterpolationQuery::new(a, b);
        let core = UnsatCore::new(vec!["a0".into(), "b0".into()]);

        let result = compute_interpolant(&query, &core).expect("should succeed");
        assert!(result.is_found());
        let interp = result.interpolant().expect("should have interpolant");
        assert!(!interp.predicates.is_empty());
    }

    #[test]
    fn test_compute_interpolant_empty_core() {
        let a = vec![("a0".into(), Formula::Bool(true))];
        let b = vec![("b0".into(), Formula::Bool(false))];
        let query = InterpolationQuery::new(a, b);
        let core = UnsatCore::default();

        let result = compute_interpolant(&query, &core).expect("should succeed");
        assert!(matches!(result, InterpolationResult::NoInterpolant));
    }

    #[test]
    fn test_compute_interpolant_no_extractable_predicates() {
        // Core references only boolean literals -- no comparison predicates extractable
        let a = vec![("a0".into(), Formula::Bool(true))];
        let b = vec![("b0".into(), Formula::Bool(false))];
        let query = InterpolationQuery::new(a, b);
        let core = UnsatCore::new(vec!["a0".into()]);

        let result = compute_interpolant(&query, &core).expect("should succeed");
        assert!(matches!(result, InterpolationResult::NoInterpolant));
    }

    // -- refine_predicates --

    #[test]
    fn test_refine_predicates_discovers_new() {
        let existing = vec![Predicate::comparison("x", CmpOp::Lt, "10")];
        let interp = Interpolant::new(
            Formula::Gt(Box::new(var("y")), Box::new(int(0))),
            vec![Predicate::comparison("y", CmpOp::Gt, "0")],
        );
        let results = vec![InterpolationResult::Found(interp)];

        let new = refine_predicates(&existing, &results);
        assert_eq!(new, vec![Predicate::comparison("y", CmpOp::Gt, "0")]);
    }

    #[test]
    fn test_refine_predicates_filters_existing() {
        let p = Predicate::comparison("x", CmpOp::Lt, "10");
        let existing = vec![p.clone()];
        let interp = Interpolant::new(
            Formula::Lt(Box::new(var("x")), Box::new(int(10))),
            vec![p],
        );
        let results = vec![InterpolationResult::Found(interp)];

        let new = refine_predicates(&existing, &results);
        assert!(new.is_empty(), "should not re-discover existing predicates");
    }

    #[test]
    fn test_refine_predicates_handles_no_interpolant() {
        let existing = vec![Predicate::comparison("x", CmpOp::Lt, "10")];
        let results = vec![InterpolationResult::NoInterpolant, InterpolationResult::Timeout];

        let new = refine_predicates(&existing, &results);
        assert!(new.is_empty());
    }

    // -- sequence_interpolation --

    #[test]
    fn test_sequence_interpolation_two_steps() {
        let steps = vec![
            ("s0".into(), Formula::Lt(Box::new(var("x")), Box::new(int(10)))),
            ("s1".into(), Formula::Ge(Box::new(var("x")), Box::new(int(20)))),
        ];
        let cores = vec![UnsatCore::new(vec!["s0".into(), "s1".into()])];

        let results = sequence_interpolation(&steps, &cores).expect("should succeed");
        assert_eq!(results.len(), 1);
        assert!(results[0].is_found());
    }

    #[test]
    fn test_sequence_interpolation_three_steps() {
        let steps = vec![
            ("s0".into(), Formula::Lt(Box::new(var("x")), Box::new(int(5)))),
            ("s1".into(), Formula::Ge(Box::new(var("x")), Box::new(int(3)))),
            ("s2".into(), Formula::Lt(Box::new(var("x")), Box::new(int(0)))),
        ];
        // Two cut points
        let cores = vec![
            UnsatCore::new(vec!["s0".into(), "s1".into()]),
            UnsatCore::new(vec!["s0".into(), "s1".into(), "s2".into()]),
        ];

        let results = sequence_interpolation(&steps, &cores).expect("should succeed");
        assert_eq!(results.len(), 2);
    }

    #[test]
    fn test_sequence_interpolation_wrong_core_count() {
        let steps = vec![
            ("s0".into(), Formula::Bool(true)),
            ("s1".into(), Formula::Bool(true)),
            ("s2".into(), Formula::Bool(false)),
        ];
        // Need 2 cores but provide 1
        let cores = vec![UnsatCore::default()];

        let result = sequence_interpolation(&steps, &cores);
        assert!(matches!(result, Err(CegarError::SolverError { .. })));
    }

    #[test]
    fn test_sequence_interpolation_single_step() {
        let steps = vec![("s0".into(), Formula::Bool(true))];
        let cores: Vec<UnsatCore> = vec![];

        let results = sequence_interpolation(&steps, &cores).expect("single step ok");
        assert!(results.is_empty());
    }

    // -- InterpolationCache --

    #[test]
    fn test_cache_hit_and_miss() {
        let mut cache = InterpolationCache::new();
        assert!(cache.is_empty());

        let a = vec![("a0".into(), Formula::Bool(true))];
        let b = vec![("b0".into(), Formula::Bool(false))];
        let query = InterpolationQuery::new(a, b);

        // Miss
        assert!(cache.get(&query).is_none());
        assert_eq!(cache.miss_count(), 1);

        // Insert
        cache.insert(&query, InterpolationResult::NoInterpolant);
        assert_eq!(cache.len(), 1);

        // Hit
        let a2 = vec![("a0".into(), Formula::Bool(true))];
        let b2 = vec![("b0".into(), Formula::Bool(false))];
        let query2 = InterpolationQuery::new(a2, b2);
        let cached = cache.get(&query2);
        assert!(cached.is_some());
        assert_eq!(cache.hit_count(), 1);
        assert!(cache.hit_rate() > 0.0);
    }

    #[test]
    fn test_cache_clear() {
        let mut cache = InterpolationCache::new();
        let query =
            InterpolationQuery::new(vec![("a".into(), Formula::Bool(true))], vec![]);
        cache.insert(&query, InterpolationResult::Timeout);
        assert_eq!(cache.len(), 1);

        cache.clear();
        assert!(cache.is_empty());
        assert_eq!(cache.hit_count(), 0);
        assert_eq!(cache.miss_count(), 0);
    }

    // -- InterpolationResult --

    #[test]
    fn test_interpolation_result_accessors() {
        let no = InterpolationResult::NoInterpolant;
        assert!(!no.is_found());
        assert!(no.interpolant().is_none());

        let timeout = InterpolationResult::Timeout;
        assert!(!timeout.is_found());

        let interp = Interpolant::new(Formula::Bool(true), vec![]);
        let found = InterpolationResult::Found(interp);
        assert!(found.is_found());
        assert!(found.interpolant().is_some());
    }

    // -- predicate_to_formula round-trip helpers --

    #[test]
    fn test_predicates_to_formula_empty() {
        let f = predicates_to_formula(&[]);
        assert_eq!(f, Formula::Bool(true));
    }

    #[test]
    fn test_predicates_to_formula_single() {
        let preds = vec![Predicate::comparison("x", CmpOp::Lt, "10")];
        let f = predicates_to_formula(&preds);
        let expected = Formula::Lt(Box::new(var("x")), Box::new(int(10)));
        assert_eq!(f, expected);
    }

    #[test]
    fn test_predicates_to_formula_conjunction() {
        let preds = vec![
            Predicate::comparison("x", CmpOp::Lt, "10"),
            Predicate::comparison("y", CmpOp::Gt, "0"),
        ];
        let f = predicates_to_formula(&preds);
        match f {
            Formula::And(children) => assert_eq!(children.len(), 2),
            other => panic!("expected And, got {other:?}"),
        }
    }
}
