// trust-cache/reuse.rs: Counterexample reuse across functions
//
// Given a counterexample from function A, attempts to replay it on function B
// by mapping variables between the two functions. This enables cross-function
// counterexample sharing when formulas have compatible structure.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;

use trust_types::{Counterexample, Formula, Sort, VerificationCondition};

use crate::semantic_cache::normalize_formula;
use trust_types::fx::FxHashSet;

/// Reuses counterexamples across functions with structurally similar formulas.
///
/// When function A has a counterexample and function B has a similar formula
/// (after alpha-renaming), we can adapt A's counterexample to B's variable
/// names and try to reuse it.
pub struct CounterexampleReuser {
    /// Minimum similarity score required for reuse attempt.
    threshold: f64,
    /// Number of successful reuses.
    successes: usize,
    /// Number of failed reuse attempts.
    failures: usize,
}

impl CounterexampleReuser {
    /// Create a new reuser with the given similarity threshold.
    ///
    /// `threshold` is in `[0.0, 1.0]`. Higher values require closer structural
    /// match before attempting reuse. Recommended: 0.8 for safety.
    pub fn new(threshold: f64) -> Self {
        CounterexampleReuser {
            threshold: threshold.clamp(0.0, 1.0),
            successes: 0,
            failures: 0,
        }
    }

    /// Attempt to adapt a counterexample from `source` VC to `target` VC.
    ///
    /// Returns `Some(adapted_cex)` if the variable mapping succeeds.
    /// Returns `None` if the formulas are too dissimilar or the mapping fails.
    pub fn try_reuse(
        &mut self,
        source_vc: &VerificationCondition,
        source_cex: &Counterexample,
        target_vc: &VerificationCondition,
    ) -> Option<Counterexample> {
        let result = adapt_counterexample(
            &source_vc.formula,
            source_cex,
            &target_vc.formula,
            self.threshold,
        );
        match &result {
            Some(_) => self.successes += 1,
            None => self.failures += 1,
        }
        result
    }

    /// Number of successful reuse operations.
    #[must_use]
    pub fn successes(&self) -> usize {
        self.successes
    }

    /// Number of failed reuse attempts.
    #[must_use]
    pub fn failures(&self) -> usize {
        self.failures
    }

    /// Current similarity threshold.
    #[must_use]
    pub fn threshold(&self) -> f64 {
        self.threshold
    }
}

impl Default for CounterexampleReuser {
    fn default() -> Self {
        Self::new(0.8)
    }
}

/// Adapt a counterexample from a source formula to a target formula.
///
/// 1. Normalize both formulas (alpha-rename variables).
/// 2. Check structural similarity meets `threshold`.
/// 3. Build a variable mapping: source original names -> target original names
///    via the canonical (positional) names.
/// 4. Remap the counterexample assignments.
///
/// Returns `None` if similarity is below threshold or if any source variable
/// in the counterexample cannot be mapped to the target.
#[must_use]
pub(crate) fn adapt_counterexample(
    source_formula: &Formula,
    source_cex: &Counterexample,
    target_formula: &Formula,
    threshold: f64,
) -> Option<Counterexample> {
    let source_norm = normalize_formula(source_formula);
    let target_norm = normalize_formula(target_formula);

    // Check similarity
    let score = crate::semantic_cache::similarity_score(&source_norm, &target_norm);
    if score < threshold {
        return None;
    }

    // Build mapping: canonical_name -> source_original_name
    let canonical_to_source: FxHashMap<&str, &str> = source_norm
        .var_map
        .iter()
        .map(|(orig, canon)| (canon.as_str(), orig.as_str()))
        .collect();

    // Build mapping: canonical_name -> target_original_name
    let canonical_to_target: FxHashMap<&str, &str> = target_norm
        .var_map
        .iter()
        .map(|(orig, canon)| (canon.as_str(), orig.as_str()))
        .collect();

    // Build source_original -> target_original via canonical names
    let mut source_to_target: FxHashMap<&str, &str> = FxHashMap::default();
    for (canon, source_orig) in &canonical_to_source {
        if let Some(target_orig) = canonical_to_target.get(canon) {
            source_to_target.insert(source_orig, target_orig);
        }
    }

    // Remap counterexample assignments
    let mut adapted_assignments = Vec::new();
    for (var_name, value) in &source_cex.assignments {
        match source_to_target.get(var_name.as_str()) {
            Some(target_name) => {
                adapted_assignments.push((target_name.to_string(), value.clone()));
            }
            None => {
                // Source variable not in target formula -- reuse cannot proceed
                return None;
            }
        }
    }

    Some(Counterexample::new(adapted_assignments))
}

/// Extract all free variable names from a formula.
#[must_use]
pub(crate) fn free_variables(formula: &Formula) -> Vec<(String, Sort)> {
    let mut vars = Vec::new();
    let mut seen = FxHashSet::default();
    collect_vars(formula, &mut vars, &mut seen);
    vars
}

fn collect_vars(
    formula: &Formula,
    vars: &mut Vec<(String, Sort)>,
    seen: &mut FxHashSet<String>,
) {
    match formula {
        Formula::Var(name, sort) => {
            if seen.insert(name.clone()) {
                vars.push((name.clone(), sort.clone()));
            }
        }
        Formula::Not(inner)
        | Formula::Neg(inner)
        | Formula::BvNot(inner, _)
        | Formula::BvToInt(inner, _, _)
        | Formula::IntToBv(inner, _)
        | Formula::BvZeroExt(inner, _)
        | Formula::BvSignExt(inner, _) => collect_vars(inner, vars, seen),

        Formula::BvExtract { inner, .. } => collect_vars(inner, vars, seen),

        Formula::And(children) | Formula::Or(children) => {
            for child in children {
                collect_vars(child, vars, seen);
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
        | Formula::Select(a, b)
        | Formula::BvConcat(a, b) => {
            collect_vars(a, vars, seen);
            collect_vars(b, vars, seen);
        }

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
        | Formula::BvSLe(a, b, _) => {
            collect_vars(a, vars, seen);
            collect_vars(b, vars, seen);
        }

        Formula::Ite(c, t, e) | Formula::Store(c, t, e) => {
            collect_vars(c, vars, seen);
            collect_vars(t, vars, seen);
            collect_vars(e, vars, seen);
        }

        Formula::Forall(bound, body) | Formula::Exists(bound, body) => {
            // Bound variables are not free, but we still recurse into the body
            // to find free occurrences of other variables.
            for (name, _) in bound {
                seen.insert(name.clone());
            }
            collect_vars(body, vars, seen);
        }

        Formula::Bool(_) | Formula::Int(_) | Formula::UInt(_) | Formula::BitVec { .. } => {}
        _ => {},
    }
}

#[cfg(test)]
mod tests {
    use trust_types::{CounterexampleValue, SourceSpan, VcKind};

    use super::*;

    fn var(name: &str) -> Formula {
        Formula::Var(name.to_string(), Sort::Int)
    }

    fn make_vc(function: &str, formula: Formula) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: function.to_string(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
        }
    }

    fn make_cex(assignments: Vec<(&str, i128)>) -> Counterexample {
        Counterexample::new(
            assignments
                .into_iter()
                .map(|(n, v)| (n.to_string(), CounterexampleValue::Int(v)))
                .collect(),
        )
    }

    /// Assert that a counterexample value displays as the expected string.
    fn assert_cex_value(val: &CounterexampleValue, expected: &str) {
        assert_eq!(val.to_string(), expected, "counterexample value mismatch");
    }

    // -----------------------------------------------------------------------
    // adapt_counterexample tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_adapt_identical_formulas() {
        let formula = Formula::Gt(Box::new(var("x")), Box::new(Formula::Int(0)));
        let cex = make_cex(vec![("x", -5)]);
        let result = adapt_counterexample(&formula, &cex, &formula, 0.8);
        assert!(result.is_some());
        let adapted = result.unwrap();
        assert_eq!(adapted.assignments.len(), 1);
        assert_eq!(adapted.assignments[0].0, "x");
        assert_cex_value(&adapted.assignments[0].1, "-5");
    }

    #[test]
    fn test_adapt_alpha_equivalent_formulas() {
        // Source: a > 0 with cex a = -1
        let source = Formula::Gt(Box::new(var("a")), Box::new(Formula::Int(0)));
        let cex = make_cex(vec![("a", -1)]);
        // Target: b > 0
        let target = Formula::Gt(Box::new(var("b")), Box::new(Formula::Int(0)));

        let result = adapt_counterexample(&source, &cex, &target, 0.8);
        assert!(result.is_some(), "alpha-equivalent formulas should allow reuse");
        let adapted = result.unwrap();
        assert_eq!(adapted.assignments.len(), 1);
        assert_eq!(adapted.assignments[0].0, "b", "variable should be remapped to target name");
        assert_cex_value(&adapted.assignments[0].1, "-1");
    }

    #[test]
    fn test_adapt_multi_variable() {
        // Source: a > 0 AND b < 10, cex: a=-1, b=20
        let source = Formula::And(vec![
            Formula::Gt(Box::new(var("a")), Box::new(Formula::Int(0))),
            Formula::Lt(Box::new(var("b")), Box::new(Formula::Int(10))),
        ]);
        let cex = make_cex(vec![("a", -1), ("b", 20)]);
        // Target: x > 0 AND y < 10
        let target = Formula::And(vec![
            Formula::Gt(Box::new(var("x")), Box::new(Formula::Int(0))),
            Formula::Lt(Box::new(var("y")), Box::new(Formula::Int(10))),
        ]);

        let result = adapt_counterexample(&source, &cex, &target, 0.8);
        assert!(result.is_some());
        let adapted = result.unwrap();
        assert_eq!(adapted.assignments.len(), 2);
        // a -> x, b -> y
        assert_eq!(adapted.assignments[0].0, "x");
        assert_cex_value(&adapted.assignments[0].1, "-1");
        assert_eq!(adapted.assignments[1].0, "y");
        assert_cex_value(&adapted.assignments[1].1, "20");
    }

    #[test]
    fn test_adapt_below_threshold_returns_none() {
        let source = Formula::Bool(true);
        let cex = make_cex(vec![]);
        let target = Formula::And(vec![
            Formula::Gt(Box::new(var("x")), Box::new(Formula::Int(0))),
            Formula::Lt(Box::new(var("y")), Box::new(Formula::Int(10))),
        ]);

        let result = adapt_counterexample(&source, &cex, &target, 0.9);
        assert!(result.is_none(), "dissimilar formulas should fail reuse");
    }

    #[test]
    fn test_adapt_unmapped_variable_returns_none() {
        // Source has variable "extra" not in target
        let source = Formula::And(vec![
            Formula::Gt(Box::new(var("a")), Box::new(Formula::Int(0))),
            Formula::Lt(Box::new(var("extra")), Box::new(Formula::Int(10))),
        ]);
        // Counterexample references "extra"
        let cex = make_cex(vec![("a", -1), ("extra", 5)]);
        // Target has different structure
        let target = Formula::Gt(Box::new(var("b")), Box::new(Formula::Int(0)));

        let result = adapt_counterexample(&source, &cex, &target, 0.0);
        assert!(result.is_none(), "unmapped cex variable should prevent reuse");
    }

    // -----------------------------------------------------------------------
    // CounterexampleReuser tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_reuser_successful_reuse() {
        let mut reuser = CounterexampleReuser::new(0.8);
        let source_vc = make_vc("foo", Formula::Gt(Box::new(var("a")), Box::new(Formula::Int(0))));
        let cex = make_cex(vec![("a", -1)]);
        let target_vc = make_vc("bar", Formula::Gt(Box::new(var("b")), Box::new(Formula::Int(0))));

        let result = reuser.try_reuse(&source_vc, &cex, &target_vc);
        assert!(result.is_some());
        assert_eq!(reuser.successes(), 1);
        assert_eq!(reuser.failures(), 0);
    }

    #[test]
    fn test_reuser_failed_reuse() {
        let mut reuser = CounterexampleReuser::new(0.9);
        let source_vc = make_vc("foo", Formula::Bool(true));
        let cex = make_cex(vec![]);
        let target_vc = make_vc(
            "bar",
            Formula::And(vec![
                Formula::Gt(Box::new(var("x")), Box::new(Formula::Int(0))),
                Formula::Lt(Box::new(var("y")), Box::new(Formula::Int(10))),
            ]),
        );

        let result = reuser.try_reuse(&source_vc, &cex, &target_vc);
        assert!(result.is_none());
        assert_eq!(reuser.successes(), 0);
        assert_eq!(reuser.failures(), 1);
    }

    #[test]
    fn test_reuser_default_threshold() {
        let reuser = CounterexampleReuser::default();
        assert!((reuser.threshold() - 0.8).abs() < f64::EPSILON);
    }

    #[test]
    fn test_reuser_threshold_clamped() {
        let reuser = CounterexampleReuser::new(1.5);
        assert!((reuser.threshold() - 1.0).abs() < f64::EPSILON);
        let reuser = CounterexampleReuser::new(-0.5);
        assert!(reuser.threshold().abs() < f64::EPSILON);
    }

    // -----------------------------------------------------------------------
    // free_variables tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_free_variables_simple() {
        let f = Formula::And(vec![
            Formula::Gt(Box::new(var("x")), Box::new(Formula::Int(0))),
            Formula::Lt(Box::new(var("y")), Box::new(Formula::Int(10))),
        ]);
        let vars = free_variables(&f);
        assert_eq!(vars.len(), 2);
        assert_eq!(vars[0].0, "x");
        assert_eq!(vars[1].0, "y");
    }

    #[test]
    fn test_free_variables_no_duplicates() {
        // x appears twice
        let f = Formula::And(vec![
            Formula::Gt(Box::new(var("x")), Box::new(Formula::Int(0))),
            Formula::Lt(Box::new(var("x")), Box::new(Formula::Int(10))),
        ]);
        let vars = free_variables(&f);
        assert_eq!(vars.len(), 1);
        assert_eq!(vars[0].0, "x");
    }

    #[test]
    fn test_free_variables_literal_only() {
        let f = Formula::Bool(true);
        let vars = free_variables(&f);
        assert!(vars.is_empty());
    }

    #[test]
    fn test_free_variables_excludes_bound() {
        // forall i. i > 0  -- "i" is bound, not free
        let f = Formula::Forall(
            vec![("i".to_string(), Sort::Int)],
            Box::new(Formula::Gt(Box::new(var("i")), Box::new(Formula::Int(0)))),
        );
        let vars = free_variables(&f);
        assert!(vars.is_empty(), "bound variables should not appear as free");
    }

    #[test]
    fn test_free_variables_mixed_bound_and_free() {
        // forall i. x > i  -- "i" is bound, "x" is free
        let f = Formula::Forall(
            vec![("i".to_string(), Sort::Int)],
            Box::new(Formula::Gt(Box::new(var("x")), Box::new(var("i")))),
        );
        let vars = free_variables(&f);
        assert_eq!(vars.len(), 1);
        assert_eq!(vars[0].0, "x");
    }
}
