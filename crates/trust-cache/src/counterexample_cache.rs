// trust-cache/counterexample_cache.rs: Counterexample reuse cache
//
// Stores (Formula, Counterexample) pairs. If a new formula subsumes a cached
// formula that has a counterexample, the counterexample is reused without
// calling the solver. Inspired by KLEE's CexCachingSolver.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{Counterexample, Formula};

/// Cache of counterexamples for formula subsumption checking.
///
/// Key insight: if formula F1 has counterexample C, and F2 is *weaker* than F1
/// (F1 implies F2), then C is also a counterexample for F2. We check this
/// structurally rather than calling the solver.
pub struct CounterexampleCache {
    entries: Vec<CexEntry>,
    hits: usize,
    misses: usize,
}

struct CexEntry {
    formula: Formula,
    counterexample: Counterexample,
}

impl CounterexampleCache {
    /// Create an empty counterexample cache.
    pub fn new() -> Self {
        CounterexampleCache { entries: Vec::new(), hits: 0, misses: 0 }
    }

    /// Store a counterexample for a formula.
    pub fn insert(&mut self, formula: Formula, counterexample: Counterexample) {
        self.entries.push(CexEntry { formula, counterexample });
    }

    /// Check if any cached counterexample can be reused for the given formula.
    ///
    /// Returns a counterexample if the new formula is subsumed by a cached
    /// formula that has a counterexample. Subsumption check is structural
    /// (syntactic), not semantic — it may miss some valid reuse opportunities
    /// but is always sound.
    pub fn check_subsumption(&mut self, formula: &Formula) -> Option<&Counterexample> {
        for entry in &self.entries {
            if structurally_subsumes(&entry.formula, formula) {
                self.hits += 1;
                return Some(&entry.counterexample);
            }
        }
        self.misses += 1;
        None
    }

    /// Number of cache entries.
    #[must_use]
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether the cache is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Number of subsumption hits.
    #[must_use]
    pub fn hits(&self) -> usize {
        self.hits
    }

    /// Number of subsumption misses.
    #[must_use]
    pub fn misses(&self) -> usize {
        self.misses
    }

    /// Clear all entries.
    pub fn clear(&mut self) {
        self.entries.clear();
        self.hits = 0;
        self.misses = 0;
    }
}

impl Default for CounterexampleCache {
    fn default() -> Self {
        Self::new()
    }
}

/// Check if `stronger` structurally subsumes `weaker`.
///
/// F1 subsumes F2 means: every model of F1 is a model of F2 (F1 => F2).
/// We check this conservatively using structural rules:
///
/// 1. If F1 == F2 (syntactic equality), F1 => F2.
/// 2. If F2 is a disjunction containing F1 as a disjunct, F1 => F2.
/// 3. If F1 is a conjunction containing F2 as a conjunct, F1 => F2.
/// 4. If F1's free variables are a subset of F2's and F1 adds additional
///    constraints (more conjuncts), F1 => F2.
///
/// This is incomplete (may return false when F1 actually implies F2) but sound.
#[must_use]
pub(crate) fn structurally_subsumes(stronger: &Formula, weaker: &Formula) -> bool {
    // Rule 1: syntactic equality
    if stronger == weaker {
        return true;
    }

    // Rule 2: weaker is Or(...) containing stronger as a disjunct
    if let Formula::Or(disjuncts) = weaker
        && disjuncts.iter().any(|d| d == stronger) {
            return true;
        }

    // Rule 3: stronger is And(...) containing weaker as a conjunct
    if let Formula::And(conjuncts) = stronger
        && conjuncts.iter().any(|c| c == weaker) {
            return true;
        }

    // Rule 4: stronger is And(...) and weaker is And(...),
    // and weaker's conjuncts are a subset of stronger's conjuncts
    if let (Formula::And(s_conj), Formula::And(w_conj)) = (stronger, weaker)
        && w_conj.iter().all(|wc| s_conj.contains(wc)) {
            return true;
        }

    false
}

#[cfg(test)]
mod tests {
    use trust_types::{CounterexampleValue, Sort};

    use super::*;

    fn var(name: &str) -> Formula {
        Formula::Var(name.to_string(), Sort::Int)
    }

    fn cex(assignments: Vec<(&str, CounterexampleValue)>) -> Counterexample {
        Counterexample::new(
            assignments.into_iter().map(|(n, v)| (n.to_string(), v)).collect(),
        )
    }

    #[test]
    fn test_counterexample_cache_insert_and_check() {
        let mut cache = CounterexampleCache::new();
        let f = Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0)));
        let c = cex(vec![("x", CounterexampleValue::Int(0))]);
        cache.insert(f.clone(), c);

        // Same formula should match
        let result = cache.check_subsumption(&f);
        assert!(result.is_some());
        assert_eq!(cache.hits(), 1);
    }

    #[test]
    fn test_counterexample_cache_miss() {
        let mut cache = CounterexampleCache::new();
        let f1 = Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0)));
        let f2 = Formula::Eq(Box::new(var("y")), Box::new(Formula::Int(1)));
        let c = cex(vec![("x", CounterexampleValue::Int(0))]);
        cache.insert(f1, c);

        let result = cache.check_subsumption(&f2);
        assert!(result.is_none());
        assert_eq!(cache.misses(), 1);
    }

    #[test]
    fn test_subsumption_stronger_and_contains_weaker() {
        // stronger = A AND B, weaker = A => stronger implies weaker
        let a = Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0)));
        let b = Formula::Gt(Box::new(var("y")), Box::new(Formula::Int(1)));
        let stronger = Formula::And(vec![a.clone(), b]);

        assert!(structurally_subsumes(&stronger, &a));
    }

    #[test]
    fn test_subsumption_weaker_or_contains_stronger() {
        // stronger = A, weaker = A OR B => stronger implies weaker
        let a = Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0)));
        let b = Formula::Gt(Box::new(var("y")), Box::new(Formula::Int(1)));
        let weaker = Formula::Or(vec![a.clone(), b]);

        assert!(structurally_subsumes(&a, &weaker));
    }

    #[test]
    fn test_subsumption_and_subset() {
        // stronger = A AND B AND C, weaker = A AND B
        let a = Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0)));
        let b = Formula::Gt(Box::new(var("y")), Box::new(Formula::Int(1)));
        let c = Formula::Lt(Box::new(var("z")), Box::new(Formula::Int(5)));
        let stronger = Formula::And(vec![a.clone(), b.clone(), c]);
        let weaker = Formula::And(vec![a, b]);

        assert!(structurally_subsumes(&stronger, &weaker));
    }

    #[test]
    fn test_subsumption_equal() {
        let f = Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(42)));
        assert!(structurally_subsumes(&f, &f));
    }

    #[test]
    fn test_subsumption_no_match() {
        let a = Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0)));
        let b = Formula::Eq(Box::new(var("y")), Box::new(Formula::Int(1)));
        assert!(!structurally_subsumes(&a, &b));
    }

    #[test]
    fn test_cache_clear() {
        let mut cache = CounterexampleCache::new();
        let f = Formula::Bool(true);
        cache.insert(f.clone(), cex(vec![]));
        cache.check_subsumption(&f);
        assert_eq!(cache.len(), 1);

        cache.clear();
        assert!(cache.is_empty());
        assert_eq!(cache.hits(), 0);
    }
}
