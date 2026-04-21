// trust-cache/query_cache.rs: Solver query result cache
//
// Caches solver results keyed by canonical VC hash (SHA-256 of formula).
// Inspired by KLEE's CachingSolver (refs/klee/lib/Solver/CachingSolver.cpp).
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;
use std::path::Path;

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use trust_types::{Formula, VerificationCondition, VerificationResult};

use crate::CacheError;
use trust_types::fx::FxHashSet;

/// Statistics about cache usage.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct CacheStats {
    pub hits: usize,
    pub misses: usize,
    pub size: usize,
}

impl CacheStats {
    /// Hit rate as a fraction in [0.0, 1.0]. Returns 0.0 if no lookups.
    #[must_use]
    pub fn hit_rate(&self) -> f64 {
        let total = self.hits + self.misses;
        if total == 0 { 0.0 } else { self.hits as f64 / total as f64 }
    }

    /// Miss rate as a fraction in [0.0, 1.0]. Returns 0.0 if no lookups.
    #[must_use]
    pub fn miss_rate(&self) -> f64 {
        let total = self.hits + self.misses;
        if total == 0 { 0.0 } else { self.misses as f64 / total as f64 }
    }
}

/// Persistent on-disk format for the query cache.
#[derive(Debug, Clone, Serialize, Deserialize)]
struct QueryCacheFile {
    version: u32,
    entries: FxHashMap<String, SerializableResult>,
}

/// Serializable wrapper for VerificationResult (which already derives Serialize/Deserialize).
#[derive(Debug, Clone, Serialize, Deserialize)]
struct SerializableResult {
    result: VerificationResult,
}

const QUERY_CACHE_VERSION: u32 = 1;

/// Cache of solver query results keyed by canonical formula hash.
///
/// Wraps a base solver: before sending a VC to the solver, check the cache.
/// If the formula hash matches, return the cached result immediately.
pub struct QueryCache {
    entries: FxHashMap<String, VerificationResult>,
    hits: usize,
    misses: usize,
}

impl QueryCache {
    /// Create an empty query cache.
    pub fn new() -> Self {
        QueryCache { entries: FxHashMap::default(), hits: 0, misses: 0 }
    }

    /// Compute the canonical SHA-256 hash of a formula.
    ///
    /// Alpha-normalizes bound variables before hashing so that structurally
    /// equivalent formulas with different bound variable names (e.g.,
    /// `Exists(a, a > 0)` vs `Exists(b, b > 0)`) produce the same hash.
    ///
    /// Uses serde_json serialization of the normalized form as a stable
    /// canonical representation.
    #[must_use]
    pub(crate) fn formula_hash(formula: &Formula) -> String {
        crate::alpha_normalize::alpha_normalized_hash(formula)
    }

    /// Compute the canonical hash for a VerificationCondition.
    ///
    /// Alpha-normalizes the formula before hashing. Includes the function
    /// name for disambiguation.
    #[must_use]
    pub(crate) fn vc_hash(vc: &VerificationCondition) -> String {
        let normalized = crate::alpha_normalize::alpha_normalize(&vc.formula);
        let formula_json = serde_json::to_string(&normalized).unwrap_or_default();
        let mut hasher = Sha256::new();
        hasher.update(vc.function.as_bytes());
        hasher.update(b":");
        hasher.update(formula_json.as_bytes());
        format!("{:x}", hasher.finalize())
    }

    /// Look up a cached result for a VC.
    pub fn lookup(&mut self, vc: &VerificationCondition) -> Option<&VerificationResult> {
        let hash = Self::vc_hash(vc);
        if self.entries.contains_key(&hash) {
            self.hits += 1;
            self.entries.get(&hash)
        } else {
            self.misses += 1;
            None
        }
    }

    /// Look up by pre-computed hash.
    pub fn lookup_by_hash(&mut self, hash: &str) -> Option<&VerificationResult> {
        if self.entries.contains_key(hash) {
            self.hits += 1;
            self.entries.get(hash)
        } else {
            self.misses += 1;
            None
        }
    }

    /// Insert a result for a VC.
    pub fn insert(&mut self, vc: &VerificationCondition, result: VerificationResult) {
        let hash = Self::vc_hash(vc);
        self.entries.insert(hash, result);
    }

    /// Insert by pre-computed hash.
    pub fn insert_by_hash(&mut self, hash: String, result: VerificationResult) {
        self.entries.insert(hash, result);
    }

    /// Get cache statistics.
    #[must_use]
    pub fn stats(&self) -> CacheStats {
        CacheStats { hits: self.hits, misses: self.misses, size: self.entries.len() }
    }

    /// Number of cached entries.
    #[must_use]
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether the cache is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Clear all entries and reset statistics.
    pub fn clear(&mut self) {
        self.entries.clear();
        self.hits = 0;
        self.misses = 0;
    }

    /// Persist cache to disk as JSON.
    pub fn save(&self, path: &Path) -> Result<(), CacheError> {
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent)?;
        }
        let file = QueryCacheFile {
            version: QUERY_CACHE_VERSION,
            entries: self
                .entries
                .iter()
                .map(|(k, v)| (k.clone(), SerializableResult { result: v.clone() }))
                .collect(),
        };
        let json = serde_json::to_string_pretty(&file)?;
        std::fs::write(path, json)?;
        Ok(())
    }

    /// Load cache from disk. Returns empty cache if file doesn't exist or is corrupt.
    pub fn load(path: &Path) -> Result<Self, CacheError> {
        if !path.exists() {
            return Ok(Self::new());
        }
        let contents = std::fs::read_to_string(path)?;
        match serde_json::from_str::<QueryCacheFile>(&contents) {
            Ok(file) if file.version == QUERY_CACHE_VERSION => {
                let entries =
                    file.entries.into_iter().map(|(k, v)| (k, v.result)).collect();
                Ok(QueryCache { entries, hits: 0, misses: 0 })
            }
            _ => Ok(Self::new()),
        }
    }
}

impl Default for QueryCache {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// CacheKey: formula hash + relevant variables for more precise cache lookups
// ---------------------------------------------------------------------------

/// Cache key based on formula hash and relevant variable set.
///
/// Unlike a raw formula hash, this key incorporates which variables are
/// "interesting" for the query. Two formulas that are identical after
/// projecting away irrelevant variables share the same CacheKey, enabling
/// cache hits even when the full constraint set differs.
///
/// Inspired by KLEE's approach of caching query results after constraint
/// independence splitting.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CacheKey {
    /// SHA-256 hash of the formula's canonical serialization.
    pub formula_hash: String,
    /// Sorted set of relevant variable names, concatenated and hashed.
    pub vars_hash: String,
}

impl CacheKey {
    /// Build a CacheKey from a formula and a set of relevant variables.
    ///
    /// The formula is hashed via SHA-256 of its JSON serialization. The
    /// relevant variable set is sorted and hashed separately so that
    /// key lookup is O(1) regardless of variable count.
    #[must_use]
    pub fn new(formula: &Formula, relevant_vars: &FxHashSet<String>) -> Self {
        let formula_hash = QueryCache::formula_hash(formula);

        let mut sorted_vars: Vec<&String> = relevant_vars.iter().collect();
        sorted_vars.sort();
        let vars_str = sorted_vars.iter().map(|s| s.as_str()).collect::<Vec<_>>().join(",");
        let mut hasher = Sha256::new();
        hasher.update(vars_str.as_bytes());
        let vars_hash = format!("{:x}", hasher.finalize());

        CacheKey { formula_hash, vars_hash }
    }

    /// Build a CacheKey from a formula alone (using all free variables).
    #[must_use]
    pub fn from_formula(formula: &Formula) -> Self {
        let free_vars = crate::independence::free_variables(formula);
        Self::new(formula, &free_vars)
    }

    /// The combined key string used for HashMap lookups.
    #[must_use]
    pub fn combined(&self) -> String {
        format!("{}:{}", self.formula_hash, self.vars_hash)
    }
}

// ---------------------------------------------------------------------------
// SubsumptionCache: if a stronger formula was proved, weaker formulas are free
// ---------------------------------------------------------------------------

/// Subsumption-based proof cache.
///
/// Stores proved formulas so that weaker formulas can be discharged without
/// calling the solver. If formula F1 was proved (UNSAT when checking for
/// violations), and F2 is weaker (F1 => F2), then F2 is also proved.
///
/// The subsumption check is structural (conservative) — it may miss some
/// valid subsumptions but is always sound.
///
/// Inspired by KLEE's `CexCachingSolver` which reuses counterexamples in
/// the opposite direction. Here we reuse proofs: stronger proofs subsume
/// weaker obligations.
pub struct SubsumptionCache {
    /// Proved formulas stored for subsumption checking.
    proved_formulas: Vec<(Formula, VerificationResult)>,
    /// Number of subsumption hits (avoided solver calls).
    hits: usize,
    /// Number of subsumption misses.
    misses: usize,
}

impl SubsumptionCache {
    /// Create an empty subsumption cache.
    pub fn new() -> Self {
        SubsumptionCache {
            proved_formulas: Vec::new(),
            hits: 0,
            misses: 0,
        }
    }

    /// Record a proved formula in the subsumption cache.
    ///
    /// Only `Proved` results are stored — failed/unknown results cannot
    /// subsume other formulas.
    pub fn insert_proved(&mut self, formula: Formula, result: VerificationResult) {
        if result.is_proved() {
            self.proved_formulas.push((formula, result));
        }
    }

    /// Check if a formula is subsumed by a previously proved formula.
    ///
    /// Returns the cached proof result if the formula is subsumed,
    /// `None` otherwise. Subsumption is checked structurally:
    ///
    /// 1. Syntactic equality (exact match).
    /// 2. The cached formula is a conjunction containing the query as a conjunct
    ///    (stronger => weaker).
    /// 3. The query is a disjunction containing the cached formula as a disjunct
    ///    (stronger => weaker).
    /// 4. Both are conjunctions and the query's conjuncts are a subset of the
    ///    cached formula's conjuncts.
    pub fn check(&mut self, formula: &Formula) -> Option<&VerificationResult> {
        for (proved_f, result) in &self.proved_formulas {
            if formula_is_subsumed_by(formula, proved_f) {
                self.hits += 1;
                return Some(result);
            }
        }
        self.misses += 1;
        None
    }

    /// Number of entries in the cache.
    #[must_use]
    pub fn len(&self) -> usize {
        self.proved_formulas.len()
    }

    /// Whether the cache is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.proved_formulas.is_empty()
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

    /// Clear all entries and reset statistics.
    pub fn clear(&mut self) {
        self.proved_formulas.clear();
        self.hits = 0;
        self.misses = 0;
    }
}

impl Default for SubsumptionCache {
    fn default() -> Self {
        Self::new()
    }
}

/// Check if `query` is subsumed by `proved` (i.e., proving `proved` implies `query` holds).
///
/// For verification conditions checked via UNSAT (negation):
/// - If we proved "NOT(violation_F1)" is UNSAT (F1 holds), and F2 is weaker than F1,
///   then F2 also holds.
/// - "F1 stronger than F2" means F1 => F2 (every model of F1 is a model of F2).
///
/// We check structural subsumption conservatively:
/// 1. Syntactic equality.
/// 2. `proved` is And(...) containing `query` as a conjunct (conjunction is stronger).
/// 3. `query` is Or(...) containing `proved` as a disjunct (disjunction is weaker).
/// 4. Both are And(...) and query's conjuncts are a subset of proved's.
#[must_use]
fn formula_is_subsumed_by(query: &Formula, proved: &Formula) -> bool {
    // Rule 1: syntactic equality
    if query == proved {
        return true;
    }

    // Rule 2: proved = And(...) containing query as a conjunct
    // Proving (A AND B) means both A and B hold; so query=A is subsumed.
    if let Formula::And(conjuncts) = proved
        && conjuncts.iter().any(|c| c == query) {
            return true;
        }

    // Rule 3: query = Or(...) containing proved as a disjunct
    // If proved=A holds and query=(A OR B), then query holds.
    if let Formula::Or(disjuncts) = query
        && disjuncts.iter().any(|d| d == proved) {
            return true;
        }

    // Rule 4: both are And; query's conjuncts are a subset of proved's
    // proved = (A AND B AND C), query = (A AND B) => proved implies query
    if let (Formula::And(p_conj), Formula::And(q_conj)) = (proved, query)
        && q_conj.iter().all(|qc| p_conj.contains(qc)) {
            return true;
        }

    false
}

/// Check if a formula is subsumed by any entry in a SubsumptionCache.
///
/// Convenience function for callers that want a simple yes/no check.
/// Returns the cached result if subsumed, `None` otherwise.
pub fn is_subsumed(
    formula: &Formula,
    cache: &mut SubsumptionCache,
) -> Option<VerificationResult> {
    cache.check(formula).cloned()
}

#[cfg(test)]
mod tests {
    use trust_types::{ProofStrength, Sort, SourceSpan, VcKind};

    use super::*;

    fn make_vc(name: &str, formula: Formula) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: name.to_string(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
        }
    }

    fn proved_result() -> VerificationResult {
        VerificationResult::Proved {
            solver: "z4".to_string(),
            time_ms: 10,
            strength: ProofStrength::smt_unsat(), proof_certificate: None,
                solver_warnings: None, }
    }

    fn failed_result() -> VerificationResult {
        VerificationResult::Failed { solver: "z4".to_string(), time_ms: 5, counterexample: None }
    }

    #[test]
    fn test_query_cache_insert_and_lookup_hit() {
        let mut cache = QueryCache::new();
        let vc = make_vc("foo", Formula::Bool(true));
        cache.insert(&vc, proved_result());

        let result = cache.lookup(&vc);
        assert!(result.is_some());
        assert!(result.unwrap().is_proved());
        assert_eq!(cache.stats().hits, 1);
        assert_eq!(cache.stats().misses, 0);
    }

    #[test]
    fn test_query_cache_lookup_miss() {
        let mut cache = QueryCache::new();
        let vc = make_vc("foo", Formula::Bool(true));
        let result = cache.lookup(&vc);
        assert!(result.is_none());
        assert_eq!(cache.stats().misses, 1);
    }

    #[test]
    fn test_query_cache_different_formulas_different_hashes() {
        let mut cache = QueryCache::new();
        let vc1 = make_vc("foo", Formula::Bool(true));
        let vc2 = make_vc("foo", Formula::Bool(false));
        cache.insert(&vc1, proved_result());

        assert!(cache.lookup(&vc1).is_some());
        assert!(cache.lookup(&vc2).is_none());
    }

    #[test]
    fn test_query_cache_different_functions_different_hashes() {
        let mut cache = QueryCache::new();
        let vc1 = make_vc("foo", Formula::Bool(true));
        let vc2 = make_vc("bar", Formula::Bool(true));
        cache.insert(&vc1, proved_result());

        assert!(cache.lookup(&vc1).is_some());
        assert!(cache.lookup(&vc2).is_none());
    }

    #[test]
    fn test_query_cache_stats() {
        let mut cache = QueryCache::new();
        let vc1 = make_vc("f", Formula::Bool(true));
        let vc2 = make_vc("g", Formula::Int(42));
        cache.insert(&vc1, proved_result());

        cache.lookup(&vc1); // hit
        cache.lookup(&vc2); // miss
        cache.lookup(&vc1); // hit

        let stats = cache.stats();
        assert_eq!(stats.hits, 2);
        assert_eq!(stats.misses, 1);
        assert_eq!(stats.size, 1);
        assert!((stats.hit_rate() - 2.0 / 3.0).abs() < 1e-9);
        assert!((stats.miss_rate() - 1.0 / 3.0).abs() < 1e-9);
    }

    #[test]
    fn test_query_cache_stats_empty() {
        let stats = CacheStats::default();
        assert_eq!(stats.hit_rate(), 0.0);
        assert_eq!(stats.miss_rate(), 0.0);
    }

    #[test]
    fn test_query_cache_clear() {
        let mut cache = QueryCache::new();
        let vc = make_vc("f", Formula::Bool(true));
        cache.insert(&vc, proved_result());
        cache.lookup(&vc);
        assert_eq!(cache.len(), 1);

        cache.clear();
        assert!(cache.is_empty());
        assert_eq!(cache.stats().hits, 0);
    }

    #[test]
    fn test_formula_hash_deterministic() {
        let f = Formula::And(vec![
            Formula::Var("x".into(), Sort::Int),
            Formula::Bool(true),
        ]);
        let h1 = QueryCache::formula_hash(&f);
        let h2 = QueryCache::formula_hash(&f);
        assert_eq!(h1, h2);
        assert_eq!(h1.len(), 64); // SHA-256 hex
    }

    #[test]
    fn test_query_cache_overwrite() {
        let mut cache = QueryCache::new();
        let vc = make_vc("f", Formula::Bool(true));
        cache.insert(&vc, proved_result());
        cache.insert(&vc, failed_result());

        let result = cache.lookup(&vc).unwrap();
        assert!(result.is_failed());
    }

    #[test]
    fn test_query_cache_persistence_roundtrip() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("query-cache.json");

        {
            let mut cache = QueryCache::new();
            let vc = make_vc("persist_fn", Formula::Int(99));
            cache.insert(&vc, proved_result());
            cache.save(&path).unwrap();
        }

        {
            let mut cache = QueryCache::load(&path).unwrap();
            let vc = make_vc("persist_fn", Formula::Int(99));
            assert!(cache.lookup(&vc).is_some());
        }
    }

    #[test]
    fn test_query_cache_load_nonexistent() {
        let cache = QueryCache::load(Path::new("/tmp/nonexistent-trust-qc.json")).unwrap();
        assert!(cache.is_empty());
    }

    #[test]
    fn test_query_cache_load_corrupt() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("corrupt.json");
        std::fs::write(&path, "not json{{{").unwrap();

        let cache = QueryCache::load(&path).unwrap();
        assert!(cache.is_empty());
    }

    #[test]
    fn test_lookup_by_hash() {
        let mut cache = QueryCache::new();
        let vc = make_vc("h", Formula::Bool(false));
        let hash = QueryCache::vc_hash(&vc);
        cache.insert_by_hash(hash.clone(), proved_result());

        assert!(cache.lookup_by_hash(&hash).is_some());
        assert!(cache.lookup_by_hash("bogus").is_none());
    }

    // -----------------------------------------------------------------------
    // CacheKey tests
    // -----------------------------------------------------------------------

    fn var(name: &str) -> Formula {
        Formula::Var(name.to_string(), Sort::Int)
    }

    #[test]
    fn test_cache_key_deterministic() {
        let f = Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0)));
        let vars: FxHashSet<String> = ["x".to_string()].into();
        let k1 = CacheKey::new(&f, &vars);
        let k2 = CacheKey::new(&f, &vars);
        assert_eq!(k1, k2);
        assert_eq!(k1.combined(), k2.combined());
    }

    #[test]
    fn test_cache_key_different_vars_different_key() {
        let f = Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0)));
        let vars1: FxHashSet<String> = ["x".to_string()].into();
        let vars2: FxHashSet<String> = ["x".to_string(), "y".to_string()].into();
        let k1 = CacheKey::new(&f, &vars1);
        let k2 = CacheKey::new(&f, &vars2);
        assert_ne!(k1.vars_hash, k2.vars_hash);
        // Same formula => same formula_hash
        assert_eq!(k1.formula_hash, k2.formula_hash);
    }

    #[test]
    fn test_cache_key_different_formula_different_key() {
        let f1 = Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0)));
        let f2 = Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(1)));
        let vars: FxHashSet<String> = ["x".to_string()].into();
        let k1 = CacheKey::new(&f1, &vars);
        let k2 = CacheKey::new(&f2, &vars);
        assert_ne!(k1.formula_hash, k2.formula_hash);
    }

    #[test]
    fn test_cache_key_from_formula() {
        let f = Formula::Add(Box::new(var("a")), Box::new(var("b")));
        let k = CacheKey::from_formula(&f);
        // Should include both a and b in vars
        assert!(!k.vars_hash.is_empty());
        assert!(!k.formula_hash.is_empty());
        assert_eq!(k.combined().len(), 64 + 1 + 64); // sha256:sha256
    }

    #[test]
    fn test_cache_key_empty_vars() {
        let f = Formula::Bool(true);
        let vars: FxHashSet<String> = FxHashSet::default();
        let k = CacheKey::new(&f, &vars);
        assert!(!k.vars_hash.is_empty()); // SHA-256 of empty string is still a valid hash
    }

    // -----------------------------------------------------------------------
    // SubsumptionCache tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_subsumption_cache_exact_match() {
        let mut cache = SubsumptionCache::new();
        let f = Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0)));
        cache.insert_proved(f.clone(), proved_result());

        let result = cache.check(&f);
        assert!(result.is_some());
        assert!(result.unwrap().is_proved());
        assert_eq!(cache.hits(), 1);
    }

    #[test]
    fn test_subsumption_cache_miss() {
        let mut cache = SubsumptionCache::new();
        let f1 = Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0)));
        let f2 = Formula::Eq(Box::new(var("y")), Box::new(Formula::Int(1)));
        cache.insert_proved(f1, proved_result());

        let result = cache.check(&f2);
        assert!(result.is_none());
        assert_eq!(cache.misses(), 1);
    }

    #[test]
    fn test_subsumption_cache_and_contains_conjunct() {
        // Proved: (x==0 AND y>1), query: x==0 => subsumed
        let mut cache = SubsumptionCache::new();
        let x_eq_0 = Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0)));
        let y_gt_1 = Formula::Gt(Box::new(var("y")), Box::new(Formula::Int(1)));
        let proved = Formula::And(vec![x_eq_0.clone(), y_gt_1]);
        cache.insert_proved(proved, proved_result());

        let result = cache.check(&x_eq_0);
        assert!(result.is_some(), "And containing query should subsume it");
        assert_eq!(cache.hits(), 1);
    }

    #[test]
    fn test_subsumption_cache_or_contains_proved() {
        // Proved: x==0, query: (x==0 OR y>1) => subsumed
        let mut cache = SubsumptionCache::new();
        let x_eq_0 = Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0)));
        let y_gt_1 = Formula::Gt(Box::new(var("y")), Box::new(Formula::Int(1)));
        cache.insert_proved(x_eq_0.clone(), proved_result());

        let query = Formula::Or(vec![x_eq_0, y_gt_1]);
        let result = cache.check(&query);
        assert!(result.is_some(), "Or containing proved should be subsumed");
    }

    #[test]
    fn test_subsumption_cache_and_subset() {
        // Proved: (A AND B AND C), query: (A AND B) => subsumed
        let mut cache = SubsumptionCache::new();
        let a = Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0)));
        let b = Formula::Gt(Box::new(var("y")), Box::new(Formula::Int(1)));
        let c = Formula::Lt(Box::new(var("z")), Box::new(Formula::Int(5)));
        let proved = Formula::And(vec![a.clone(), b.clone(), c]);
        cache.insert_proved(proved, proved_result());

        let query = Formula::And(vec![a, b]);
        let result = cache.check(&query);
        assert!(result.is_some(), "subset conjuncts should be subsumed");
    }

    #[test]
    fn test_subsumption_cache_ignores_failed_results() {
        let mut cache = SubsumptionCache::new();
        let f = Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0)));
        // Insert a failed result — should NOT be stored
        cache.insert_proved(f.clone(), failed_result());
        assert!(cache.is_empty(), "failed results should not be inserted");

        let result = cache.check(&f);
        assert!(result.is_none());
    }

    #[test]
    fn test_subsumption_cache_clear() {
        let mut cache = SubsumptionCache::new();
        let f = Formula::Bool(true);
        cache.insert_proved(f.clone(), proved_result());
        cache.check(&f); // hit
        assert_eq!(cache.len(), 1);
        assert_eq!(cache.hits(), 1);

        cache.clear();
        assert!(cache.is_empty());
        assert_eq!(cache.hits(), 0);
        assert_eq!(cache.misses(), 0);
    }

    #[test]
    fn test_subsumption_cache_multiple_entries() {
        let mut cache = SubsumptionCache::new();
        let f1 = Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0)));
        let f2 = Formula::Gt(Box::new(var("y")), Box::new(Formula::Int(1)));
        cache.insert_proved(f1.clone(), proved_result());
        cache.insert_proved(f2.clone(), proved_result());

        assert_eq!(cache.len(), 2);
        assert!(cache.check(&f1).is_some());
        assert!(cache.check(&f2).is_some());
        assert_eq!(cache.hits(), 2);
    }

    // -----------------------------------------------------------------------
    // is_subsumed convenience function tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_is_subsumed_returns_cloned_result() {
        let mut cache = SubsumptionCache::new();
        let f = Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(42)));
        cache.insert_proved(f.clone(), proved_result());

        let result = is_subsumed(&f, &mut cache);
        assert!(result.is_some());
        assert!(result.unwrap().is_proved());
    }

    #[test]
    fn test_is_subsumed_returns_none_for_miss() {
        let mut cache = SubsumptionCache::new();
        let f = Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(42)));
        let result = is_subsumed(&f, &mut cache);
        assert!(result.is_none());
    }

    // -----------------------------------------------------------------------
    // formula_is_subsumed_by direct tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_formula_subsumed_equal() {
        let f = Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0)));
        assert!(formula_is_subsumed_by(&f, &f));
    }

    #[test]
    fn test_formula_subsumed_and_conjunct() {
        let a = Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0)));
        let b = Formula::Gt(Box::new(var("y")), Box::new(Formula::Int(1)));
        let proved = Formula::And(vec![a.clone(), b]);
        assert!(formula_is_subsumed_by(&a, &proved));
    }

    #[test]
    fn test_formula_subsumed_or_disjunct() {
        let a = Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0)));
        let b = Formula::Gt(Box::new(var("y")), Box::new(Formula::Int(1)));
        let query = Formula::Or(vec![a.clone(), b]);
        assert!(formula_is_subsumed_by(&query, &a));
    }

    #[test]
    fn test_formula_not_subsumed_unrelated() {
        let a = Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0)));
        let b = Formula::Eq(Box::new(var("y")), Box::new(Formula::Int(1)));
        assert!(!formula_is_subsumed_by(&a, &b));
    }

    // -----------------------------------------------------------------------
    // Alpha-normalization cache hit tests (#434)
    // -----------------------------------------------------------------------

    #[test]
    fn test_alpha_norm_cache_hit_exists() {
        // Two VCs with alpha-equivalent formulas should cache-hit
        let mut cache = QueryCache::new();

        // VC with Exists(a, a > 0)
        let vc1 = make_vc(
            "foo",
            Formula::Exists(
                vec![("a".into(), Sort::Int)],
                Box::new(Formula::Gt(Box::new(var("a")), Box::new(Formula::Int(0)))),
            ),
        );
        cache.insert(&vc1, proved_result());

        // VC with Exists(b, b > 0) — alpha-equivalent, different bound var name
        let vc2 = make_vc(
            "foo",
            Formula::Exists(
                vec![("b".into(), Sort::Int)],
                Box::new(Formula::Gt(Box::new(var("b")), Box::new(Formula::Int(0)))),
            ),
        );

        let result = cache.lookup(&vc2);
        assert!(result.is_some(), "alpha-equivalent formula should cache-hit");
        assert!(result.unwrap().is_proved());
        assert_eq!(cache.stats().hits, 1);
    }

    #[test]
    fn test_alpha_norm_cache_hit_forall() {
        let mut cache = QueryCache::new();

        // Forall(x, x >= 0) proved
        let vc1 = make_vc(
            "bar",
            Formula::Forall(
                vec![("x".into(), Sort::Int)],
                Box::new(Formula::Ge(Box::new(var("x")), Box::new(Formula::Int(0)))),
            ),
        );
        cache.insert(&vc1, proved_result());

        // Forall(y, y >= 0) — same structure, different bound var
        let vc2 = make_vc(
            "bar",
            Formula::Forall(
                vec![("y".into(), Sort::Int)],
                Box::new(Formula::Ge(Box::new(var("y")), Box::new(Formula::Int(0)))),
            ),
        );

        assert!(cache.lookup(&vc2).is_some(), "Forall with renamed bound var should hit");
    }

    #[test]
    fn test_alpha_norm_cache_hit_nested_quantifiers() {
        let mut cache = QueryCache::new();

        // Forall(a, Exists(b, a < b))
        let vc1 = make_vc(
            "nested",
            Formula::Forall(
                vec![("a".into(), Sort::Int)],
                Box::new(Formula::Exists(
                    vec![("b".into(), Sort::Int)],
                    Box::new(Formula::Lt(Box::new(var("a")), Box::new(var("b")))),
                )),
            ),
        );
        cache.insert(&vc1, proved_result());

        // Forall(p, Exists(q, p < q)) — same structure
        let vc2 = make_vc(
            "nested",
            Formula::Forall(
                vec![("p".into(), Sort::Int)],
                Box::new(Formula::Exists(
                    vec![("q".into(), Sort::Int)],
                    Box::new(Formula::Lt(Box::new(var("p")), Box::new(var("q")))),
                )),
            ),
        );

        assert!(
            cache.lookup(&vc2).is_some(),
            "nested quantifiers with renamed bound vars should hit"
        );
    }

    #[test]
    fn test_alpha_norm_formula_hash_equivalent() {
        // Ensure formula_hash itself is alpha-normalized
        let f1 = Formula::Exists(
            vec![("var_alpha".into(), Sort::Int)],
            Box::new(Formula::Eq(Box::new(var("var_alpha")), Box::new(Formula::Int(99)))),
        );
        let f2 = Formula::Exists(
            vec![("var_beta".into(), Sort::Int)],
            Box::new(Formula::Eq(Box::new(var("var_beta")), Box::new(Formula::Int(99)))),
        );
        assert_eq!(
            QueryCache::formula_hash(&f1),
            QueryCache::formula_hash(&f2),
            "formula_hash should be alpha-normalized"
        );
    }

    #[test]
    fn test_alpha_norm_different_structure_no_false_hit() {
        // Different formulas should NOT cache-hit even after normalization
        let mut cache = QueryCache::new();

        let vc1 = make_vc(
            "foo",
            Formula::Exists(
                vec![("a".into(), Sort::Int)],
                Box::new(Formula::Gt(Box::new(var("a")), Box::new(Formula::Int(0)))),
            ),
        );
        cache.insert(&vc1, proved_result());

        // Different body: a < 0 instead of a > 0
        let vc2 = make_vc(
            "foo",
            Formula::Exists(
                vec![("b".into(), Sort::Int)],
                Box::new(Formula::Lt(Box::new(var("b")), Box::new(Formula::Int(0)))),
            ),
        );

        assert!(
            cache.lookup(&vc2).is_none(),
            "structurally different formula should NOT hit"
        );
    }

    #[test]
    fn test_alpha_norm_free_vars_not_renamed() {
        // Free variables should NOT be renamed — different free var names = different hash
        let f1 = Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0)));
        let f2 = Formula::Eq(Box::new(var("y")), Box::new(Formula::Int(0)));
        assert_ne!(
            QueryCache::formula_hash(&f1),
            QueryCache::formula_hash(&f2),
            "free variables should NOT be alpha-normalized"
        );
    }

    #[test]
    fn test_cache_key_alpha_normalized() {
        // CacheKey should also benefit from alpha-normalization
        let f1 = Formula::Exists(
            vec![("a".into(), Sort::Int)],
            Box::new(Formula::Eq(Box::new(var("a")), Box::new(Formula::Int(7)))),
        );
        let f2 = Formula::Exists(
            vec![("z".into(), Sort::Int)],
            Box::new(Formula::Eq(Box::new(var("z")), Box::new(Formula::Int(7)))),
        );
        let vars = FxHashSet::default();
        let k1 = CacheKey::new(&f1, &vars);
        let k2 = CacheKey::new(&f2, &vars);
        assert_eq!(
            k1.formula_hash, k2.formula_hash,
            "CacheKey formula_hash should be alpha-normalized"
        );
    }
}
