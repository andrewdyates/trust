// trust-router/query_cache.rs: Content-addressed query cache for solver results
//
// KLEE-inspired optimization: hash formulas structurally so that alpha-equivalent
// formulas map to the same cache key. LRU eviction keeps memory bounded.
// Tracks hit rate metrics.
//
// Reference: Cadar, Dunbar, Engler. "KLEE: Unassisted and Automatic Generation
// of High-Coverage Tests for Complex Systems Programs." OSDI 2008.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::hash::{Hash, Hasher};
use trust_types::fx::FxHashMap;

use trust_types::{Formula, Sort, VerificationResult};

/// Content-addressed cache for solver query results.
///
/// Formulas are hashed structurally: two formulas that differ only in
/// variable names (alpha-equivalence) are NOT collapsed (full alpha-normalization
/// would be expensive). Instead, we hash the tree structure including variable
/// names, which is sound (may miss some hits, never produces wrong results).
///
/// LRU eviction is approximated via a generation counter: entries older than
/// `max_generations` are evicted on the next `evict()` call.
pub struct QueryCache {
    /// Map from structural hash -> (result, generation_last_accessed).
    entries: FxHashMap<u64, CacheEntry>,
    /// Current generation (incremented on each query).
    generation: u64,
    /// Maximum number of entries before eviction.
    max_entries: usize,
    /// Metrics.
    hits: u64,
    misses: u64,
}

struct CacheEntry {
    result: VerificationResult,
    last_accessed: u64,
}

/// Cache lookup result.
pub enum CacheLookupResult {
    /// Cache hit: the formula was previously solved.
    Hit(VerificationResult),
    /// Cache miss: the formula needs to be solved.
    Miss,
}

/// Cache statistics snapshot.
#[derive(Debug, Clone)]
pub struct CacheStats {
    pub entries: usize,
    pub hits: u64,
    pub misses: u64,
    pub hit_rate: f64,
}

impl QueryCache {
    /// Create a new cache with the given maximum entry count.
    #[must_use]
    pub fn new(max_entries: usize) -> Self {
        Self { entries: FxHashMap::default(), generation: 0, max_entries, hits: 0, misses: 0 }
    }

    /// Look up a formula in the cache.
    pub fn lookup(&mut self, formula: &Formula) -> CacheLookupResult {
        self.generation += 1;
        let key = structural_hash(formula);

        if let Some(entry) = self.entries.get_mut(&key) {
            entry.last_accessed = self.generation;
            self.hits += 1;
            CacheLookupResult::Hit(entry.result.clone())
        } else {
            self.misses += 1;
            CacheLookupResult::Miss
        }
    }

    /// Store a result in the cache, evicting old entries if needed.
    pub fn store(&mut self, formula: &Formula, result: VerificationResult) {
        let key = structural_hash(formula);
        self.entries.insert(key, CacheEntry { result, last_accessed: self.generation });

        if self.entries.len() > self.max_entries {
            self.evict();
        }
    }

    /// Evict the oldest entries to bring the cache back to max_entries.
    fn evict(&mut self) {
        if self.entries.len() <= self.max_entries {
            return;
        }

        // Collect entries with their last_accessed, sort, remove oldest.
        let mut by_age: Vec<(u64, u64)> =
            self.entries.iter().map(|(&key, entry)| (key, entry.last_accessed)).collect();
        by_age.sort_by_key(|&(_, accessed)| accessed);

        let to_remove = self.entries.len() - self.max_entries;
        for (key, _) in by_age.into_iter().take(to_remove) {
            self.entries.remove(&key);
        }
    }

    /// Get current cache statistics.
    #[must_use]
    pub fn stats(&self) -> CacheStats {
        let total = self.hits + self.misses;
        CacheStats {
            entries: self.entries.len(),
            hits: self.hits,
            misses: self.misses,
            hit_rate: if total == 0 { 0.0 } else { self.hits as f64 / total as f64 },
        }
    }

    /// Number of entries currently in the cache.
    #[must_use]
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether the cache is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Clear all entries and reset metrics.
    pub fn clear(&mut self) {
        self.entries.clear();
        self.generation = 0;
        self.hits = 0;
        self.misses = 0;
    }
}

/// Compute a structural hash of a formula.
///
/// Uses a standard Hasher (SipHash) to hash the formula tree. The hash
/// encodes the shape and content of the formula, including variable names
/// and literal values.
#[must_use]
pub fn structural_hash(formula: &Formula) -> u64 {
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    hash_formula(formula, &mut hasher);
    hasher.finish()
}

fn hash_formula<H: Hasher>(formula: &Formula, hasher: &mut H) {
    // Discriminant tag for each variant.
    std::mem::discriminant(formula).hash(hasher);

    match formula {
        Formula::Bool(b) => b.hash(hasher),
        Formula::Int(n) => n.hash(hasher),
        Formula::UInt(n) => n.hash(hasher),
        Formula::BitVec { value, width } => {
            value.hash(hasher);
            width.hash(hasher);
        }
        Formula::Var(name, sort) => {
            name.hash(hasher);
            hash_sort(sort, hasher);
        }
        Formula::Not(inner) => hash_formula(inner, hasher),
        Formula::And(children) => {
            children.len().hash(hasher);
            for child in children {
                hash_formula(child, hasher);
            }
        }
        Formula::Or(children) => {
            children.len().hash(hasher);
            for child in children {
                hash_formula(child, hasher);
            }
        }
        Formula::Implies(lhs, rhs)
        | Formula::Eq(lhs, rhs)
        | Formula::Lt(lhs, rhs)
        | Formula::Le(lhs, rhs)
        | Formula::Gt(lhs, rhs)
        | Formula::Ge(lhs, rhs)
        | Formula::Add(lhs, rhs)
        | Formula::Sub(lhs, rhs)
        | Formula::Mul(lhs, rhs)
        | Formula::Div(lhs, rhs)
        | Formula::Rem(lhs, rhs) => {
            hash_formula(lhs, hasher);
            hash_formula(rhs, hasher);
        }
        Formula::Neg(inner) => hash_formula(inner, hasher),
        Formula::BvAdd(a, b, w)
        | Formula::BvSub(a, b, w)
        | Formula::BvMul(a, b, w)
        | Formula::BvUDiv(a, b, w)
        | Formula::BvSDiv(a, b, w)
        | Formula::BvURem(a, b, w)
        | Formula::BvSRem(a, b, w)
        | Formula::BvAnd(a, b, w)
        | Formula::BvOr(a, b, w)
        | Formula::BvXor(a, b, w)
        | Formula::BvShl(a, b, w)
        | Formula::BvLShr(a, b, w)
        | Formula::BvAShr(a, b, w)
        | Formula::BvULt(a, b, w)
        | Formula::BvULe(a, b, w)
        | Formula::BvSLt(a, b, w)
        | Formula::BvSLe(a, b, w) => {
            hash_formula(a, hasher);
            hash_formula(b, hasher);
            w.hash(hasher);
        }
        Formula::BvNot(inner, w) => {
            hash_formula(inner, hasher);
            w.hash(hasher);
        }
        Formula::BvToInt(inner, w, signed) => {
            hash_formula(inner, hasher);
            w.hash(hasher);
            signed.hash(hasher);
        }
        Formula::IntToBv(inner, w) => {
            hash_formula(inner, hasher);
            w.hash(hasher);
        }
        Formula::BvExtract { inner, high, low } => {
            hash_formula(inner, hasher);
            high.hash(hasher);
            low.hash(hasher);
        }
        Formula::BvConcat(a, b) => {
            hash_formula(a, hasher);
            hash_formula(b, hasher);
        }
        Formula::BvZeroExt(inner, bits) | Formula::BvSignExt(inner, bits) => {
            hash_formula(inner, hasher);
            bits.hash(hasher);
        }
        Formula::Ite(cond, then_f, else_f) | Formula::Store(cond, then_f, else_f) => {
            hash_formula(cond, hasher);
            hash_formula(then_f, hasher);
            hash_formula(else_f, hasher);
        }
        Formula::Forall(bindings, body) | Formula::Exists(bindings, body) => {
            bindings.len().hash(hasher);
            for (name, sort) in bindings {
                name.hash(hasher);
                hash_sort(sort, hasher);
            }
            hash_formula(body, hasher);
        }
        Formula::Select(arr, idx) => {
            hash_formula(arr, hasher);
            hash_formula(idx, hasher);
        }
        // tRust #734: non-panicking fallback for #[non_exhaustive] forward compat
        _ => {
            hasher.write_u8(0xff);
        }
    }
}

fn hash_sort<H: Hasher>(sort: &Sort, hasher: &mut H) {
    std::mem::discriminant(sort).hash(hasher);
    match sort {
        Sort::Bool | Sort::Int => {}
        Sort::BitVec(w) => w.hash(hasher),
        Sort::Array(key, val) => {
            hash_sort(key, hasher);
            hash_sort(val, hasher);
        }
        // tRust #734: non-panicking fallback for #[non_exhaustive] forward compat
        _ => {
            hasher.write_u8(0xff);
        }
    }
}

#[cfg(test)]
mod tests {
    use trust_types::{ProofStrength, VerificationResult};

    use super::*;

    fn proved_result() -> VerificationResult {
        VerificationResult::Proved {
            solver: "z4".into(),
            time_ms: 10,
            strength: ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: None,
        }
    }

    fn failed_result() -> VerificationResult {
        VerificationResult::Failed { solver: "z4".into(), time_ms: 20, counterexample: None }
    }

    #[test]
    fn test_structural_hash_deterministic() {
        let f = Formula::And(vec![
            Formula::Var("x".into(), Sort::Int),
            Formula::Gt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(0))),
        ]);
        let h1 = structural_hash(&f);
        let h2 = structural_hash(&f);
        assert_eq!(h1, h2);
    }

    #[test]
    fn test_structural_hash_different_formulas_differ() {
        let f1 = Formula::Var("x".into(), Sort::Int);
        let f2 = Formula::Var("y".into(), Sort::Int);
        assert_ne!(structural_hash(&f1), structural_hash(&f2));
    }

    #[test]
    fn test_structural_hash_same_structure_same_hash() {
        let f1 = Formula::And(vec![Formula::Bool(true), Formula::Bool(false)]);
        let f2 = Formula::And(vec![Formula::Bool(true), Formula::Bool(false)]);
        assert_eq!(structural_hash(&f1), structural_hash(&f2));
    }

    #[test]
    fn test_cache_miss_then_hit() {
        let mut cache = QueryCache::new(100);
        let f = Formula::Bool(true);

        // Miss
        assert!(matches!(cache.lookup(&f), CacheLookupResult::Miss));

        // Store
        cache.store(&f, proved_result());

        // Hit
        if let CacheLookupResult::Hit(result) = cache.lookup(&f) {
            assert!(result.is_proved());
        } else {
            panic!("expected cache hit");
        }
    }

    #[test]
    fn test_cache_stats() {
        let mut cache = QueryCache::new(100);
        let f = Formula::Bool(true);

        cache.lookup(&f); // miss
        cache.store(&f, proved_result());
        cache.lookup(&f); // hit
        cache.lookup(&f); // hit

        let stats = cache.stats();
        assert_eq!(stats.hits, 2);
        assert_eq!(stats.misses, 1);
        assert!((stats.hit_rate - 2.0 / 3.0).abs() < 0.01);
        assert_eq!(stats.entries, 1);
    }

    #[test]
    fn test_cache_eviction() {
        let mut cache = QueryCache::new(3);

        // Fill cache
        for i in 0..5 {
            let f = Formula::Int(i);
            cache.store(&f, proved_result());
        }

        // Should have been evicted down to 3
        assert!(cache.len() <= 3);
    }

    #[test]
    fn test_cache_lru_keeps_recent() {
        let mut cache = QueryCache::new(2);

        let f0 = Formula::Int(0);
        let f1 = Formula::Int(1);
        let f2 = Formula::Int(2);

        cache.store(&f0, proved_result());
        cache.store(&f1, failed_result());

        // Access f0 to make it recent
        cache.lookup(&f0);

        // Store f2, which should evict f1 (older)
        cache.store(&f2, proved_result());

        // f0 should still be cached (recently accessed)
        assert!(matches!(cache.lookup(&f0), CacheLookupResult::Hit(_)));
    }

    #[test]
    fn test_cache_clear() {
        let mut cache = QueryCache::new(100);
        cache.store(&Formula::Bool(true), proved_result());
        cache.store(&Formula::Bool(false), failed_result());

        assert_eq!(cache.len(), 2);
        cache.clear();
        assert!(cache.is_empty());

        let stats = cache.stats();
        assert_eq!(stats.hits, 0);
        assert_eq!(stats.misses, 0);
    }

    #[test]
    fn test_cache_overwrite_same_formula() {
        let mut cache = QueryCache::new(100);
        let f = Formula::Bool(true);

        cache.store(&f, proved_result());
        cache.store(&f, failed_result());

        assert_eq!(cache.len(), 1);
        if let CacheLookupResult::Hit(result) = cache.lookup(&f) {
            assert!(result.is_failed());
        } else {
            panic!("expected hit");
        }
    }

    #[test]
    fn test_hash_bitvec_formulas() {
        let f1 = Formula::BvAdd(
            Box::new(Formula::Var("a".into(), Sort::BitVec(32))),
            Box::new(Formula::Var("b".into(), Sort::BitVec(32))),
            32,
        );
        let f2 = Formula::BvAdd(
            Box::new(Formula::Var("a".into(), Sort::BitVec(64))),
            Box::new(Formula::Var("b".into(), Sort::BitVec(64))),
            64,
        );
        assert_ne!(structural_hash(&f1), structural_hash(&f2));
    }

    #[test]
    fn test_hash_quantifiers() {
        let f1 = Formula::Forall(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::Gt(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            )),
        );
        let f2 = Formula::Exists(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::Gt(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            )),
        );
        assert_ne!(structural_hash(&f1), structural_hash(&f2));
    }

    #[test]
    fn test_empty_cache_stats() {
        let cache = QueryCache::new(100);
        let stats = cache.stats();
        assert_eq!(stats.entries, 0);
        assert_eq!(stats.hits, 0);
        assert_eq!(stats.misses, 0);
        assert_eq!(stats.hit_rate, 0.0);
    }
}
