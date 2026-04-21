// trust-symex/constraint_cache.rs: Constraint caching for solver invocations (#288)
//
// Caches solver results (Sat/Unsat/Unknown) keyed by normalized constraint hashes.
// Avoids redundant solver calls during symbolic execution by recognizing
// structurally equivalent constraints after canonicalization.
//
// Inspired by KLEE's query caching (refs/klee/lib/Solver/).
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;
use std::hash::{Hash, Hasher};

use trust_types::Formula;

// ---------------------------------------------------------------------------
// Cache entry types
// ---------------------------------------------------------------------------

/// Result cached from a solver invocation.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum CacheEntry {
    /// Satisfiable with a model (variable name -> value as string).
    Sat(Vec<(String, String)>),
    /// Unsatisfiable — no model exists.
    Unsat,
    /// Solver returned unknown (timeout, resource limit, etc.).
    Unknown,
}

// ---------------------------------------------------------------------------
// Constraint key (normalized hash)
// ---------------------------------------------------------------------------

/// A hash-based key for normalized constraints.
///
/// Two formulas that are structurally equivalent after normalization
/// will produce the same `ConstraintKey`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct ConstraintKey {
    hash: u64,
}

impl ConstraintKey {
    /// Build a cache key from a formula by normalizing then hashing.
    #[must_use]
    pub(crate) fn from_formula(formula: &Formula) -> Self {
        let normalized = normalize_constraint(formula);
        let hash = hash_formula(&normalized);
        Self { hash }
    }

    /// Return the raw hash value.
    #[must_use]
    pub(crate) fn hash_value(&self) -> u64 {
        self.hash
    }
}

// ---------------------------------------------------------------------------
// Cache statistics
// ---------------------------------------------------------------------------

/// Statistics about cache performance.
#[derive(Debug, Clone, Default, PartialEq)]
pub(crate) struct CacheStats {
    /// Number of cache hits.
    pub hits: u64,
    /// Number of cache misses.
    pub misses: u64,
    /// Number of entries evicted due to capacity limits.
    pub evictions: u64,
    /// Number of entries currently in the cache.
    pub entries: usize,
    /// Total solver calls avoided (same as hits).
    pub solver_calls_saved: u64,
}

impl CacheStats {
    /// Hit rate as a fraction in [0.0, 1.0]. Returns 0.0 if no lookups.
    #[must_use]
    pub(crate) fn hit_rate(&self) -> f64 {
        let total = self.hits + self.misses;
        if total == 0 {
            0.0
        } else {
            self.hits as f64 / total as f64
        }
    }

    /// Total number of lookups performed.
    #[must_use]
    pub(crate) fn total_lookups(&self) -> u64 {
        self.hits + self.misses
    }
}

// ---------------------------------------------------------------------------
// LRU constraint cache
// ---------------------------------------------------------------------------

/// LRU constraint cache mapping normalized formula hashes to solver results.
///
/// When the cache exceeds `capacity`, the least-recently-used entry is evicted.
/// "Recently used" is tracked by access order (both lookup hits and inserts).
pub(crate) struct ConstraintCache {
    /// Maximum number of entries before eviction.
    capacity: usize,
    /// Map from key to (entry, access_order).
    entries: FxHashMap<ConstraintKey, (CacheEntry, u64)>,
    /// Monotonically increasing access counter for LRU ordering.
    access_counter: u64,
    /// Accumulated statistics.
    stats: CacheStats,
}

impl ConstraintCache {
    /// Create a new cache with the given capacity.
    ///
    /// # Panics
    /// Panics if capacity is zero.
    #[must_use]
    pub(crate) fn new(capacity: usize) -> Self {
        assert!(capacity > 0, "cache capacity must be > 0");
        Self {
            capacity,
            entries: FxHashMap::default(),
            access_counter: 0,
            stats: CacheStats::default(),
        }
    }

    /// Look up a formula in the cache.
    ///
    /// Returns `Some(entry)` on hit, `None` on miss. Updates stats accordingly.
    pub(crate) fn lookup(&mut self, formula: &Formula) -> Option<&CacheEntry> {
        let key = ConstraintKey::from_formula(formula);
        if self.entries.contains_key(&key) {
            self.access_counter += 1;
            // Update access order — re-borrow after contains_key check.
            if let Some(entry) = self.entries.get_mut(&key) {
                entry.1 = self.access_counter;
            }
            self.stats.hits += 1;
            self.stats.solver_calls_saved += 1;
            // Return immutable reference.
            self.entries.get(&key).map(|(e, _)| e)
        } else {
            self.stats.misses += 1;
            None
        }
    }

    /// Insert a solver result into the cache.
    ///
    /// If the cache is at capacity, evicts the least-recently-used entry first.
    pub(crate) fn insert(&mut self, formula: &Formula, entry: CacheEntry) {
        let key = ConstraintKey::from_formula(formula);

        // If key already exists, just update.
        if self.entries.contains_key(&key) {
            self.access_counter += 1;
            self.entries.insert(key, (entry, self.access_counter));
            self.stats.entries = self.entries.len();
            return;
        }

        // Evict if at capacity.
        if self.entries.len() >= self.capacity {
            self.evict_lru();
        }

        self.access_counter += 1;
        self.entries.insert(key, (entry, self.access_counter));
        self.stats.entries = self.entries.len();
    }

    /// Get current cache statistics.
    #[must_use]
    pub(crate) fn stats(&self) -> &CacheStats {
        &self.stats
    }

    /// Number of entries currently in the cache.
    #[must_use]
    pub(crate) fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether the cache is empty.
    #[must_use]
    pub(crate) fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Clear all entries and reset statistics.
    pub(crate) fn clear(&mut self) {
        self.entries.clear();
        self.access_counter = 0;
        self.stats = CacheStats::default();
    }

    /// Maximum capacity.
    #[must_use]
    pub(crate) fn capacity(&self) -> usize {
        self.capacity
    }

    /// Evict the least-recently-used entry.
    fn evict_lru(&mut self) {
        if let Some(lru_key) = self
            .entries
            .iter()
            .min_by_key(|(_, (_, order))| *order)
            .map(|(k, _)| k.clone())
        {
            self.entries.remove(&lru_key);
            self.stats.evictions += 1;
        }
        self.stats.entries = self.entries.len();
    }
}

// ---------------------------------------------------------------------------
// Formula normalization
// ---------------------------------------------------------------------------

/// Normalize a formula for caching purposes.
///
/// Normalization improves cache hit rates by canonicalizing structurally
/// equivalent formulas to the same form:
/// - `And`/`Or` children are sorted by their hash
/// - Double negation is eliminated: `Not(Not(x))` -> `x`
/// - `And`/`Or` with a single child is flattened
/// - Nested `And(And(...))` and `Or(Or(...))` are flattened
#[must_use]
pub(crate) fn normalize_constraint(formula: &Formula) -> Formula {
    match formula {
        // Leaves — no normalization needed.
        Formula::Bool(_)
        | Formula::Int(_)
        | Formula::UInt(_)
        | Formula::BitVec { .. }
        | Formula::Var(..) => formula.clone(),

        // Double negation elimination.
        Formula::Not(inner) => {
            let inner_norm = normalize_constraint(inner);
            if let Formula::Not(double_inner) = inner_norm {
                *double_inner
            } else {
                Formula::Not(Box::new(inner_norm))
            }
        }

        // Commutative n-ary: sort children by hash for canonical order.
        Formula::And(terms) => {
            let mut normalized: Vec<Formula> = terms
                .iter()
                .flat_map(|t| {
                    let n = normalize_constraint(t);
                    // Flatten nested And.
                    if let Formula::And(inner) = n {
                        inner
                    } else {
                        vec![n]
                    }
                })
                .collect();

            if normalized.len() == 1 {
                return normalized.remove(0);
            }

            normalized.sort_by_key(hash_formula);
            Formula::And(normalized)
        }

        Formula::Or(terms) => {
            let mut normalized: Vec<Formula> = terms
                .iter()
                .flat_map(|t| {
                    let n = normalize_constraint(t);
                    // Flatten nested Or.
                    if let Formula::Or(inner) = n {
                        inner
                    } else {
                        vec![n]
                    }
                })
                .collect();

            if normalized.len() == 1 {
                return normalized.remove(0);
            }

            normalized.sort_by_key(hash_formula);
            Formula::Or(normalized)
        }

        // For all other nodes: recursively normalize children.
        other => other.clone().map_children(&mut |child| normalize_constraint(&child)),
    }
}

// ---------------------------------------------------------------------------
// Formula hashing (structural)
// ---------------------------------------------------------------------------

/// Compute a structural hash of a formula.
///
/// Uses `std::hash::DefaultHasher` over the SMT-LIB serialization for
/// a simple, collision-resistant hash. This is sufficient for cache keys.
fn hash_formula(formula: &Formula) -> u64 {
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    formula.to_smtlib().hash(&mut hasher);
    hasher.finish()
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use trust_types::Sort;

    fn var(name: &str) -> Formula {
        Formula::Var(name.into(), Sort::Int)
    }

    fn bv_var(name: &str, w: u32) -> Formula {
        Formula::Var(name.into(), Sort::BitVec(w))
    }

    // --- ConstraintKey tests ---

    #[test]
    fn test_constraint_key_deterministic() {
        let f = Formula::And(vec![var("x"), var("y")]);
        let k1 = ConstraintKey::from_formula(&f);
        let k2 = ConstraintKey::from_formula(&f);
        assert_eq!(k1, k2);
    }

    #[test]
    fn test_constraint_key_different_formulas() {
        let f1 = var("x");
        let f2 = var("y");
        let k1 = ConstraintKey::from_formula(&f1);
        let k2 = ConstraintKey::from_formula(&f2);
        assert_ne!(k1, k2);
    }

    #[test]
    fn test_constraint_key_normalized_equivalence() {
        // And(x, y) and And(y, x) should produce the same key after normalization.
        let f1 = Formula::And(vec![var("x"), var("y")]);
        let f2 = Formula::And(vec![var("y"), var("x")]);
        let k1 = ConstraintKey::from_formula(&f1);
        let k2 = ConstraintKey::from_formula(&f2);
        assert_eq!(k1, k2);
    }

    // --- CacheEntry tests ---

    #[test]
    fn test_cache_entry_variants() {
        let sat = CacheEntry::Sat(vec![("x".into(), "42".into())]);
        let unsat = CacheEntry::Unsat;
        let unknown = CacheEntry::Unknown;
        assert_ne!(sat, unsat);
        assert_ne!(unsat, unknown);
    }

    // --- CacheStats tests ---

    #[test]
    fn test_cache_stats_hit_rate_zero_lookups() {
        let stats = CacheStats::default();
        assert!((stats.hit_rate() - 0.0).abs() < f64::EPSILON);
        assert_eq!(stats.total_lookups(), 0);
    }

    #[test]
    fn test_cache_stats_hit_rate_calculation() {
        let stats = CacheStats {
            hits: 3,
            misses: 1,
            evictions: 0,
            entries: 1,
            solver_calls_saved: 3,
        };
        assert!((stats.hit_rate() - 0.75).abs() < f64::EPSILON);
        assert_eq!(stats.total_lookups(), 4);
    }

    // --- ConstraintCache tests ---

    #[test]
    fn test_cache_new_empty() {
        let cache = ConstraintCache::new(10);
        assert!(cache.is_empty());
        assert_eq!(cache.len(), 0);
        assert_eq!(cache.capacity(), 10);
    }

    #[test]
    #[should_panic(expected = "cache capacity must be > 0")]
    fn test_cache_zero_capacity_panics() {
        let _cache = ConstraintCache::new(0);
    }

    #[test]
    fn test_cache_insert_and_lookup() {
        let mut cache = ConstraintCache::new(10);
        let f = Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(5)));

        cache.insert(&f, CacheEntry::Sat(vec![("x".into(), "5".into())]));
        assert_eq!(cache.len(), 1);

        let result = cache.lookup(&f);
        assert!(result.is_some());
        assert_eq!(
            result.unwrap(),
            &CacheEntry::Sat(vec![("x".into(), "5".into())])
        );
    }

    #[test]
    fn test_cache_miss() {
        let mut cache = ConstraintCache::new(10);
        let f = var("x");
        assert!(cache.lookup(&f).is_none());
        assert_eq!(cache.stats().misses, 1);
        assert_eq!(cache.stats().hits, 0);
    }

    #[test]
    fn test_cache_lru_eviction() {
        let mut cache = ConstraintCache::new(2);

        let f1 = Formula::Int(1);
        let f2 = Formula::Int(2);
        let f3 = Formula::Int(3);

        cache.insert(&f1, CacheEntry::Sat(vec![]));
        cache.insert(&f2, CacheEntry::Unsat);

        assert_eq!(cache.len(), 2);

        // Insert a third — should evict f1 (least recently used).
        cache.insert(&f3, CacheEntry::Unknown);
        assert_eq!(cache.len(), 2);
        assert_eq!(cache.stats().evictions, 1);

        // f1 should be gone.
        assert!(cache.lookup(&f1).is_none());
        // f2 and f3 should still be present.
        assert!(cache.lookup(&f2).is_some());
        assert!(cache.lookup(&f3).is_some());
    }

    #[test]
    fn test_cache_lru_access_refreshes_order() {
        let mut cache = ConstraintCache::new(2);

        let f1 = Formula::Int(1);
        let f2 = Formula::Int(2);
        let f3 = Formula::Int(3);

        cache.insert(&f1, CacheEntry::Unsat);
        cache.insert(&f2, CacheEntry::Unsat);

        // Access f1 to refresh it.
        cache.lookup(&f1);

        // Now insert f3 — should evict f2 (now least recently used).
        cache.insert(&f3, CacheEntry::Unknown);

        assert!(cache.lookup(&f1).is_some(), "f1 should survive (was accessed)");
        assert!(cache.lookup(&f2).is_none(), "f2 should be evicted");
        assert!(cache.lookup(&f3).is_some(), "f3 should be present");
    }

    #[test]
    fn test_cache_clear() {
        let mut cache = ConstraintCache::new(10);
        cache.insert(&Formula::Bool(true), CacheEntry::Sat(vec![]));
        cache.insert(&Formula::Bool(false), CacheEntry::Unsat);
        assert_eq!(cache.len(), 2);

        cache.clear();
        assert!(cache.is_empty());
        assert_eq!(cache.stats().hits, 0);
        assert_eq!(cache.stats().misses, 0);
    }

    #[test]
    fn test_cache_stats_tracking() {
        let mut cache = ConstraintCache::new(10);
        let f = Formula::Bool(true);

        cache.insert(&f, CacheEntry::Sat(vec![]));

        // First lookup — hit.
        cache.lookup(&f);
        assert_eq!(cache.stats().hits, 1);
        assert_eq!(cache.stats().misses, 0);
        assert_eq!(cache.stats().solver_calls_saved, 1);

        // Second lookup — another hit.
        cache.lookup(&f);
        assert_eq!(cache.stats().hits, 2);

        // Miss on unknown formula.
        cache.lookup(&Formula::Bool(false));
        assert_eq!(cache.stats().misses, 1);

        assert!((cache.stats().hit_rate() - (2.0 / 3.0)).abs() < 0.01);
    }

    #[test]
    fn test_cache_overwrite_existing_key() {
        let mut cache = ConstraintCache::new(10);
        let f = Formula::Int(42);

        cache.insert(&f, CacheEntry::Unknown);
        assert_eq!(cache.lookup(&f), Some(&CacheEntry::Unknown));

        cache.insert(&f, CacheEntry::Unsat);
        assert_eq!(cache.lookup(&f), Some(&CacheEntry::Unsat));
        assert_eq!(cache.len(), 1); // Not duplicated.
    }

    // --- Normalization tests ---

    #[test]
    fn test_normalize_and_commutative() {
        let f1 = Formula::And(vec![var("a"), var("b"), var("c")]);
        let f2 = Formula::And(vec![var("c"), var("a"), var("b")]);
        let n1 = normalize_constraint(&f1);
        let n2 = normalize_constraint(&f2);
        assert_eq!(n1, n2);
    }

    #[test]
    fn test_normalize_or_commutative() {
        let f1 = Formula::Or(vec![var("x"), var("y")]);
        let f2 = Formula::Or(vec![var("y"), var("x")]);
        let n1 = normalize_constraint(&f1);
        let n2 = normalize_constraint(&f2);
        assert_eq!(n1, n2);
    }

    #[test]
    fn test_normalize_double_negation() {
        let f = Formula::Not(Box::new(Formula::Not(Box::new(var("x")))));
        let n = normalize_constraint(&f);
        assert_eq!(n, var("x"));
    }

    #[test]
    fn test_normalize_single_and_flattened() {
        let f = Formula::And(vec![var("x")]);
        let n = normalize_constraint(&f);
        assert_eq!(n, var("x"));
    }

    #[test]
    fn test_normalize_nested_and_flattened() {
        let f = Formula::And(vec![
            Formula::And(vec![var("a"), var("b")]),
            var("c"),
        ]);
        let n = normalize_constraint(&f);
        // Should be a single And with 3 children, sorted.
        if let Formula::And(terms) = &n {
            assert_eq!(terms.len(), 3);
        } else {
            panic!("expected And, got {n:?}");
        }
    }

    #[test]
    fn test_normalize_leaf_unchanged() {
        let f = Formula::Int(42);
        assert_eq!(normalize_constraint(&f), f);

        let f2 = Formula::Bool(true);
        assert_eq!(normalize_constraint(&f2), f2);

        let f3 = var("x");
        assert_eq!(normalize_constraint(&f3), f3);
    }

    #[test]
    fn test_normalize_binary_recursive() {
        // Normalization recurses into binary nodes.
        let f = Formula::Eq(
            Box::new(Formula::And(vec![var("b"), var("a")])),
            Box::new(Formula::Bool(true)),
        );
        let n = normalize_constraint(&f);
        // The inner And should have its children sorted.
        if let Formula::Eq(lhs, _) = &n {
            if let Formula::And(terms) = lhs.as_ref() {
                // Sorted order depends on hash — just verify both present and length 2.
                assert_eq!(terms.len(), 2);
            } else {
                panic!("expected And in Eq lhs");
            }
        } else {
            panic!("expected Eq");
        }
    }

    #[test]
    fn test_normalize_bitvector_preserved() {
        let f = Formula::BvAdd(
            Box::new(bv_var("a", 32)),
            Box::new(bv_var("b", 32)),
            32,
        );
        let n = normalize_constraint(&f);
        assert_eq!(n, f); // Non-commutative op, no reordering.
    }
}
