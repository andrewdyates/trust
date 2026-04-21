// trust-cache/incremental.rs: Incremental verification with dependency tracking
//
// Wraps VerificationCache + DependencyTracker to provide dependency-aware
// incremental verification. When a function's spec changes, all transitive
// callers are automatically invalidated.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashSet;

use crate::invalidation::{plan_invalidation, DependencyTracker, InvalidationPlan};
use crate::{CacheEntry, CacheLookup, VerificationCache};

/// Incremental verifier combining cache + dependency tracking.
///
/// Maintains a generation counter for staleness detection: each call to
/// `update_after_change` bumps the generation, and cached entries from
/// earlier generations for affected functions are treated as stale.
pub struct IncrementalVerifier {
    cache: VerificationCache,
    deps: DependencyTracker,
    /// Monotonically increasing generation counter.
    generation: u64,
    /// Functions invalidated in the current generation (not yet re-verified).
    stale: FxHashSet<String>,
}

impl IncrementalVerifier {
    /// Create a new incremental verifier with the given cache.
    pub fn new(cache: VerificationCache) -> Self {
        IncrementalVerifier {
            cache,
            deps: DependencyTracker::new(),
            generation: 0,
            stale: FxHashSet::default(),
        }
    }

    /// Create a new incremental verifier with an in-memory cache.
    pub fn in_memory() -> Self {
        Self::new(VerificationCache::in_memory())
    }

    /// Register that `function` depends on `dependency` (calls it).
    pub fn add_dependency(&mut self, function: &str, dependency: &str) {
        self.deps.add_dependency(function, dependency);
    }

    /// Register multiple dependencies at once.
    pub fn add_dependencies(&mut self, function: &str, dependencies: &[&str]) {
        self.deps.add_dependencies(function, dependencies);
    }

    /// Process spec changes: invalidate affected functions and return the list
    /// of functions that need re-verification, ordered callee-first.
    ///
    /// Bumps the generation counter and marks all transitively affected
    /// functions as stale. Returns the invalidation plan.
    pub fn update_after_change(&mut self, changed_functions: &[String]) -> Vec<String> {
        if changed_functions.is_empty() {
            return Vec::new();
        }

        self.generation += 1;

        let plan = plan_invalidation(changed_functions, &self.deps);

        // Invalidate all affected entries in the underlying cache
        for func in &plan.functions {
            self.cache.invalidate(func);
            self.stale.insert(func.clone());
        }

        plan.functions
    }

    /// Process spec changes and return the full invalidation plan (with reasons).
    pub fn update_after_change_with_plan(
        &mut self,
        changed_functions: &[String],
    ) -> InvalidationPlan {
        if changed_functions.is_empty() {
            return InvalidationPlan::default();
        }

        self.generation += 1;

        let plan = plan_invalidation(changed_functions, &self.deps);

        for func in &plan.functions {
            self.cache.invalidate(func);
            self.stale.insert(func.clone());
        }

        plan
    }

    /// Check if a function's cached result is still valid.
    ///
    /// Returns `false` if the function was invalidated and has not been
    /// re-verified since.
    #[must_use]
    pub fn is_fresh(&self, func: &str) -> bool {
        !self.stale.contains(func)
    }

    /// Look up a cached result, respecting staleness.
    ///
    /// Returns `CacheLookup::Miss` if the function is stale even if
    /// there is a cache entry (which should have been removed by
    /// `update_after_change`, but this is a safety net).
    pub fn lookup(&mut self, def_path: &str, content_hash: &str, spec_hash: &str) -> CacheLookup {
        if self.stale.contains(def_path) {
            return CacheLookup::Miss;
        }
        self.cache.lookup(def_path, content_hash, spec_hash)
    }

    /// Store a verification result and mark the function as fresh.
    pub fn store(&mut self, def_path: &str, entry: CacheEntry) {
        self.stale.remove(def_path);
        self.cache.store(def_path, entry);
    }

    /// Current generation counter.
    #[must_use]
    pub fn generation(&self) -> u64 {
        self.generation
    }

    /// Number of currently stale (invalidated, not yet re-verified) functions.
    #[must_use]
    pub fn stale_count(&self) -> usize {
        self.stale.len()
    }

    /// Get the set of currently stale functions.
    #[must_use]
    pub fn stale_functions(&self) -> &FxHashSet<String> {
        &self.stale
    }

    /// Access the underlying cache (read-only).
    #[must_use]
    pub fn cache(&self) -> &VerificationCache {
        &self.cache
    }

    /// Access the underlying cache (mutable).
    pub fn cache_mut(&mut self) -> &mut VerificationCache {
        &mut self.cache
    }

    /// Access the dependency tracker (read-only).
    #[must_use]
    pub fn deps(&self) -> &DependencyTracker {
        &self.deps
    }

    /// Access the dependency tracker (mutable).
    pub fn deps_mut(&mut self) -> &mut DependencyTracker {
        &mut self.deps
    }

    /// Summary string for diagnostics.
    #[must_use]
    pub fn summary(&self) -> String {
        format!(
            "gen={}, stale={}, cache=[{}]",
            self.generation,
            self.stale.len(),
            self.cache.summary()
        )
    }
}

#[cfg(test)]
mod tests {
    use trust_types::FunctionVerdict;

    use super::*;
    use crate::CacheEntry;

    fn sample_entry(hash: &str) -> CacheEntry {
        CacheEntry {
            content_hash: hash.to_string(),
            verdict: FunctionVerdict::Verified,
            total_obligations: 1,
            proved: 1,
            failed: 0,
            unknown: 0,
            runtime_checked: 0,
            cached_at: 100,
            spec_hash: String::new(),
        }
    }

    // -- Basic lifecycle --

    #[test]
    fn test_incremental_new_is_fresh() {
        let verifier = IncrementalVerifier::in_memory();
        assert_eq!(verifier.generation(), 0);
        assert_eq!(verifier.stale_count(), 0);
        assert!(verifier.is_fresh("anything"));
    }

    #[test]
    fn test_incremental_store_and_lookup() {
        let mut verifier = IncrementalVerifier::in_memory();
        verifier.store("m::f", sample_entry("h1"));

        let result = verifier.lookup("m::f", "h1", "");
        assert!(matches!(result, CacheLookup::Hit(_)));
    }

    #[test]
    fn test_incremental_lookup_miss() {
        let mut verifier = IncrementalVerifier::in_memory();
        let result = verifier.lookup("m::f", "h1", "");
        assert_eq!(result, CacheLookup::Miss);
    }

    // -- Invalidation --

    #[test]
    fn test_incremental_invalidation_simple() {
        let mut verifier = IncrementalVerifier::in_memory();
        verifier.add_dependency("caller", "callee");
        verifier.store("caller", sample_entry("h1"));
        verifier.store("callee", sample_entry("h2"));

        // Callee spec changes
        let to_reverify = verifier.update_after_change(&["callee".to_string()]);

        assert!(to_reverify.contains(&"callee".to_string()));
        assert!(to_reverify.contains(&"caller".to_string()));
        assert!(!verifier.is_fresh("caller"));
        assert!(!verifier.is_fresh("callee"));
        assert_eq!(verifier.generation(), 1);
    }

    #[test]
    fn test_incremental_invalidation_transitive() {
        let mut verifier = IncrementalVerifier::in_memory();
        verifier.add_dependency("A", "B");
        verifier.add_dependency("B", "C");
        verifier.store("A", sample_entry("hA"));
        verifier.store("B", sample_entry("hB"));
        verifier.store("C", sample_entry("hC"));

        let to_reverify = verifier.update_after_change(&["C".to_string()]);

        assert_eq!(to_reverify.len(), 3);
        assert!(!verifier.is_fresh("A"));
        assert!(!verifier.is_fresh("B"));
        assert!(!verifier.is_fresh("C"));
    }

    #[test]
    fn test_incremental_stale_blocks_lookup() {
        let mut verifier = IncrementalVerifier::in_memory();
        verifier.add_dependency("caller", "callee");
        verifier.store("caller", sample_entry("h1"));

        verifier.update_after_change(&["callee".to_string()]);

        // Even if we didn't remove the entry, stale should block lookup
        let result = verifier.lookup("caller", "h1", "");
        assert_eq!(result, CacheLookup::Miss);
    }

    #[test]
    fn test_incremental_re_store_clears_stale() {
        let mut verifier = IncrementalVerifier::in_memory();
        verifier.add_dependency("caller", "callee");
        verifier.store("caller", sample_entry("h1"));

        verifier.update_after_change(&["callee".to_string()]);
        assert!(!verifier.is_fresh("caller"));

        // Re-store after re-verification
        verifier.store("caller", sample_entry("h2"));
        assert!(verifier.is_fresh("caller"));

        let result = verifier.lookup("caller", "h2", "");
        assert!(matches!(result, CacheLookup::Hit(_)));
    }

    // -- Generation counter --

    #[test]
    fn test_incremental_generation_bumps() {
        let mut verifier = IncrementalVerifier::in_memory();
        assert_eq!(verifier.generation(), 0);

        verifier.update_after_change(&["f".to_string()]);
        assert_eq!(verifier.generation(), 1);

        verifier.update_after_change(&["g".to_string()]);
        assert_eq!(verifier.generation(), 2);
    }

    #[test]
    fn test_incremental_empty_change_no_bump() {
        let mut verifier = IncrementalVerifier::in_memory();
        let result = verifier.update_after_change(&[]);
        assert!(result.is_empty());
        assert_eq!(verifier.generation(), 0);
    }

    // -- Minimal invalidation --

    #[test]
    fn test_incremental_minimal_invalidation() {
        let mut verifier = IncrementalVerifier::in_memory();
        // A -> B, C is independent
        verifier.add_dependency("A", "B");
        verifier.store("A", sample_entry("hA"));
        verifier.store("B", sample_entry("hB"));
        verifier.store("C", sample_entry("hC"));

        let to_reverify = verifier.update_after_change(&["B".to_string()]);

        // Only A and B should be affected, not C
        assert!(to_reverify.contains(&"A".to_string()));
        assert!(to_reverify.contains(&"B".to_string()));
        assert!(!to_reverify.contains(&"C".to_string()));
        assert!(verifier.is_fresh("C"));
    }

    // -- Plan with reasons --

    #[test]
    fn test_incremental_plan_with_reasons() {
        let mut verifier = IncrementalVerifier::in_memory();
        verifier.add_dependency("A", "B");
        verifier.add_dependency("B", "C");

        let plan = verifier.update_after_change_with_plan(&["C".to_string()]);

        assert_eq!(plan.len(), 3);
        let reason = plan.reason_for("A").expect("should have reason for A");
        assert_eq!(reason.changed_root, "C");
    }

    // -- Summary --

    #[test]
    fn test_incremental_summary() {
        let mut verifier = IncrementalVerifier::in_memory();
        verifier.store("f", sample_entry("h"));
        verifier.update_after_change(&["f".to_string()]);

        let summary = verifier.summary();
        assert!(summary.contains("gen=1"));
        assert!(summary.contains("stale=1"));
    }

    // -- Stale functions accessor --

    #[test]
    fn test_incremental_stale_functions() {
        let mut verifier = IncrementalVerifier::in_memory();
        verifier.add_dependency("A", "B");
        verifier.update_after_change(&["B".to_string()]);

        let stale = verifier.stale_functions();
        assert!(stale.contains("A"));
        assert!(stale.contains("B"));
    }

    // -- Diamond pattern --

    #[test]
    fn test_incremental_diamond_no_duplicates() {
        let mut verifier = IncrementalVerifier::in_memory();
        verifier.add_dependency("A", "B");
        verifier.add_dependency("A", "C");
        verifier.add_dependency("B", "D");
        verifier.add_dependency("C", "D");

        let to_reverify = verifier.update_after_change(&["D".to_string()]);

        // Should have 4 unique entries, no duplicates
        let unique: FxHashSet<&String> = to_reverify.iter().collect();
        assert_eq!(unique.len(), 4);
        assert_eq!(to_reverify.len(), 4);
    }
}
