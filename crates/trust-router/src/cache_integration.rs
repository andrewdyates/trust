// trust-router/cache_integration.rs: Cache-aware verification routing
//
// Wraps the Router with spec-aware cache invalidation so that when specs
// change, stale cached results are invalidated before verification begins.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_cache::spec_aware_cache::SpecAwareCacheManager;
use trust_cache::spec_change_detector::SpecFingerprint;
use trust_cache::{CacheLookup, compute_content_hash};
use trust_types::*;

use crate::Router;

/// A cache-aware router that checks the cache before dispatching to backends,
/// and invalidates stale entries when specs change.
///
/// Usage:
/// 1. Create with a Router and SpecAwareCacheManager
/// 2. Before each verification round, call `process_specs` with current fingerprints
/// 3. Call `verify_one_cached` or `verify_all_cached` to use the cache
/// 4. Results are automatically stored in the cache
pub struct CacheAwareRouter {
    router: Router,
    cache_manager: SpecAwareCacheManager,
}

impl CacheAwareRouter {
    /// Create a new cache-aware router.
    pub fn new(router: Router, cache_manager: SpecAwareCacheManager) -> Self {
        Self {
            router,
            cache_manager,
        }
    }

    /// Access the underlying router.
    #[must_use]
    pub fn router(&self) -> &Router {
        &self.router
    }

    /// Access the cache manager (immutable).
    #[must_use]
    pub fn cache_manager(&self) -> &SpecAwareCacheManager {
        &self.cache_manager
    }

    /// Access the cache manager (mutable).
    pub fn cache_manager_mut(&mut self) -> &mut SpecAwareCacheManager {
        &mut self.cache_manager
    }

    /// Process spec fingerprints for the current iteration.
    ///
    /// Detects spec changes and invalidates stale cache entries. Call this
    /// before verifying functions in each compilation round.
    pub fn process_specs(&mut self, fingerprints: &[SpecFingerprint]) {
        let _ = self.cache_manager.process_specs(fingerprints);
    }

    /// Register a dependency: `caller` depends on `callee`.
    pub fn add_dependency(&mut self, caller: &str, callee: &str) {
        self.cache_manager.add_dependency(caller, callee);
    }

    /// Verify a single function, using the cache when possible.
    ///
    /// Returns (result, was_cached):
    /// - If the cache has a valid entry, returns the cached verdict without calling backends
    /// - If the cache misses, dispatches to the router and stores the result
    pub fn verify_one_cached(
        &mut self,
        func: &VerifiableFunction,
        vcs: &[VerificationCondition],
    ) -> (FunctionVerdict, bool) {
        let content_hash = compute_content_hash(func);
        let spec_fp = SpecFingerprint::from_contracts(&func.def_path, &func.contracts);

        // Check cache with spec awareness
        let lookup = self.cache_manager.lookup_with_spec_check(
            &func.def_path,
            &content_hash,
            &spec_fp.hash,
        );

        if let CacheLookup::Hit(entry) = lookup {
            return (entry.verdict, true);
        }

        // Cache miss: verify via router
        let results = self.router.verify_all(vcs);

        // Compute aggregate verdict
        let mut total = results.len();
        let mut proved = 0;
        let mut failed = 0;
        let mut unknown = 0;

        for (_, result) in &results {
            match result {
                VerificationResult::Proved { .. } => proved += 1,
                VerificationResult::Failed { .. } => failed += 1,
                VerificationResult::Unknown { .. }
                | VerificationResult::Timeout { .. } => unknown += 1,
                // tRust #734: non-panicking fallback for #[non_exhaustive] forward compat
                _ => unknown += 1,
            }
        }

        if total == 0 {
            total = 1; // avoid storing zero-obligation entries
        }

        let verdict = if failed > 0 {
            FunctionVerdict::HasViolations
        } else if unknown > 0 {
            FunctionVerdict::Inconclusive
        } else {
            FunctionVerdict::Verified
        };

        // Store in cache
        self.cache_manager.cache_mut().store_function(
            func,
            verdict,
            total,
            proved,
            failed,
            unknown,
            0, // runtime_checked
        );

        (verdict, false)
    }

    /// Verify all functions, using the cache for unchanged functions.
    ///
    /// Returns a list of (def_path, verdict, was_cached) for each function.
    pub fn verify_all_cached(
        &mut self,
        functions: &[(VerifiableFunction, Vec<VerificationCondition>)],
    ) -> Vec<(String, FunctionVerdict, bool)> {
        functions
            .iter()
            .map(|(func, vcs)| {
                let (verdict, cached) = self.verify_one_cached(func, vcs);
                (func.def_path.clone(), verdict, cached)
            })
            .collect()
    }

    /// Cache statistics summary.
    #[must_use]
    pub fn summary(&self) -> String {
        self.cache_manager.summary()
    }

    /// Save the cache to disk.
    pub fn save(&self) -> Result<(), trust_cache::CacheError> {
        self.cache_manager.save()
    }
}

#[cfg(test)]
mod tests {
    use trust_cache::invalidation_strategy::InvalidationStrategy;
    use trust_cache::spec_aware_cache::SpecAwareCacheManager;
    use trust_cache::spec_change_detector::SpecFingerprint;
    use trust_types::*;

    use super::*;

    fn make_function(name: &str) -> VerifiableFunction {
        VerifiableFunction {
            name: name.to_string(),
            def_path: format!("crate::{name}"),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Return,
                }],
                arg_count: 0,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    fn make_function_with_contract(
        name: &str,
        contract_body: &str,
    ) -> VerifiableFunction {
        let mut func = make_function(name);
        func.contracts.push(Contract {
            kind: ContractKind::Ensures,
            span: SourceSpan::default(),
            body: contract_body.to_string(),
        });
        func
    }

    fn make_vc(func_name: &str) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: func_name.to_string(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
        }
    }

    // -----------------------------------------------------------------------
    // Basic cache-aware verification
    // -----------------------------------------------------------------------

    #[test]
    fn test_verify_one_cached_miss_then_hit() {
        let router = Router::new(); // mock backend
        let mgr = SpecAwareCacheManager::new();
        let mut car = CacheAwareRouter::new(router, mgr);

        let func = make_function("foo");
        let vcs = vec![make_vc("foo")];

        // First call: cache miss
        let (verdict1, cached1) = car.verify_one_cached(&func, &vcs);
        assert!(!cached1);
        assert!(matches!(
            verdict1,
            FunctionVerdict::Verified | FunctionVerdict::HasViolations | FunctionVerdict::Inconclusive
        ));

        // Second call: cache hit (same function)
        let (verdict2, cached2) = car.verify_one_cached(&func, &vcs);
        assert!(cached2);
        assert_eq!(verdict1, verdict2);
    }

    #[test]
    fn test_verify_one_cached_miss_on_body_change() {
        let router = Router::new();
        let mgr = SpecAwareCacheManager::new();
        let mut car = CacheAwareRouter::new(router, mgr);

        let func_v1 = make_function("bar");
        let vcs = vec![make_vc("bar")];

        // Cache the result
        let (_, cached1) = car.verify_one_cached(&func_v1, &vcs);
        assert!(!cached1);

        // Change the body
        let mut func_v2 = make_function("bar");
        func_v2.body.arg_count = 3;

        let (_, cached2) = car.verify_one_cached(&func_v2, &vcs);
        assert!(!cached2); // body changed -> miss
    }

    // -----------------------------------------------------------------------
    // Spec change invalidation through router
    // -----------------------------------------------------------------------

    #[test]
    fn test_spec_change_invalidates_cached_result() {
        let router = Router::new();
        let mgr = SpecAwareCacheManager::new();
        let mut car = CacheAwareRouter::new(router, mgr);

        let func_v1 = make_function_with_contract("baz", "result > 0");
        let vcs = vec![make_vc("baz")];

        // Cache the result
        let (_, cached1) = car.verify_one_cached(&func_v1, &vcs);
        assert!(!cached1);

        // Process specs for baseline
        let fps_v1 = vec![SpecFingerprint::from_contracts(
            &func_v1.def_path,
            &func_v1.contracts,
        )];
        car.process_specs(&fps_v1);

        // Change the spec
        let func_v2 = make_function_with_contract("baz", "result > 1");
        let fps_v2 = vec![SpecFingerprint::from_contracts(
            &func_v2.def_path,
            &func_v2.contracts,
        )];
        car.process_specs(&fps_v2);

        // Verify again: should be a miss because spec changed
        let (_, cached2) = car.verify_one_cached(&func_v2, &vcs);
        assert!(!cached2);
    }

    // -----------------------------------------------------------------------
    // Transitive invalidation through router
    // -----------------------------------------------------------------------

    #[test]
    fn test_transitive_invalidation_through_router() {
        let router = Router::new();
        let mgr = SpecAwareCacheManager::new();
        let mut car = CacheAwareRouter::new(router, mgr);

        // Setup: caller depends on callee
        car.add_dependency("crate::caller", "crate::callee");

        let caller = make_function("caller");
        let callee = make_function_with_contract("callee", "result > 0");
        let caller_vcs = vec![make_vc("caller")];
        let callee_vcs = vec![make_vc("callee")];

        // Cache both
        let (_, c1) = car.verify_one_cached(&callee, &callee_vcs);
        assert!(!c1);
        let (_, c2) = car.verify_one_cached(&caller, &caller_vcs);
        assert!(!c2);

        // Verify both are cached
        let (_, c3) = car.verify_one_cached(&callee, &callee_vcs);
        assert!(c3);
        let (_, c4) = car.verify_one_cached(&caller, &caller_vcs);
        assert!(c4);

        // Establish baseline fingerprints
        let fps_v1 = vec![
            SpecFingerprint::from_contracts(&caller.def_path, &caller.contracts),
            SpecFingerprint::from_contracts(&callee.def_path, &callee.contracts),
        ];
        car.process_specs(&fps_v1);

        // Change callee's spec
        let callee_v2 = make_function_with_contract("callee", "result > 1");
        let fps_v2 = vec![
            SpecFingerprint::from_contracts(&caller.def_path, &caller.contracts),
            SpecFingerprint::from_contracts(&callee_v2.def_path, &callee_v2.contracts),
        ];
        car.process_specs(&fps_v2);

        // Both should be cache misses now
        let (_, c5) = car.verify_one_cached(&callee_v2, &callee_vcs);
        assert!(!c5, "callee should be invalidated");
        let (_, c6) = car.verify_one_cached(&caller, &caller_vcs);
        assert!(!c6, "caller should be invalidated transitively");
    }

    // -----------------------------------------------------------------------
    // verify_all_cached
    // -----------------------------------------------------------------------

    #[test]
    fn test_verify_all_cached() {
        let router = Router::new();
        let mgr = SpecAwareCacheManager::new();
        let mut car = CacheAwareRouter::new(router, mgr);

        let f1 = make_function("f1");
        let f2 = make_function("f2");
        let vcs1 = vec![make_vc("f1")];
        let vcs2 = vec![make_vc("f2")];

        let results = car.verify_all_cached(&[
            (f1.clone(), vcs1.clone()),
            (f2.clone(), vcs2.clone()),
        ]);
        assert_eq!(results.len(), 2);
        // All should be misses
        assert!(!results[0].2);
        assert!(!results[1].2);

        // Second pass: all cached
        let results2 = car.verify_all_cached(&[
            (f1, vcs1),
            (f2, vcs2),
        ]);
        assert!(results2[0].2);
        assert!(results2[1].2);
    }

    // -----------------------------------------------------------------------
    // Strategy configuration
    // -----------------------------------------------------------------------

    #[test]
    fn test_selective_strategy_no_transitive() {
        let router = Router::new();
        let mut mgr = SpecAwareCacheManager::new();
        mgr.set_strategy(InvalidationStrategy::Selective);
        let mut car = CacheAwareRouter::new(router, mgr);

        car.add_dependency("crate::caller", "crate::callee");

        let caller = make_function("caller");
        let callee = make_function_with_contract("callee", "result > 0");
        let caller_vcs = vec![make_vc("caller")];
        let callee_vcs = vec![make_vc("callee")];

        // Cache both
        car.verify_one_cached(&callee, &callee_vcs);
        car.verify_one_cached(&caller, &caller_vcs);

        // Establish baseline
        let fps_v1 = vec![
            SpecFingerprint::from_contracts(&caller.def_path, &caller.contracts),
            SpecFingerprint::from_contracts(&callee.def_path, &callee.contracts),
        ];
        car.process_specs(&fps_v1);

        // Change callee's spec
        let callee_v2 = make_function_with_contract("callee", "result > 1");
        let fps_v2 = vec![
            SpecFingerprint::from_contracts(&caller.def_path, &caller.contracts),
            SpecFingerprint::from_contracts(&callee_v2.def_path, &callee_v2.contracts),
        ];
        car.process_specs(&fps_v2);

        // Callee should be miss, but caller should STILL be cached (selective)
        let (_, c_callee) = car.verify_one_cached(&callee_v2, &callee_vcs);
        assert!(!c_callee, "callee should be invalidated");
        let (_, c_caller) = car.verify_one_cached(&caller, &caller_vcs);
        assert!(c_caller, "caller should still be cached with selective strategy");
    }

    // -----------------------------------------------------------------------
    // Summary
    // -----------------------------------------------------------------------

    #[test]
    fn test_summary() {
        let router = Router::new();
        let mgr = SpecAwareCacheManager::new();
        let car = CacheAwareRouter::new(router, mgr);
        let s = car.summary();
        assert!(s.contains("cache:"));
    }
}
