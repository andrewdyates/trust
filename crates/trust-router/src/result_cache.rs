// trust-router/result_cache.rs: Re-export from trust-cache
//
// tRust #527: The solver result cache implementation has been consolidated into
// trust-cache. This module re-exports all public types for backward
// compatibility so that existing consumers (solver_cache.rs, trust-driver)
// continue to compile without import changes.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#[allow(unused_imports)]
pub use trust_cache::result_cache::{
    CachePolicy, CacheStats, CachedResult, ReplayConfig, ResultCache, ResultCacheKey, hash_formula,
};
