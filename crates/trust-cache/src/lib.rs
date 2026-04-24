//! trust-cache: Incremental verification cache for tRust
//!
//! Caches verification results keyed by function body hash so that unchanged
//! functions are not re-verified on subsequent compilations. Also provides:
//! - Solver query caching (query_cache.rs) — KLEE-inspired exact-match cache
//! - Constraint independence splitting (independence.rs) — variable-based splitting
//! - Subsumption-based proof caching (query_cache.rs) — stronger proofs subsume weaker
//!
//! Author: Andrew Yates <andrew@andrewdyates.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

// tRust: Allow std HashMap/HashSet — FxHash lint only applies to compiler internals
#![allow(rustc::default_hash_types, rustc::potential_query_instability)]

use trust_types::fx::FxHashSet;

pub mod alpha_normalize;
// tRust #884: File-based cache coordination for concurrent compilations.
pub mod coordination;
pub(crate) mod independence;
// tRust #725: HMAC-SHA256 integrity protection for cache files on disk.
pub(crate) mod integrity;
// tRust #479: MIR structural hashing and per-function incremental cache.
pub(crate) mod invalidation;
pub mod invalidation_strategy;
pub(crate) mod mir_hash;
pub mod proof_replay;
pub(crate) mod query_cache;
// tRust #527: Solver result caching consolidated from trust-router.
pub mod result_cache;
pub mod spec_aware_cache;
pub mod spec_change_detector;
pub(crate) mod sub_query_splitter;
// tRust #666: Property-based idempotency and serialization roundtrip tests.
#[cfg(test)]
mod proptest_roundtrip;

// tRust #884: Re-export cache coordination types.
pub use coordination::{
    CacheLockGuard, CoordinationConfig, CoordinationError, acquire_exclusive_lock,
    acquire_shared_lock, coordinated_read, coordinated_write, file_content_hash,
    try_exclusive_lock, try_shared_lock, validate_content_hash,
};

// Re-export key types from independence and query_cache for convenience.
pub use alpha_normalize::{SubFormulaCache, alpha_normalize, alpha_normalized_hash};
pub use independence::{
    ConstraintIndependence, free_variables, partition_constraints, simplify_query,
};
pub use query_cache::{CacheKey, CacheStats, QueryCache, SubsumptionCache, is_subsumed};
pub use sub_query_splitter::{
    IndependenceAnalysis, SplitResult, SplitterConfig, SplitterStats, SubQuery, SubQuerySplitter,
    analyze_independence, sub_query_hash,
};
// tRust #527: Re-export solver result cache types.
pub use result_cache::{
    CachePolicy, CacheStats as ResultCacheStats, CachedResult, ReplayConfig as ResultReplayConfig,
    ResultCache, ResultCacheKey, hash_formula,
};
// tRust #479: Re-export MIR hash incremental types.
pub use mir_hash::{
    DependencyGraph, IncrementalCache, MirHash, MirHashCacheError, VerificationResult,
    compute_mir_hash,
};

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

use serde::{Deserialize, Serialize};
use thiserror::Error;
use trust_types::{FunctionVerdict, TransportObligationResult, VerifiableFunction};

/// Current cache schema version. Bump when CacheEntry format changes.
/// v2: Added spec_hash field. v3: Added HMAC integrity protection (#725).
/// v4: Persisted per-obligation transport results for stable cached reporting.
const CACHE_VERSION: u32 = 4;

/// Errors from cache operations.
#[derive(Debug, Error)]
pub enum CacheError {
    #[error("cache I/O error: {0}")]
    Io(#[from] std::io::Error),
    #[error("cache deserialization error: {0}")]
    Deserialize(#[from] serde_json::Error),
}

/// Compute a SHA-256 content hash of a function's body, contracts, and spec.
///
/// This is the cache key: if the hash matches a stored entry, the function
/// has not changed and verification can be skipped.
///
/// Delegates to [`VerifiableFunction::content_hash()`] to ensure a single
/// source of truth. The two must always agree.
#[must_use]
pub fn compute_content_hash(func: &VerifiableFunction) -> String {
    func.content_hash()
}

/// A single cached entry for one function.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct CacheEntry {
    /// The SHA-256 content hash of the function body + contracts at verification time.
    pub content_hash: String,
    /// The verification verdict.
    pub verdict: FunctionVerdict,
    /// Number of obligations that were checked.
    pub total_obligations: usize,
    /// Number proved.
    pub proved: usize,
    /// Number failed.
    pub failed: usize,
    /// Number unknown.
    pub unknown: usize,
    /// Number runtime-checked.
    #[serde(default)]
    pub runtime_checked: usize,
    /// Unix timestamp (seconds since epoch) when this entry was cached.
    #[serde(default)]
    pub cached_at: u64,
    /// SHA-256 fingerprint of the function's spec clauses (requires/ensures/invariants).
    ///
    /// Used for cross-session spec change detection: if this hash differs from the
    /// current spec fingerprint, the cached result is stale even if the body hash
    /// matches. Absent (empty) for entries created before spec tracking was added.
    #[serde(default)]
    pub spec_hash: String,
    /// Cached per-obligation transport results for stable human/json reporting on cache hits.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub obligation_results: Vec<TransportObligationResult>,
}

/// On-disk cache format.
#[derive(Debug, Clone, Serialize, Deserialize)]
struct CacheFile {
    /// Schema version for forward compatibility.
    version: u32,
    /// Map from function def_path to cached entry.
    entries: BTreeMap<String, CacheEntry>,
    /// HMAC-SHA256 tag over the serialized entries, hex-encoded.
    /// Computed using a key derived from the tRust executable hash + machine hostname.
    /// Empty string for in-memory caches or legacy files. See #725.
    #[serde(default)]
    hmac: String,
}

impl Default for CacheFile {
    fn default() -> Self {
        CacheFile { version: CACHE_VERSION, entries: BTreeMap::new(), hmac: String::new() }
    }
}

/// Result of a cache lookup.
#[derive(Debug, Clone, PartialEq)]
pub enum CacheLookup {
    /// Cache hit: the function body has not changed since last verification.
    Hit(CacheEntry),
    /// Cache miss: the function is new or its body changed.
    Miss,
}

/// Incremental verification cache.
///
/// Stores verification results keyed by function def_path and content hash.
/// When a function's content hash matches the cached entry, verification can
/// be skipped.
///
/// Supports coordinated access for concurrent compilations (#884):
/// use [`VerificationCache::load_coordinated`] and [`VerificationCache::save_coordinated`]
/// for file-locking and content-hash validation. The original [`load`] and [`save`]
/// methods remain available for single-process use or backward compatibility.
pub struct VerificationCache {
    path: PathBuf,
    data: CacheFile,
    hits: usize,
    misses: usize,
    /// SHA-256 hash of the cache file contents at load time.
    /// Used for content-hash-based invalidation in coordinated mode.
    /// Empty if the cache was created in-memory or loaded without coordination.
    content_hash_at_load: String,
}

impl VerificationCache {
    /// Load or create a cache at the given path.
    ///
    /// Verifies the HMAC-SHA256 tag on load. If the tag is missing, invalid,
    /// or does not match, the cache is discarded and a fresh one is created.
    /// This prevents accepting tampered cache files. See #725.
    pub fn load(path: impl AsRef<Path>) -> Result<Self, CacheError> {
        let path = path.as_ref().to_path_buf();
        let data = if path.exists() {
            let contents = std::fs::read_to_string(&path)?;
            match serde_json::from_str::<CacheFile>(&contents) {
                Ok(cf) if cf.version == CACHE_VERSION => {
                    // Verify HMAC integrity (#725).
                    let entries_json = serde_json::to_string(&cf.entries).unwrap_or_default();
                    let key = integrity::derive_cache_key();
                    if cf.hmac.is_empty()
                        || !integrity::verify_hmac(&key, entries_json.as_bytes(), &cf.hmac)
                    {
                        // HMAC missing or invalid: start fresh.
                        CacheFile::default()
                    } else {
                        cf
                    }
                }
                // Version mismatch or corrupt: start fresh
                _ => CacheFile::default(),
            }
        } else {
            CacheFile::default()
        };
        Ok(VerificationCache {
            path,
            data,
            hits: 0,
            misses: 0,
            content_hash_at_load: String::new(),
        })
    }

    /// Create an empty in-memory cache (no file backing).
    pub fn in_memory() -> Self {
        VerificationCache {
            path: PathBuf::new(),
            data: CacheFile::default(),
            hits: 0,
            misses: 0,
            content_hash_at_load: String::new(),
        }
    }

    /// Load or create a cache at the given path with file locking (#884).
    ///
    /// Acquires a shared (read) lock on the cache file before reading.
    /// The lock is released after loading. Records the content hash at
    /// load time for use by [`save_coordinated`].
    ///
    /// If the file does not exist, returns an empty cache (no lock needed).
    pub fn load_coordinated(
        path: impl AsRef<Path>,
        config: &coordination::CoordinationConfig,
    ) -> Result<Self, CacheError> {
        let path = path.as_ref().to_path_buf();
        if !path.exists() {
            return Ok(VerificationCache {
                path,
                data: CacheFile::default(),
                hits: 0,
                misses: 0,
                content_hash_at_load: String::new(),
            });
        }

        let (contents, content_hash, _guard) = coordination::coordinated_read(&path, config)
            .map_err(|e| CacheError::Io(std::io::Error::other(e.to_string())))?;
        // _guard is dropped here, releasing the shared lock.

        let data = match serde_json::from_str::<CacheFile>(&contents) {
            Ok(cf) if cf.version == CACHE_VERSION => {
                let entries_json = serde_json::to_string(&cf.entries).unwrap_or_default();
                let key = integrity::derive_cache_key();
                if cf.hmac.is_empty()
                    || !integrity::verify_hmac(&key, entries_json.as_bytes(), &cf.hmac)
                {
                    CacheFile::default()
                } else {
                    cf
                }
            }
            _ => CacheFile::default(),
        };

        Ok(VerificationCache { path, data, hits: 0, misses: 0, content_hash_at_load: content_hash })
    }

    /// Write the cache to disk with file locking and content-hash validation (#884).
    ///
    /// Acquires an exclusive (write) lock before writing. If `validate` is true
    /// and the cache was loaded with [`load_coordinated`], verifies that the
    /// file has not been modified by another process since load time. If another
    /// process wrote to the cache, returns an error (the caller should reload).
    ///
    /// Uses atomic write (write to temp, then rename) to prevent readers from
    /// seeing partial data.
    pub fn save_coordinated(
        &self,
        config: &coordination::CoordinationConfig,
    ) -> Result<(), CacheError> {
        if self.path.as_os_str().is_empty() {
            return Ok(()); // in-memory cache
        }
        if let Some(parent) = self.path.parent() {
            std::fs::create_dir_all(parent)?;
        }

        // Validate content hash if enabled and we have a prior hash
        if config.validate_content_hash && !self.content_hash_at_load.is_empty() {
            coordination::validate_content_hash(&self.path, &self.content_hash_at_load)
                .map_err(|e| CacheError::Io(std::io::Error::other(e.to_string())))?;
        }

        // Serialize with HMAC
        let entries_json = serde_json::to_string(&self.data.entries)?;
        let key = integrity::derive_cache_key();
        let tag = integrity::compute_hmac(&key, entries_json.as_bytes());

        let file =
            CacheFile { version: CACHE_VERSION, entries: self.data.entries.clone(), hmac: tag };
        let json = serde_json::to_string_pretty(&file)?;

        // Write with exclusive lock and atomic rename
        coordination::coordinated_write(&self.path, &json, config)
            .map_err(|e| CacheError::Io(std::io::Error::other(e.to_string())))?;
        Ok(())
    }

    /// The content hash of the cache file at load time.
    ///
    /// Empty if loaded without coordination or created in-memory.
    #[must_use]
    pub fn content_hash_at_load(&self) -> &str {
        &self.content_hash_at_load
    }

    /// Look up a function by def_path, content hash, and spec hash.
    ///
    /// A cache hit requires both the content hash AND spec hash to match.
    /// This prevents returning stale "proved" verdicts when a spec changes
    /// but the function body stays the same (e.g., strengthened postcondition).
    /// See #690.
    pub fn lookup(&mut self, def_path: &str, content_hash: &str, spec_hash: &str) -> CacheLookup {
        match self.data.entries.get(def_path) {
            Some(entry)
                if entry.content_hash == content_hash
                    && (entry.spec_hash.is_empty() || entry.spec_hash == spec_hash) =>
            {
                self.hits += 1;
                CacheLookup::Hit(entry.clone())
            }
            _ => {
                self.misses += 1;
                CacheLookup::Miss
            }
        }
    }

    /// Look up a function using its VerifiableFunction directly.
    ///
    /// Computes the SHA-256 content hash and spec fingerprint, then checks
    /// the cache. Both must match for a hit. This is the primary entry point
    /// for the trust_verify MIR pass.
    pub fn lookup_function(&mut self, func: &VerifiableFunction) -> CacheLookup {
        let hash = compute_content_hash(func);
        let spec_fp = crate::spec_change_detector::SpecFingerprint::from_contracts(
            &func.def_path,
            &func.contracts,
        );
        self.lookup(&func.def_path, &hash, &spec_fp.hash)
    }

    fn entries_equivalent(existing: &CacheEntry, new_entry: &CacheEntry) -> bool {
        existing.content_hash == new_entry.content_hash
            && existing.verdict == new_entry.verdict
            && existing.total_obligations == new_entry.total_obligations
            && existing.proved == new_entry.proved
            && existing.failed == new_entry.failed
            && existing.unknown == new_entry.unknown
            && existing.runtime_checked == new_entry.runtime_checked
            && existing.spec_hash == new_entry.spec_hash
    }

    /// Store a verification result for a function.
    ///
    /// Returns `true` when the cache contents changed and `false` when the new
    /// entry is semantically identical to the existing one.
    pub fn store(&mut self, def_path: &str, entry: CacheEntry) -> bool {
        if self
            .data
            .entries
            .get(def_path)
            .is_some_and(|existing| Self::entries_equivalent(existing, &entry))
        {
            return false;
        }

        self.data.entries.insert(def_path.to_string(), entry);
        true
    }

    /// Store a verification result computed from a VerifiableFunction.
    ///
    /// Builds a CacheEntry with the SHA-256 content hash and current timestamp.
    /// The spec_hash is computed from the function's contracts for cross-session
    /// spec change detection. Returns `true` when the cached entry changed.
    #[allow(clippy::too_many_arguments)]
    pub fn store_function(
        &mut self,
        func: &VerifiableFunction,
        verdict: FunctionVerdict,
        total_obligations: usize,
        proved: usize,
        failed: usize,
        unknown: usize,
        runtime_checked: usize,
    ) -> bool {
        let spec_fp = crate::spec_change_detector::SpecFingerprint::from_contracts(
            &func.def_path,
            &func.contracts,
        );
        let entry = CacheEntry {
            content_hash: compute_content_hash(func),
            verdict,
            total_obligations,
            proved,
            failed,
            unknown,
            runtime_checked,
            cached_at: now_unix_secs(),
            spec_hash: spec_fp.hash,
            obligation_results: vec![],
        };
        self.store(&func.def_path, entry)
    }

    /// Remove a cached entry (e.g., when a callee spec changes).
    pub fn invalidate(&mut self, def_path: &str) -> bool {
        self.data.entries.remove(def_path).is_some()
    }

    /// Remove all cached entries.
    pub fn invalidate_all(&mut self) {
        self.data.entries.clear();
    }

    /// Remove all entries whose def_path does not appear in the provided set.
    /// This is useful for garbage-collecting entries for deleted functions.
    pub fn retain_only(&mut self, active_def_paths: &[&str]) {
        let active: FxHashSet<&str> = active_def_paths.iter().copied().collect();
        self.data.entries.retain(|key, _| active.contains(key.as_str()));
    }

    /// Write the cache to disk with HMAC integrity protection.
    ///
    /// The HMAC is computed over the serialized entries (without the hmac field
    /// itself) using a key derived from the tRust executable + machine hostname.
    /// See #725.
    pub fn save(&self) -> Result<(), CacheError> {
        if self.path.as_os_str().is_empty() {
            return Ok(()); // in-memory cache, nothing to persist
        }
        if let Some(parent) = self.path.parent() {
            std::fs::create_dir_all(parent)?;
        }
        // Serialize entries alone for HMAC input (excludes the hmac field itself
        // to avoid circular dependency).
        let entries_json = serde_json::to_string(&self.data.entries)?;
        let key = integrity::derive_cache_key();
        let tag = integrity::compute_hmac(&key, entries_json.as_bytes());

        // Build the on-disk structure with the computed HMAC.
        let file =
            CacheFile { version: CACHE_VERSION, entries: self.data.entries.clone(), hmac: tag };
        let json = serde_json::to_string_pretty(&file)?;
        std::fs::write(&self.path, json)?;
        Ok(())
    }

    /// Number of cache hits during this session.
    pub fn hits(&self) -> usize {
        self.hits
    }

    /// Number of cache misses during this session.
    pub fn misses(&self) -> usize {
        self.misses
    }

    /// Total number of cached entries.
    pub fn len(&self) -> usize {
        self.data.entries.len()
    }

    /// Whether the cache is empty.
    pub fn is_empty(&self) -> bool {
        self.data.entries.is_empty()
    }

    /// Summary string for diagnostics (e.g., "3 hits, 2 misses, 5 cached").
    #[must_use]
    pub fn summary(&self) -> String {
        format!("{} hits, {} misses, {} cached", self.hits, self.misses, self.data.entries.len())
    }
}

/// Current Unix timestamp in seconds.
fn now_unix_secs() -> u64 {
    SystemTime::now().duration_since(UNIX_EPOCH).map(|d| d.as_secs()).unwrap_or(0)
}

#[cfg(test)]
mod tests {
    use trust_types::{
        BasicBlock, BlockId, Contract, ContractKind, FunctionVerdict, SourceSpan, Terminator, Ty,
        VerifiableBody, VerifiableFunction,
    };

    use super::*;

    fn sample_entry(hash: &str, verdict: FunctionVerdict) -> CacheEntry {
        CacheEntry {
            content_hash: hash.to_string(),
            verdict,
            total_obligations: 3,
            proved: 2,
            failed: 0,
            unknown: 1,
            runtime_checked: 0,
            cached_at: 0,
            spec_hash: String::new(),
            obligation_results: vec![],
        }
    }

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

    fn make_function_with_contract(name: &str, contract_desc: &str) -> VerifiableFunction {
        let mut func = make_function(name);
        func.contracts.push(Contract {
            kind: ContractKind::Ensures,
            span: SourceSpan::default(),
            body: contract_desc.to_string(),
        });
        func
    }

    // -----------------------------------------------------------------------
    // SHA-256 content hashing tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_content_hash_deterministic() {
        let func = make_function("foo");
        let h1 = compute_content_hash(&func);
        let h2 = compute_content_hash(&func);
        assert_eq!(h1, h2, "content hash must be deterministic");
    }

    #[test]
    fn test_content_hash_is_sha256_hex() {
        let func = make_function("foo");
        let hash = compute_content_hash(&func);
        // SHA-256 hex is 64 characters
        assert_eq!(hash.len(), 64, "SHA-256 hex digest is 64 chars, got {}", hash.len());
        assert!(hash.chars().all(|c| c.is_ascii_hexdigit()), "must be valid hex");
    }

    #[test]
    fn test_content_hash_ignores_name() {
        let f1 = make_function("foo");
        let f2 = make_function("bar");
        assert_eq!(
            compute_content_hash(&f1),
            compute_content_hash(&f2),
            "content hash depends on body+contracts, not name — cache keys by def_path separately"
        );
    }

    #[test]
    fn test_content_hash_changes_with_contracts() {
        let f1 = make_function("foo");
        let f2 = make_function_with_contract("foo", "result > 0");
        assert_ne!(
            compute_content_hash(&f1),
            compute_content_hash(&f2),
            "adding a contract must change the hash"
        );
    }

    #[test]
    fn test_content_hash_changes_with_body() {
        let f1 = make_function("foo");
        let mut f2 = make_function("foo");
        f2.body.arg_count = 3;
        assert_ne!(
            compute_content_hash(&f1),
            compute_content_hash(&f2),
            "changing body must change the hash"
        );
    }

    // -----------------------------------------------------------------------
    // Cache hit/miss tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_cache_hit_and_miss() {
        let mut cache = VerificationCache::in_memory();
        cache.store("mymod::foo", sample_entry("abc123", FunctionVerdict::Verified));

        assert_eq!(
            cache.lookup("mymod::foo", "abc123", ""),
            CacheLookup::Hit(sample_entry("abc123", FunctionVerdict::Verified))
        );
        assert_eq!(cache.lookup("mymod::foo", "different_hash", ""), CacheLookup::Miss);
        assert_eq!(cache.lookup("mymod::bar", "abc123", ""), CacheLookup::Miss);

        assert_eq!(cache.hits(), 1);
        assert_eq!(cache.misses(), 2);
    }

    #[test]
    fn test_cache_invalidate() {
        let mut cache = VerificationCache::in_memory();
        cache.store("mymod::foo", sample_entry("abc123", FunctionVerdict::Verified));
        assert!(cache.invalidate("mymod::foo"));
        assert!(!cache.invalidate("mymod::foo")); // already removed
        assert_eq!(cache.lookup("mymod::foo", "abc123", ""), CacheLookup::Miss);
    }

    #[test]
    fn test_cache_invalidate_all() {
        let mut cache = VerificationCache::in_memory();
        cache.store("a::f", sample_entry("h1", FunctionVerdict::Verified));
        cache.store("b::g", sample_entry("h2", FunctionVerdict::HasViolations));
        cache.store("c::h", sample_entry("h3", FunctionVerdict::Inconclusive));
        assert_eq!(cache.len(), 3);

        cache.invalidate_all();
        assert!(cache.is_empty());
        assert_eq!(cache.len(), 0);
    }

    #[test]
    fn test_cache_retain_only() {
        let mut cache = VerificationCache::in_memory();
        cache.store("a::f", sample_entry("h1", FunctionVerdict::Verified));
        cache.store("b::g", sample_entry("h2", FunctionVerdict::HasViolations));
        cache.store("c::h", sample_entry("h3", FunctionVerdict::Inconclusive));

        cache.retain_only(&["a::f", "c::h"]);
        assert_eq!(cache.len(), 2);
        assert_eq!(cache.lookup("b::g", "h2", ""), CacheLookup::Miss);
    }

    #[test]
    fn test_cache_overwrite() {
        let mut cache = VerificationCache::in_memory();
        cache.store("m::f", sample_entry("old", FunctionVerdict::Inconclusive));
        cache.store("m::f", sample_entry("new", FunctionVerdict::Verified));

        assert_eq!(
            cache.lookup("m::f", "new", ""),
            CacheLookup::Hit(sample_entry("new", FunctionVerdict::Verified))
        );
        assert_eq!(cache.lookup("m::f", "old", ""), CacheLookup::Miss);
    }

    // -----------------------------------------------------------------------
    // VerifiableFunction convenience methods
    // -----------------------------------------------------------------------

    #[test]
    fn test_lookup_function_hit() {
        let func = make_function("foo");
        let mut cache = VerificationCache::in_memory();
        // Use store_function to ensure spec_hash matches lookup_function's computation.
        cache.store_function(&func, FunctionVerdict::Verified, 2, 2, 0, 0, 0);

        let result = cache.lookup_function(&func);
        assert!(matches!(result, CacheLookup::Hit(_)));
        assert_eq!(cache.hits(), 1);
    }

    #[test]
    fn test_lookup_function_miss_on_change() {
        let func = make_function("foo");
        let mut cache = VerificationCache::in_memory();
        // Store with old hash
        cache.store(&func.def_path, sample_entry("stale_hash", FunctionVerdict::Verified));

        // Lookup with current function (different hash)
        let result = cache.lookup_function(&func);
        assert_eq!(result, CacheLookup::Miss);
        assert_eq!(cache.misses(), 1);
    }

    #[test]
    fn test_store_function_roundtrip() {
        let func = make_function("bar");
        let mut cache = VerificationCache::in_memory();
        cache.store_function(&func, FunctionVerdict::Verified, 5, 4, 0, 1, 0);

        let result = cache.lookup_function(&func);
        match result {
            CacheLookup::Hit(entry) => {
                assert_eq!(entry.verdict, FunctionVerdict::Verified);
                assert_eq!(entry.total_obligations, 5);
                assert_eq!(entry.proved, 4);
                assert_eq!(entry.unknown, 1);
                assert!(entry.cached_at > 0, "timestamp should be set");
            }
            CacheLookup::Miss => panic!("expected cache hit after store_function"),
        }
    }

    #[test]
    fn test_store_function_is_noop_when_entry_is_unchanged() {
        let func = make_function("bar");
        let mut cache = VerificationCache::in_memory();

        assert!(cache.store_function(&func, FunctionVerdict::Verified, 5, 4, 0, 1, 0));

        let cached_at = match cache.lookup_function(&func) {
            CacheLookup::Hit(entry) => entry.cached_at,
            CacheLookup::Miss => panic!("expected cache hit after initial store_function"),
        };

        assert!(
            !cache.store_function(&func, FunctionVerdict::Verified, 5, 4, 0, 1, 0),
            "identical store_function call should be a no-op"
        );

        match cache.lookup_function(&func) {
            CacheLookup::Hit(entry) => {
                assert_eq!(entry.cached_at, cached_at, "no-op store should preserve timestamp");
            }
            CacheLookup::Miss => panic!("expected cache hit after no-op store_function"),
        }
    }

    #[test]
    fn test_store_function_detects_body_change() {
        let func_v1 = make_function("baz");
        let mut cache = VerificationCache::in_memory();
        cache.store_function(&func_v1, FunctionVerdict::Verified, 1, 1, 0, 0, 0);

        // Modify the function body
        let mut func_v2 = make_function("baz");
        func_v2.body.arg_count = 2;

        // Lookup with modified function should miss
        let result = cache.lookup_function(&func_v2);
        assert_eq!(result, CacheLookup::Miss);
    }

    // -----------------------------------------------------------------------
    // Persistence tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_cache_persistence_roundtrip() {
        let dir = tempfile::tempdir().expect("create tempdir");
        let cache_path = dir.path().join("trust-cache.json");

        // Write
        {
            let mut cache = VerificationCache::load(&cache_path).expect("create cache");
            cache.store("m::f", sample_entry("hash1", FunctionVerdict::Verified));
            cache.store("m::g", sample_entry("hash2", FunctionVerdict::HasViolations));
            cache.save().expect("save cache");
        }

        // Read back
        {
            let mut cache = VerificationCache::load(&cache_path).expect("load cache");
            assert_eq!(cache.len(), 2);
            assert_eq!(
                cache.lookup("m::f", "hash1", ""),
                CacheLookup::Hit(sample_entry("hash1", FunctionVerdict::Verified))
            );
            assert_eq!(
                cache.lookup("m::g", "hash2", ""),
                CacheLookup::Hit(sample_entry("hash2", FunctionVerdict::HasViolations))
            );
        }
    }

    #[test]
    fn test_cache_persistence_with_timestamp() {
        let dir = tempfile::tempdir().expect("create tempdir");
        let cache_path = dir.path().join("trust-cache.json");

        let func = make_function("stamped");
        {
            let mut cache = VerificationCache::load(&cache_path).expect("create cache");
            cache.store_function(&func, FunctionVerdict::Verified, 2, 2, 0, 0, 0);
            cache.save().expect("save cache");
        }

        // Read back and verify timestamp survived
        {
            let mut cache = VerificationCache::load(&cache_path).expect("load cache");
            match cache.lookup_function(&func) {
                CacheLookup::Hit(entry) => {
                    assert!(entry.cached_at > 0, "timestamp should survive persistence");
                }
                CacheLookup::Miss => panic!("expected hit after persistence roundtrip"),
            }
        }
    }

    #[test]
    fn test_cache_handles_corrupt_file() {
        let dir = tempfile::tempdir().expect("create tempdir");
        let cache_path = dir.path().join("trust-cache.json");
        std::fs::write(&cache_path, "not valid json{{{").expect("write corrupt file");

        let cache = VerificationCache::load(&cache_path).expect("should not fail on corrupt");
        assert!(cache.is_empty(), "corrupt cache should start fresh");
    }

    #[test]
    fn test_cache_handles_version_mismatch() {
        let dir = tempfile::tempdir().expect("create tempdir");
        let cache_path = dir.path().join("trust-cache.json");
        std::fs::write(&cache_path, r#"{"version": 999, "entries": {}}"#)
            .expect("write future version");

        let cache =
            VerificationCache::load(&cache_path).expect("should not fail on version mismatch");
        assert!(cache.is_empty(), "version mismatch should start fresh");
    }

    #[test]
    fn test_cache_handles_old_version() {
        let dir = tempfile::tempdir().expect("create tempdir");
        let cache_path = dir.path().join("trust-cache.json");
        // Old version 1 cache should be discarded
        std::fs::write(&cache_path, r#"{"version": 1, "entries": {}}"#).expect("write old version");

        let cache = VerificationCache::load(&cache_path).expect("should not fail on old version");
        assert!(cache.is_empty(), "old version cache should start fresh");
    }

    #[test]
    fn test_cache_len_and_is_empty() {
        let mut cache = VerificationCache::in_memory();
        assert!(cache.is_empty());
        assert_eq!(cache.len(), 0);

        cache.store("m::f", sample_entry("h", FunctionVerdict::Verified));
        assert!(!cache.is_empty());
        assert_eq!(cache.len(), 1);
    }

    #[test]
    fn test_cache_save_creates_parent_dirs() {
        let dir = tempfile::tempdir().expect("create tempdir");
        let cache_path = dir.path().join("nested").join("deep").join("trust-cache.json");

        let mut cache = VerificationCache::load(&cache_path).expect("create cache");
        cache.store("m::f", sample_entry("h", FunctionVerdict::Verified));
        cache.save().expect("save should create parent dirs");
        assert!(cache_path.exists());
    }

    #[test]
    fn test_in_memory_cache_save_is_noop() {
        let cache = VerificationCache::in_memory();
        cache.save().expect("in-memory save should be no-op");
    }

    // -----------------------------------------------------------------------
    // Summary and statistics
    // -----------------------------------------------------------------------

    #[test]
    fn test_cache_summary() {
        let mut cache = VerificationCache::in_memory();
        cache.store("a::f", sample_entry("h1", FunctionVerdict::Verified));
        cache.store("b::g", sample_entry("h2", FunctionVerdict::Verified));
        cache.lookup("a::f", "h1", ""); // hit
        cache.lookup("c::h", "h3", ""); // miss

        let summary = cache.summary();
        assert_eq!(summary, "1 hits, 1 misses, 2 cached");
    }

    #[test]
    fn test_invalidate_all_then_store() {
        let mut cache = VerificationCache::in_memory();
        cache.store("a::f", sample_entry("h1", FunctionVerdict::Verified));
        cache.store("b::g", sample_entry("h2", FunctionVerdict::Verified));
        cache.invalidate_all();

        // Can store again after invalidation
        cache.store("c::h", sample_entry("h3", FunctionVerdict::Inconclusive));
        assert_eq!(cache.len(), 1);
        assert_eq!(
            cache.lookup("c::h", "h3", ""),
            CacheLookup::Hit(sample_entry("h3", FunctionVerdict::Inconclusive))
        );
    }

    // -----------------------------------------------------------------------
    // Regression tests for #372 and #368
    // -----------------------------------------------------------------------

    /// Regression test for #372: compute_content_hash() must agree with
    /// VerifiableFunction::content_hash().
    #[test]
    fn test_compute_content_hash_matches_method() {
        let func = make_function("foo");
        assert_eq!(
            compute_content_hash(&func),
            func.content_hash(),
            "compute_content_hash() must delegate to VerifiableFunction::content_hash()"
        );
    }

    /// Regression test for #372: both hash functions must agree even with
    /// contracts present.
    #[test]
    fn test_compute_content_hash_matches_method_with_contracts() {
        let func = make_function_with_contract("bar", "result > 0");
        assert_eq!(
            compute_content_hash(&func),
            func.content_hash(),
            "compute_content_hash() must match content_hash() with contracts"
        );
    }

    /// Regression test for #368: content_hash() must produce a 64-char SHA-256
    /// hex digest, not a 16-char DefaultHasher output.
    #[test]
    fn test_content_hash_is_sha256_not_default_hasher() {
        let func = make_function("foo");
        let hash = func.content_hash();
        // SHA-256 = 64 hex chars; DefaultHasher = 16 hex chars
        assert_eq!(
            hash.len(),
            64,
            "content_hash() should be SHA-256 (64 hex chars), got {} chars: {}",
            hash.len(),
            hash
        );
        assert!(hash.chars().all(|c| c.is_ascii_hexdigit()), "content_hash() must be valid hex");
    }

    // -----------------------------------------------------------------------
    // Regression tests for #690: spec_hash validation on lookup
    // -----------------------------------------------------------------------

    /// Regression test for #690: lookup must miss when spec_hash differs,
    /// even if content_hash matches. This prevents stale "proved" verdicts
    /// when a spec is strengthened but the function body stays the same.
    #[test]
    fn test_lookup_misses_on_spec_hash_mismatch() {
        let mut cache = VerificationCache::in_memory();
        let mut entry = sample_entry("body_hash", FunctionVerdict::Verified);
        entry.spec_hash = "spec_v1".to_string();
        cache.store("m::f", entry);

        // Same content_hash but different spec_hash: must miss
        assert_eq!(
            cache.lookup("m::f", "body_hash", "spec_v2"),
            CacheLookup::Miss,
            "spec change must cause cache miss even with same body hash"
        );
        // Same content_hash and same spec_hash: must hit
        assert_eq!(
            cache.lookup("m::f", "body_hash", "spec_v1"),
            CacheLookup::Hit(CacheEntry {
                content_hash: "body_hash".to_string(),
                verdict: FunctionVerdict::Verified,
                total_obligations: 3,
                proved: 2,
                failed: 0,
                unknown: 1,
                runtime_checked: 0,
                cached_at: 0,
                spec_hash: "spec_v1".to_string(),
                obligation_results: vec![],
            })
        );
    }

    /// Regression test for #690: lookup_function must miss when a contract
    /// changes, even if the function body is identical.
    #[test]
    fn test_lookup_function_misses_on_spec_change() {
        let func_v1 = make_function_with_contract("foo", "result > 0");
        let mut cache = VerificationCache::in_memory();
        cache.store_function(&func_v1, FunctionVerdict::Verified, 1, 1, 0, 0, 0);

        // Lookup with same spec: should hit
        assert!(
            matches!(cache.lookup_function(&func_v1), CacheLookup::Hit(_)),
            "identical function+spec must hit"
        );

        // Strengthen the postcondition: body identical, spec changed
        let func_v2 = make_function_with_contract("foo", "result > 0 && result < 100");
        let result = cache.lookup_function(&func_v2);
        assert_eq!(
            result,
            CacheLookup::Miss,
            "strengthened postcondition must cause cache miss (#690)"
        );
    }

    // -----------------------------------------------------------------------
    // HMAC integrity tests (#725)
    // -----------------------------------------------------------------------

    /// #725: Save + load roundtrip with HMAC must preserve entries.
    #[test]
    fn test_hmac_persistence_roundtrip() {
        let dir = tempfile::tempdir().expect("create tempdir");
        let cache_path = dir.path().join("hmac-test.json");

        // Write with HMAC
        {
            let mut cache = VerificationCache::load(&cache_path).expect("create cache");
            cache.store("m::f", sample_entry("h1", FunctionVerdict::Verified));
            cache.save().expect("save with HMAC");
        }

        // Read back -- HMAC should verify
        {
            let mut cache = VerificationCache::load(&cache_path).expect("load cache");
            assert_eq!(cache.len(), 1, "HMAC-verified cache should have 1 entry");
            assert_eq!(
                cache.lookup("m::f", "h1", ""),
                CacheLookup::Hit(sample_entry("h1", FunctionVerdict::Verified))
            );
        }
    }

    /// #725: Tampered cache file must be rejected (starts fresh).
    #[test]
    fn test_hmac_rejects_tampered_cache() {
        let dir = tempfile::tempdir().expect("create tempdir");
        let cache_path = dir.path().join("tampered.json");

        // Write a valid cache
        {
            let mut cache = VerificationCache::load(&cache_path).expect("create cache");
            cache.store("m::f", sample_entry("h1", FunctionVerdict::HasViolations));
            cache.save().expect("save cache");
        }

        // Tamper: change "HasViolations" to "Verified" in the JSON
        {
            let contents = std::fs::read_to_string(&cache_path).expect("read cache");
            let tampered = contents.replace("HasViolations", "Verified");
            assert_ne!(contents, tampered, "tamper should change file content");
            std::fs::write(&cache_path, tampered).expect("write tampered");
        }

        // Load should reject tampered file
        {
            let cache = VerificationCache::load(&cache_path).expect("load tampered");
            assert!(cache.is_empty(), "tampered cache must be rejected (#725)");
        }
    }

    /// #725: Cache file with empty HMAC (legacy v2 upgraded to v3) is rejected.
    #[test]
    fn test_hmac_rejects_empty_hmac() {
        let dir = tempfile::tempdir().expect("create tempdir");
        let cache_path = dir.path().join("no-hmac.json");

        // Write a v3 cache with no HMAC (simulating legacy upgrade)
        let json = format!(r#"{{"version": {}, "entries": {{}}, "hmac": ""}}"#, CACHE_VERSION);
        std::fs::write(&cache_path, json).expect("write no-hmac file");

        let cache = VerificationCache::load(&cache_path).expect("load no-hmac");
        assert!(cache.is_empty(), "empty HMAC must be rejected (#725)");
    }

    /// #725: Saved cache file contains non-empty HMAC field.
    #[test]
    fn test_saved_cache_has_hmac() {
        let dir = tempfile::tempdir().expect("create tempdir");
        let cache_path = dir.path().join("has-hmac.json");

        {
            let mut cache = VerificationCache::load(&cache_path).expect("create cache");
            cache.store("m::f", sample_entry("h1", FunctionVerdict::Verified));
            cache.save().expect("save cache");
        }

        // Verify the on-disk file has an hmac field
        let contents = std::fs::read_to_string(&cache_path).expect("read cache");
        let parsed: serde_json::Value = serde_json::from_str(&contents).expect("parse saved JSON");
        let hmac_val = parsed.get("hmac").expect("hmac field must exist");
        let hmac_str = hmac_val.as_str().expect("hmac must be string");
        assert_eq!(hmac_str.len(), 64, "HMAC-SHA256 hex is 64 chars");
        assert!(hmac_str.chars().all(|c| c.is_ascii_hexdigit()));
    }
}
