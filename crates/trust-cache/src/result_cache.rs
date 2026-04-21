// trust-cache/src/result_cache.rs: Solver result caching with replay
//
// Remembers solver answers keyed by (formula_hash, solver_name) and can replay
// them on cache hit. Supports configurable cache policies (always, on-success,
// TTL-based, never) and stale-entry invalidation.
//
// tRust #527: Consolidated from trust-router into trust-cache so that all
// caching implementations live in the dedicated cache crate.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use trust_types::ProofLevel;

/// Key for a cached solver result: (formula_hash, solver_name).
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ResultCacheKey {
    pub formula_hash: String,
    pub solver_name: String,
}

/// A cached solver result entry.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CachedResult {
    pub key: ResultCacheKey,
    pub verdict: String,
    pub model: Option<String>,
    pub time_ms: u64,
    pub cached_at: u64,
    /// tRust #755: JSON-serialized `ProofStrength` for proved results.
    /// `None` for non-proved verdicts or legacy entries (defaults to `smt_unsat()`).
    #[serde(default)]
    pub strength_json: Option<String>,
}

/// Policy controlling when results are cached.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum CachePolicy {
    /// Cache every result regardless of verdict.
    AlwaysCache,
    /// Cache only results where the verdict indicates success ("proved").
    CacheOnSuccess,
    /// Cache all results but with a TTL (seconds) after which they are stale.
    CacheWithTTL(u64),
    /// Never cache any result.
    NeverCache,
}

/// Configuration for replay behavior.
///
/// Use [`ReplayConfig::for_proof_level`] to get proof-level-aware defaults:
/// L0Safety and L1Functional enable validation on replay; L2Domain does not.
/// The [`Default`] impl is conservative: `validate_on_replay: true`. See #726.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReplayConfig {
    /// Whether to validate cached results on replay (re-check against solver).
    pub validate_on_replay: bool,
    /// Maximum age (seconds) for a cached result to be eligible for replay.
    pub max_age_seconds: u64,
}

impl ReplayConfig {
    /// Create a replay config appropriate for the given proof level.
    ///
    /// - **L0Safety / L1Functional**: `validate_on_replay = true` -- these are
    ///   safety-critical and functional-correctness VCs; tampered or stale cache
    ///   entries must be re-verified.
    /// - **L2Domain**: `validate_on_replay = false` -- domain-level VCs are
    ///   lower severity and can tolerate replay without re-verification for
    ///   performance.
    #[must_use]
    pub fn for_proof_level(level: ProofLevel) -> Self {
        let validate = match level {
            ProofLevel::L0Safety | ProofLevel::L1Functional => true,
            ProofLevel::L2Domain => false,
            // Future proof levels default to no re-validation.
            _ => false,
        };
        Self { validate_on_replay: validate, max_age_seconds: 3600 }
    }
}

impl Default for ReplayConfig {
    /// Conservative default: validates on replay. Prefer
    /// [`ReplayConfig::for_proof_level`] for proof-level-aware configuration.
    fn default() -> Self {
        Self {
            validate_on_replay: true,
            max_age_seconds: 3600,
        }
    }
}

/// Statistics about cache usage.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct CacheStats {
    pub total_entries: usize,
    pub hits: usize,
    pub misses: usize,
    pub evictions: usize,
    pub replays: usize,
}

/// Solver result cache with replay support.
pub struct ResultCache {
    policy: CachePolicy,
    entries: FxHashMap<ResultCacheKey, CachedResult>,
    stats: CacheStats,
}

impl ResultCache {
    /// Create a new result cache with the given caching policy.
    #[must_use]
    pub fn new(policy: CachePolicy) -> Self {
        Self {
            policy,
            entries: FxHashMap::default(),
            stats: CacheStats::default(),
        }
    }

    /// Cache a solver result under the given key.
    ///
    /// Respects the cache policy: `NeverCache` silently drops, `CacheOnSuccess`
    /// only stores results with verdict "proved".
    ///
    /// `strength_json`: JSON-serialized `ProofStrength` for proved results.
    /// Pass `None` for non-proved verdicts. See tRust #755.
    pub fn cache_result(
        &mut self,
        key: ResultCacheKey,
        verdict: &str,
        model: Option<String>,
        time_ms: u64,
        strength_json: Option<String>,
    ) {
        match &self.policy {
            CachePolicy::NeverCache => return,
            CachePolicy::CacheOnSuccess if verdict != "proved" => return,
            _ => {}
        }

        let cached_at = self.current_time_secs();
        let entry = CachedResult {
            key: key.clone(),
            verdict: verdict.to_string(),
            model,
            time_ms,
            cached_at,
            strength_json,
        };
        self.entries.insert(key, entry);
        self.stats.total_entries = self.entries.len();
    }

    /// Replay a cached result if present, updating hit/miss stats.
    pub fn replay_result(&mut self, key: &ResultCacheKey) -> Option<&CachedResult> {
        if self.entries.contains_key(key) {
            self.stats.hits += 1;
            self.stats.replays += 1;
            self.entries.get(key)
        } else {
            self.stats.misses += 1;
            None
        }
    }

    /// Invalidate entries older than `max_age_seconds`. Returns eviction count.
    pub fn invalidate_stale(&mut self, max_age_seconds: u64) -> usize {
        let now = self.current_time_secs();
        let before = self.entries.len();
        self.entries.retain(|_, entry| {
            now.saturating_sub(entry.cached_at) <= max_age_seconds
        });
        let evicted = before - self.entries.len();
        self.stats.evictions += evicted;
        self.stats.total_entries = self.entries.len();
        evicted
    }

    /// Invalidate all entries from a specific solver. Returns eviction count.
    pub fn invalidate_by_solver(&mut self, solver: &str) -> usize {
        let before = self.entries.len();
        self.entries.retain(|key, _| key.solver_name != solver);
        let evicted = before - self.entries.len();
        self.stats.evictions += evicted;
        self.stats.total_entries = self.entries.len();
        evicted
    }

    /// Warm the cache with pre-existing entries (e.g., loaded from disk).
    pub fn warm_cache(&mut self, entries: Vec<CachedResult>) {
        for entry in entries {
            self.entries.insert(entry.key.clone(), entry);
        }
        self.stats.total_entries = self.entries.len();
    }

    /// Return current cache statistics.
    #[must_use]
    pub fn cache_stats(&self) -> CacheStats {
        let mut stats = self.stats.clone();
        stats.total_entries = self.entries.len();
        stats
    }

    /// Return the number of cached entries.
    #[must_use]
    pub fn entry_count(&self) -> usize {
        self.entries.len()
    }

    /// Remove all cached entries.
    pub fn clear(&mut self) {
        self.entries.clear();
        self.stats.total_entries = 0;
    }

    /// Monotonic timestamp in seconds. In production this would use
    /// `std::time::SystemTime`; here we use a simple epoch-based approach.
    fn current_time_secs(&self) -> u64 {
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_secs())
            .unwrap_or(0)
    }
}

/// Hash a formula string into a hex-encoded SHA-256 digest.
///
/// Uses SHA-256 for collision resistance. A 64-bit hash (DefaultHasher/SipHash)
/// has birthday collisions at ~2^32 formulas, which could cause one formula's
/// cached verdict to be returned for a different formula -- a soundness bug.
/// SHA-256 pushes that threshold to ~2^128. See #692.
#[must_use]
pub fn hash_formula(formula: &str) -> String {
    let mut hasher = Sha256::new();
    hasher.update(formula.as_bytes());
    format!("{:x}", hasher.finalize())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_key(formula: &str, solver: &str) -> ResultCacheKey {
        ResultCacheKey {
            formula_hash: hash_formula(formula),
            solver_name: solver.to_string(),
        }
    }

    #[test]
    fn test_cache_result_and_replay_hit() {
        let mut cache = ResultCache::new(CachePolicy::AlwaysCache);
        let key = make_key("x > 0", "z4");
        cache.cache_result(key.clone(), "proved", None, 42, None);

        let result = cache.replay_result(&key);
        assert!(result.is_some());
        let entry = result.unwrap();
        assert_eq!(entry.verdict, "proved");
        assert_eq!(entry.time_ms, 42);
    }

    #[test]
    fn test_replay_miss_returns_none() {
        let mut cache = ResultCache::new(CachePolicy::AlwaysCache);
        let key = make_key("x > 0", "z4");

        assert!(cache.replay_result(&key).is_none());
    }

    #[test]
    fn test_cache_on_success_skips_non_proved() {
        let mut cache = ResultCache::new(CachePolicy::CacheOnSuccess);
        let key = make_key("x > 0", "z4");
        cache.cache_result(key.clone(), "failed", None, 10, None);

        assert_eq!(cache.entry_count(), 0);
        assert!(cache.replay_result(&key).is_none());
    }

    #[test]
    fn test_cache_on_success_stores_proved() {
        let mut cache = ResultCache::new(CachePolicy::CacheOnSuccess);
        let key = make_key("x > 0", "z4");
        cache.cache_result(key.clone(), "proved", None, 10, None);

        assert_eq!(cache.entry_count(), 1);
        assert!(cache.replay_result(&key).is_some());
    }

    #[test]
    fn test_never_cache_stores_nothing() {
        let mut cache = ResultCache::new(CachePolicy::NeverCache);
        let key = make_key("x > 0", "z4");
        cache.cache_result(key.clone(), "proved", None, 10, None);

        assert_eq!(cache.entry_count(), 0);
    }

    #[test]
    fn test_invalidate_stale_removes_old_entries() {
        let mut cache = ResultCache::new(CachePolicy::AlwaysCache);
        let key = make_key("x > 0", "z4");

        // Insert an entry with a very old timestamp by warming.
        let old_entry = CachedResult {
            key: key.clone(),
            verdict: "proved".to_string(),
            model: None,
            time_ms: 10,
            cached_at: 1, // epoch second 1 -- ancient
            strength_json: None,
        };
        cache.warm_cache(vec![old_entry]);
        assert_eq!(cache.entry_count(), 1);

        let evicted = cache.invalidate_stale(60);
        assert_eq!(evicted, 1);
        assert_eq!(cache.entry_count(), 0);
    }

    #[test]
    fn test_invalidate_stale_keeps_fresh_entries() {
        let mut cache = ResultCache::new(CachePolicy::AlwaysCache);
        let key = make_key("x > 0", "z4");
        cache.cache_result(key.clone(), "proved", None, 10, None);

        // Very large TTL -- nothing should be evicted.
        let evicted = cache.invalidate_stale(u64::MAX);
        assert_eq!(evicted, 0);
        assert_eq!(cache.entry_count(), 1);
    }

    #[test]
    fn test_invalidate_by_solver() {
        let mut cache = ResultCache::new(CachePolicy::AlwaysCache);
        let key_z4 = make_key("x > 0", "z4");
        let key_sunder = make_key("x > 0", "sunder");
        cache.cache_result(key_z4.clone(), "proved", None, 10, None);
        cache.cache_result(key_sunder.clone(), "proved", None, 20, None);
        assert_eq!(cache.entry_count(), 2);

        let evicted = cache.invalidate_by_solver("z4");
        assert_eq!(evicted, 1);
        assert_eq!(cache.entry_count(), 1);
        assert!(cache.replay_result(&key_sunder).is_some());
    }

    #[test]
    fn test_warm_cache_loads_entries() {
        let mut cache = ResultCache::new(CachePolicy::AlwaysCache);
        let entries = vec![
            CachedResult {
                key: make_key("a", "z4"),
                verdict: "proved".to_string(),
                model: None,
                time_ms: 1,
                cached_at: 100,
                strength_json: None,
            },
            CachedResult {
                key: make_key("b", "z4"),
                verdict: "failed".to_string(),
                model: Some("x=5".to_string()),
                time_ms: 2,
                cached_at: 200,
                strength_json: None,
            },
        ];
        cache.warm_cache(entries);
        assert_eq!(cache.entry_count(), 2);
    }

    #[test]
    fn test_clear_removes_all() {
        let mut cache = ResultCache::new(CachePolicy::AlwaysCache);
        cache.cache_result(make_key("a", "z4"), "proved", None, 1, None);
        cache.cache_result(make_key("b", "z4"), "failed", None, 2, None);
        assert_eq!(cache.entry_count(), 2);

        cache.clear();
        assert_eq!(cache.entry_count(), 0);
    }

    #[test]
    fn test_cache_stats_tracks_hits_and_misses() {
        let mut cache = ResultCache::new(CachePolicy::AlwaysCache);
        let key = make_key("x > 0", "z4");
        cache.cache_result(key.clone(), "proved", None, 10, None);

        // Miss
        let _ = cache.replay_result(&make_key("unknown", "z4"));
        // Hit
        let _ = cache.replay_result(&key);

        let stats = cache.cache_stats();
        assert_eq!(stats.hits, 1);
        assert_eq!(stats.misses, 1);
        assert_eq!(stats.replays, 1);
        assert_eq!(stats.total_entries, 1);
    }

    #[test]
    fn test_cache_stats_tracks_evictions() {
        let mut cache = ResultCache::new(CachePolicy::AlwaysCache);
        let old = CachedResult {
            key: make_key("old", "z4"),
            verdict: "proved".to_string(),
            model: None,
            time_ms: 1,
            cached_at: 1,
            strength_json: None,
        };
        cache.warm_cache(vec![old]);
        cache.invalidate_stale(60);

        let stats = cache.cache_stats();
        assert_eq!(stats.evictions, 1);
    }

    #[test]
    fn test_hash_formula_deterministic() {
        let h1 = hash_formula("x > 0 && y < 10");
        let h2 = hash_formula("x > 0 && y < 10");
        assert_eq!(h1, h2);
    }

    #[test]
    fn test_hash_formula_different_inputs_differ() {
        let h1 = hash_formula("x > 0");
        let h2 = hash_formula("x < 0");
        assert_ne!(h1, h2);
    }

    #[test]
    fn test_hash_formula_returns_hex_string() {
        let h = hash_formula("test");
        assert_eq!(h.len(), 64, "SHA-256 -> 64 hex chars");
        assert!(h.chars().all(|c| c.is_ascii_hexdigit()));
    }

    #[test]
    fn test_cache_with_model() {
        let mut cache = ResultCache::new(CachePolicy::AlwaysCache);
        let key = make_key("x > 0", "z4");
        cache.cache_result(key.clone(), "failed", Some("x=0".to_string()), 5, None);

        let result = cache.replay_result(&key).unwrap();
        assert_eq!(result.model.as_deref(), Some("x=0"));
    }

    #[test]
    fn test_cache_with_ttl_stores_all_verdicts() {
        let mut cache = ResultCache::new(CachePolicy::CacheWithTTL(3600));
        let key = make_key("x > 0", "z4");
        cache.cache_result(key.clone(), "unknown", None, 100, None);

        assert_eq!(cache.entry_count(), 1);
        assert!(cache.replay_result(&key).is_some());
    }

    #[test]
    fn test_replay_config_default_validates() {
        // #726: Default is now conservative (validate_on_replay: true).
        let config = ReplayConfig::default();
        assert!(config.validate_on_replay, "default must validate on replay (#726)");
        assert_eq!(config.max_age_seconds, 3600);
    }

    #[test]
    fn test_replay_config_l0_safety_validates() {
        let config = ReplayConfig::for_proof_level(trust_types::ProofLevel::L0Safety);
        assert!(config.validate_on_replay, "L0Safety must validate on replay");
        assert_eq!(config.max_age_seconds, 3600);
    }

    #[test]
    fn test_replay_config_l1_functional_validates() {
        let config = ReplayConfig::for_proof_level(trust_types::ProofLevel::L1Functional);
        assert!(config.validate_on_replay, "L1Functional must validate on replay");
        assert_eq!(config.max_age_seconds, 3600);
    }

    #[test]
    fn test_replay_config_l2_domain_skips_validation() {
        let config = ReplayConfig::for_proof_level(trust_types::ProofLevel::L2Domain);
        assert!(!config.validate_on_replay, "L2Domain should skip validation by default");
        assert_eq!(config.max_age_seconds, 3600);
    }
}
