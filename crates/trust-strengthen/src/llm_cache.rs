// trust-strengthen/llm_cache.rs: Response caching for AI Model API spec inference
//
// Caches LLM responses keyed by (prompt_hash, model, tool_use) to avoid
// redundant API calls. Supports configurable TTL and max entries with
// oldest-first eviction. Part of Phase 3, #606.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap;
use std::time::{Duration, Instant};

use sha2::{Digest, Sha256};

use crate::LlmResponse;

/// Cache key derived from request parameters.
///
/// Uses SHA-256 of the prompt text combined with model name and tool_use flag
/// to produce a unique key. Different prompts (including counterexample
/// refinement prompts and different truncation levels) get distinct entries.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct CacheKey {
    /// SHA-256 hex digest of (prompt + model + tool_use).
    digest: String,
}

impl CacheKey {
    /// Create a cache key from request parameters.
    ///
    /// Hashes the prompt text, model name, and tool_use flag together
    /// using SHA-256 to produce a deterministic key.
    #[must_use]
    pub fn new(prompt: &str, model: &str, tool_use: bool) -> Self {
        let mut hasher = Sha256::new();
        hasher.update(prompt.as_bytes());
        hasher.update(b"\x00"); // separator
        hasher.update(model.as_bytes());
        hasher.update(b"\x00");
        hasher.update(if tool_use { b"1" } else { b"0" });
        let result = hasher.finalize();
        Self { digest: format!("{result:x}") }
    }

    /// Returns the hex digest string.
    #[must_use]
    pub fn digest(&self) -> &str {
        &self.digest
    }
}

/// A cached LLM response with metadata for invalidation and eviction.
#[derive(Debug, Clone)]
pub struct CacheEntry {
    /// The cached response.
    pub response: LlmResponse,
    /// Hash of the source code that produced the prompt, for invalidation.
    /// If the source changes, the cached response is stale.
    pub source_hash: u64,
    /// When this entry was created.
    created: Instant,
}

/// Cache hit/miss statistics.
#[derive(Debug, Clone, Default)]
pub struct CacheStats {
    /// Number of cache hits.
    pub hits: u64,
    /// Number of cache misses.
    pub misses: u64,
    /// Number of entries evicted due to capacity.
    pub evictions: u64,
    /// Number of entries expired due to TTL.
    pub expirations: u64,
    /// Number of entries invalidated due to source_hash mismatch.
    pub invalidations: u64,
}

impl CacheStats {
    /// Hit rate as a fraction in [0.0, 1.0]. Returns 0.0 if no lookups.
    #[must_use]
    pub fn hit_rate(&self) -> f64 {
        let total = self.hits + self.misses;
        if total == 0 { 0.0 } else { self.hits as f64 / total as f64 }
    }
}

/// Configuration for the response cache.
#[derive(Debug, Clone)]
pub struct CacheConfig {
    /// Time-to-live for cache entries. Default: 600 seconds.
    pub ttl: Duration,
    /// Maximum number of cached entries. Default: 256.
    pub max_entries: usize,
}

impl Default for CacheConfig {
    fn default() -> Self {
        Self { ttl: Duration::from_secs(600), max_entries: 256 }
    }
}

/// Response cache for LLM spec inference.
///
/// Simple ordered store with TTL and max_entries. Evicts oldest entries
/// first when capacity is reached. No external dependencies beyond `sha2`.
///
/// Thread safety: wrap in `Mutex` for use from `LlmSpecInference`.
#[derive(Debug)]
pub struct ResponseCache {
    entries: BTreeMap<CacheKey, CacheEntry>,
    config: CacheConfig,
    stats: CacheStats,
}

impl ResponseCache {
    /// Create a new response cache with default configuration.
    #[must_use]
    pub fn new() -> Self {
        Self {
            entries: BTreeMap::new(),
            config: CacheConfig::default(),
            stats: CacheStats::default(),
        }
    }

    /// Create a new response cache with custom configuration.
    #[must_use]
    pub fn with_config(config: CacheConfig) -> Self {
        Self { entries: BTreeMap::new(), config, stats: CacheStats::default() }
    }

    /// Look up a cached response by key, verifying source_hash and TTL.
    ///
    /// Returns `Some(response)` on a valid cache hit, `None` on miss.
    /// Expired and invalidated entries are removed on access.
    pub fn get(&mut self, key: &CacheKey, source_hash: u64) -> Option<&LlmResponse> {
        // Check if entry exists first
        if !self.entries.contains_key(key) {
            self.stats.misses += 1;
            return None;
        }

        // Check TTL
        let entry = self.entries.get(key).expect("just checked contains_key");
        if entry.created.elapsed() > self.config.ttl {
            self.entries.remove(key);
            self.stats.expirations += 1;
            self.stats.misses += 1;
            return None;
        }

        // Check source_hash for invalidation
        if entry.source_hash != source_hash {
            self.entries.remove(key);
            self.stats.invalidations += 1;
            self.stats.misses += 1;
            return None;
        }

        self.stats.hits += 1;
        // Re-borrow after mutation checks passed
        self.entries.get(key).map(|e| &e.response)
    }

    /// Insert a response into the cache. Evicts oldest entries if at capacity.
    pub fn insert(&mut self, key: CacheKey, response: LlmResponse, source_hash: u64) {
        // Evict oldest entries if at capacity
        while self.entries.len() >= self.config.max_entries {
            self.evict_oldest();
        }

        self.entries.insert(key, CacheEntry { response, source_hash, created: Instant::now() });
    }

    /// Evict the oldest entry (by creation time).
    fn evict_oldest(&mut self) {
        if self.entries.is_empty() {
            return;
        }

        // Find the oldest entry by creation time
        let oldest_key =
            self.entries.iter().min_by_key(|(_, entry)| entry.created).map(|(key, _)| key.clone());

        if let Some(key) = oldest_key {
            self.entries.remove(&key);
            self.stats.evictions += 1;
        }
    }

    /// Remove all entries from the cache.
    pub fn clear(&mut self) {
        self.entries.clear();
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

    /// Current cache statistics.
    #[must_use]
    pub fn stats(&self) -> &CacheStats {
        &self.stats
    }
}

impl Default for ResponseCache {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_response(content: &str) -> LlmResponse {
        LlmResponse {
            content: content.into(),
            used_tool_use: false,
            model_used: "test-model".into(),
        }
    }

    // -- CacheKey tests --

    #[test]
    fn test_cache_key_deterministic() {
        let k1 = CacheKey::new("prompt text", "AI Model-sonnet-4-20250514", false);
        let k2 = CacheKey::new("prompt text", "AI Model-sonnet-4-20250514", false);
        assert_eq!(k1, k2);
        assert_eq!(k1.digest(), k2.digest());
    }

    #[test]
    fn test_cache_key_different_prompts() {
        let k1 = CacheKey::new("prompt A", "model", false);
        let k2 = CacheKey::new("prompt B", "model", false);
        assert_ne!(k1, k2);
    }

    #[test]
    fn test_cache_key_different_models() {
        let k1 = CacheKey::new("prompt", "model-a", false);
        let k2 = CacheKey::new("prompt", "model-b", false);
        assert_ne!(k1, k2);
    }

    #[test]
    fn test_cache_key_different_tool_use() {
        let k1 = CacheKey::new("prompt", "model", false);
        let k2 = CacheKey::new("prompt", "model", true);
        assert_ne!(k1, k2);
    }

    #[test]
    fn test_cache_key_digest_is_hex() {
        let key = CacheKey::new("test", "model", false);
        assert_eq!(key.digest().len(), 64); // SHA-256 = 32 bytes = 64 hex chars
        assert!(key.digest().chars().all(|c| c.is_ascii_hexdigit()));
    }

    #[test]
    fn test_cache_key_empty_inputs() {
        let k1 = CacheKey::new("", "", false);
        let k2 = CacheKey::new("", "", true);
        assert_ne!(k1, k2);
        // Both should still produce valid 64-char hex digests
        assert_eq!(k1.digest().len(), 64);
    }

    // -- CacheStats tests --

    #[test]
    fn test_cache_stats_default() {
        let stats = CacheStats::default();
        assert_eq!(stats.hits, 0);
        assert_eq!(stats.misses, 0);
        assert_eq!(stats.evictions, 0);
        assert_eq!(stats.expirations, 0);
        assert_eq!(stats.invalidations, 0);
    }

    #[test]
    fn test_cache_stats_hit_rate_no_lookups() {
        let stats = CacheStats::default();
        assert!((stats.hit_rate() - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_cache_stats_hit_rate_all_hits() {
        let stats = CacheStats { hits: 10, misses: 0, ..Default::default() };
        assert!((stats.hit_rate() - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_cache_stats_hit_rate_mixed() {
        let stats = CacheStats { hits: 3, misses: 7, ..Default::default() };
        assert!((stats.hit_rate() - 0.3).abs() < f64::EPSILON);
    }

    // -- ResponseCache tests --

    #[test]
    fn test_cache_new_is_empty() {
        let cache = ResponseCache::new();
        assert!(cache.is_empty());
        assert_eq!(cache.len(), 0);
    }

    #[test]
    fn test_cache_insert_and_get() {
        let mut cache = ResponseCache::new();
        let key = CacheKey::new("prompt", "model", false);
        let response = make_response("cached content");

        cache.insert(key.clone(), response, 42);
        assert_eq!(cache.len(), 1);

        let hit = cache.get(&key, 42);
        assert!(hit.is_some());
        assert_eq!(hit.expect("just checked is_some").content, "cached content");
        assert_eq!(cache.stats().hits, 1);
    }

    #[test]
    fn test_cache_miss_nonexistent_key() {
        let mut cache = ResponseCache::new();
        let key = CacheKey::new("not-stored", "model", false);

        let hit = cache.get(&key, 42);
        assert!(hit.is_none());
        assert_eq!(cache.stats().misses, 1);
    }

    #[test]
    fn test_cache_invalidation_source_hash_mismatch() {
        let mut cache = ResponseCache::new();
        let key = CacheKey::new("prompt", "model", false);
        cache.insert(key.clone(), make_response("old"), 42);

        // Different source_hash should invalidate
        let hit = cache.get(&key, 99);
        assert!(hit.is_none());
        assert_eq!(cache.stats().invalidations, 1);
        assert_eq!(cache.stats().misses, 1);
        assert!(cache.is_empty(), "invalidated entry should be removed");
    }

    #[test]
    fn test_cache_expiration() {
        let config = CacheConfig { ttl: Duration::from_millis(1), max_entries: 256 };
        let mut cache = ResponseCache::with_config(config);
        let key = CacheKey::new("prompt", "model", false);
        cache.insert(key.clone(), make_response("ephemeral"), 42);

        // Wait for TTL to expire
        std::thread::sleep(Duration::from_millis(5));

        let hit = cache.get(&key, 42);
        assert!(hit.is_none());
        assert_eq!(cache.stats().expirations, 1);
        assert!(cache.is_empty(), "expired entry should be removed");
    }

    #[test]
    fn test_cache_eviction_at_capacity() {
        let config = CacheConfig { ttl: Duration::from_secs(600), max_entries: 3 };
        let mut cache = ResponseCache::with_config(config);

        // Fill to capacity
        for i in 0..3 {
            let key = CacheKey::new(&format!("prompt-{i}"), "model", false);
            cache.insert(key, make_response(&format!("resp-{i}")), 42);
        }
        assert_eq!(cache.len(), 3);

        // Insert one more to trigger eviction
        let new_key = CacheKey::new("prompt-3", "model", false);
        cache.insert(new_key, make_response("resp-3"), 42);
        assert_eq!(cache.len(), 3);
        assert_eq!(cache.stats().evictions, 1);
    }

    #[test]
    fn test_cache_overwrite_existing_key() {
        let mut cache = ResponseCache::new();
        let key = CacheKey::new("prompt", "model", false);

        cache.insert(key.clone(), make_response("first"), 42);
        cache.insert(key.clone(), make_response("second"), 42);

        let hit = cache.get(&key, 42);
        assert!(hit.is_some());
        assert_eq!(hit.expect("just checked").content, "second");
        assert_eq!(cache.len(), 1);
    }

    #[test]
    fn test_cache_clear() {
        let mut cache = ResponseCache::new();
        for i in 0..5 {
            let key = CacheKey::new(&format!("p-{i}"), "model", false);
            cache.insert(key, make_response("x"), 42);
        }
        assert_eq!(cache.len(), 5);

        cache.clear();
        assert!(cache.is_empty());
    }

    #[test]
    fn test_cache_multiple_distinct_entries() {
        let mut cache = ResponseCache::new();

        let k1 = CacheKey::new("prompt-a", "model", false);
        let k2 = CacheKey::new("prompt-b", "model", false);
        let k3 = CacheKey::new("prompt-a", "model", true);

        cache.insert(k1.clone(), make_response("a-no-tool"), 1);
        cache.insert(k2.clone(), make_response("b-no-tool"), 2);
        cache.insert(k3.clone(), make_response("a-tool"), 3);

        assert_eq!(cache.len(), 3);
        assert_eq!(cache.get(&k1, 1).expect("k1 should hit").content, "a-no-tool");
        assert_eq!(cache.get(&k2, 2).expect("k2 should hit").content, "b-no-tool");
        assert_eq!(cache.get(&k3, 3).expect("k3 should hit").content, "a-tool");
        assert_eq!(cache.stats().hits, 3);
    }

    #[test]
    fn test_cache_stats_accumulate() {
        let mut cache = ResponseCache::new();
        let key = CacheKey::new("prompt", "model", false);
        cache.insert(key.clone(), make_response("x"), 42);

        // 2 hits
        cache.get(&key, 42);
        cache.get(&key, 42);

        // 1 miss (wrong key)
        let missing = CacheKey::new("other", "model", false);
        cache.get(&missing, 42);

        assert_eq!(cache.stats().hits, 2);
        assert_eq!(cache.stats().misses, 1);
    }

    #[test]
    fn test_cache_config_defaults() {
        let config = CacheConfig::default();
        assert_eq!(config.ttl, Duration::from_secs(600));
        assert_eq!(config.max_entries, 256);
    }
}
