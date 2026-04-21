// trust-cache/src/vc_cache.rs: Content-addressed VC caching
//
// Avoids re-generating identical verification conditions by caching VC text
// keyed on a deterministic content hash of the VC body.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;
use std::time::{SystemTime, UNIX_EPOCH};

/// Deterministic content hash of VC text using SHA-256.
///
/// Returns a hex-encoded 256-bit hash string (64 chars). Uses SHA-256 for
/// determinism across Rust versions (unlike `DefaultHasher` which is not
/// guaranteed stable). See #368.
///
/// # Examples
///
/// ```
/// use trust_cache::vc_cache::content_hash;
///
/// let hash = content_hash("(assert (= x 0))");
/// assert_eq!(hash.len(), 64); // hex-encoded SHA-256
///
/// // Deterministic: same input always produces same hash
/// assert_eq!(hash, content_hash("(assert (= x 0))"));
/// ```
#[must_use]
pub fn content_hash(vc_text: &str) -> String {
    use sha2::{Digest, Sha256};
    let mut hasher = Sha256::new();
    hasher.update(vc_text.as_bytes());
    format!("{:x}", hasher.finalize())
}

/// Key for content-addressed VC lookup.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VcCacheKey {
    /// Deterministic hash of the VC text.
    pub content_hash: String,
    /// Fully qualified function path (e.g. `crate::module::func`).
    pub function_path: String,
}

/// A cached verification condition entry.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VcCacheEntry {
    /// The key that produced this entry.
    pub key: VcCacheKey,
    /// The full VC text.
    pub vc_text: String,
    /// Unix timestamp (seconds) when this entry was generated.
    pub generated_at: u64,
    /// Number of times this entry has been looked up successfully.
    pub hit_count: usize,
}

/// Configuration for the VC cache.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CacheConfig {
    /// Maximum number of entries before eviction.
    pub max_entries: usize,
    /// Approximate memory budget in bytes.
    pub max_memory_bytes: usize,
    /// Time-to-live in seconds; entries older than this are eviction candidates.
    pub ttl_seconds: u64,
}

impl Default for CacheConfig {
    fn default() -> Self {
        Self {
            max_entries: 4096,
            max_memory_bytes: 64 * 1024 * 1024, // 64 MiB
            ttl_seconds: 3600,                   // 1 hour
        }
    }
}

/// Aggregated cache performance metrics.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct CacheMetrics {
    /// Total number of lookup calls.
    pub total_lookups: usize,
    /// Number of successful lookups (hits).
    pub hits: usize,
    /// Number of failed lookups (misses).
    pub misses: usize,
    /// Number of entries evicted.
    pub evictions: usize,
}

/// Content-addressed VC cache.
///
/// Stores verification condition text keyed by a deterministic content hash.
/// Supports TTL-based eviction, per-function invalidation, and memory-aware
/// compaction.
///
/// # Examples
///
/// ```
/// use trust_cache::vc_cache::{VcCache, VcCacheKey, CacheConfig};
///
/// let mut cache = VcCache::new(CacheConfig::default());
///
/// // Cache a VC
/// let key = VcCacheKey {
///     content_hash: trust_cache::vc_cache::content_hash("(assert (= x 0))"),
///     function_path: "my_crate::div".to_string(),
/// };
/// cache.cache_vc(key.clone(), "(assert (= x 0))".to_string());
///
/// // Look it up
/// let entry = cache.lookup_vc(&key.content_hash);
/// assert!(entry.is_some());
/// assert_eq!(entry.unwrap().vc_text, "(assert (= x 0))");
///
/// // Check metrics
/// let metrics = cache.metrics();
/// assert_eq!(metrics.hits, 1);
/// ```
pub struct VcCache {
    config: CacheConfig,
    /// Primary index: content_hash -> entry.
    entries: FxHashMap<String, VcCacheEntry>,
    metrics: CacheMetrics,
}

impl VcCache {
    /// Create a new cache with the given configuration.
    #[must_use]
    pub fn new(config: CacheConfig) -> Self {
        Self {
            config,
            entries: FxHashMap::default(),
            metrics: CacheMetrics::default(),
        }
    }

    /// Insert or update a cached VC.
    pub fn cache_vc(&mut self, key: VcCacheKey, vc_text: String) {
        let entry = VcCacheEntry {
            key: key.clone(),
            vc_text,
            generated_at: now_unix_secs(),
            hit_count: 0,
        };
        self.entries.insert(key.content_hash.clone(), entry);

        // Evict if over capacity.
        if self.entries.len() > self.config.max_entries {
            self.compact_cache();
        }
    }

    /// Look up a VC by content hash.
    ///
    /// Returns `Some` on hit (incrementing hit_count), `None` on miss.
    pub fn lookup_vc(&mut self, content_hash: &str) -> Option<&VcCacheEntry> {
        self.metrics.total_lookups += 1;

        // Check if the entry exists first without borrowing self mutably twice.
        if self.entries.contains_key(content_hash) {
            self.metrics.hits += 1;
            // SAFETY: We just confirmed contains_key(content_hash) above.
            let entry = self.entries.get_mut(content_hash)
                .unwrap_or_else(|| unreachable!("key missing after contains_key check"));
            entry.hit_count += 1;
            // Return a shared reference from the map.
            self.entries.get(content_hash)
        } else {
            self.metrics.misses += 1;
            None
        }
    }

    /// Invalidate all entries whose function_path matches.
    ///
    /// Returns the number of entries removed.
    pub fn invalidate_by_function(&mut self, function_path: &str) -> usize {
        let before = self.entries.len();
        self.entries.retain(|_, e| e.key.function_path != function_path);
        let removed = before - self.entries.len();
        self.metrics.evictions += removed;
        removed
    }

    /// Invalidate a single entry by content hash.
    ///
    /// Returns `true` if an entry was removed.
    pub fn invalidate_by_hash(&mut self, content_hash: &str) -> bool {
        let removed = self.entries.remove(content_hash).is_some();
        if removed {
            self.metrics.evictions += 1;
        }
        removed
    }

    /// Cache hit rate as a fraction in `[0.0, 1.0]`.
    ///
    /// Returns `0.0` if no lookups have been performed.
    #[must_use]
    pub fn cache_hit_rate(&self) -> f64 {
        if self.metrics.total_lookups == 0 {
            return 0.0;
        }
        self.metrics.hits as f64 / self.metrics.total_lookups as f64
    }

    /// Evict stale or low-value entries.
    ///
    /// Removes entries older than TTL, then evicts least-hit entries if still
    /// over capacity. Returns the total number of entries evicted.
    pub fn compact_cache(&mut self) -> usize {
        let now = now_unix_secs();
        let before = self.entries.len();

        // Phase 1: TTL eviction.
        self.entries.retain(|_, e| {
            now.saturating_sub(e.generated_at) <= self.config.ttl_seconds
        });

        // Phase 2: if still over max_entries, evict least-hit entries.
        if self.entries.len() > self.config.max_entries {
            let mut by_hits: Vec<(String, usize)> = self
                .entries
                .iter()
                .map(|(k, e)| (k.clone(), e.hit_count))
                .collect();
            by_hits.sort_by_key(|(_, hits)| *hits);

            let to_remove = self.entries.len() - self.config.max_entries;
            for (hash, _) in by_hits.into_iter().take(to_remove) {
                self.entries.remove(&hash);
            }
        }

        // Phase 3: approximate memory check — evict oldest if over budget.
        while self.approx_memory_bytes() > self.config.max_memory_bytes
            && !self.entries.is_empty()
        {
            // Find the oldest entry.
            if let Some(oldest_key) = self
                .entries
                .iter()
                .min_by_key(|(_, e)| e.generated_at)
                .map(|(k, _)| k.clone())
            {
                self.entries.remove(&oldest_key);
            }
        }

        let evicted = before - self.entries.len();
        self.metrics.evictions += evicted;
        evicted
    }

    /// Number of entries currently in the cache.
    #[must_use]
    pub fn entry_count(&self) -> usize {
        self.entries.len()
    }

    /// Read-only access to cache metrics.
    #[must_use]
    pub fn metrics(&self) -> &CacheMetrics {
        &self.metrics
    }

    /// Remove all entries and reset metrics.
    pub fn clear(&mut self) {
        self.entries.clear();
        self.metrics = CacheMetrics::default();
    }

    /// Approximate memory usage in bytes.
    fn approx_memory_bytes(&self) -> usize {
        self.entries
            .values()
            .map(|e| {
                e.vc_text.len()
                    + e.key.content_hash.len()
                    + e.key.function_path.len()
                    + 64 // overhead for HashMap node, VcCacheEntry struct
            })
            .sum()
    }
}

/// Current Unix timestamp in seconds.
fn now_unix_secs() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn default_config() -> CacheConfig {
        CacheConfig {
            max_entries: 100,
            max_memory_bytes: 1024 * 1024,
            ttl_seconds: 3600,
        }
    }

    fn make_key(func: &str, text: &str) -> VcCacheKey {
        VcCacheKey {
            content_hash: content_hash(text),
            function_path: func.to_string(),
        }
    }

    // -------------------------------------------------------------------
    // content_hash tests
    // -------------------------------------------------------------------

    #[test]
    fn test_content_hash_deterministic() {
        let h1 = content_hash("assert x > 0");
        let h2 = content_hash("assert x > 0");
        assert_eq!(h1, h2, "content_hash must be deterministic");
    }

    #[test]
    fn test_content_hash_different_inputs_differ() {
        let h1 = content_hash("assert x > 0");
        let h2 = content_hash("assert x < 0");
        assert_ne!(h1, h2, "different inputs must produce different hashes");
    }

    #[test]
    fn test_content_hash_hex_format() {
        let h = content_hash("some vc text");
        assert_eq!(h.len(), 64, "SHA-256 → 64 hex chars");
        assert!(h.chars().all(|c| c.is_ascii_hexdigit()), "must be hex");
    }

    #[test]
    fn test_content_hash_empty_input() {
        let h = content_hash("");
        assert_eq!(h.len(), 64, "SHA-256 → 64 hex chars even for empty input");
    }

    // -------------------------------------------------------------------
    // VcCache basic operations
    // -------------------------------------------------------------------

    #[test]
    fn test_cache_insert_and_lookup_hit() {
        let mut cache = VcCache::new(default_config());
        let key = make_key("crate::foo", "vc body 1");
        cache.cache_vc(key.clone(), "vc body 1".to_string());

        let result = cache.lookup_vc(&key.content_hash);
        assert!(result.is_some(), "should hit after insert");
        let entry = result.unwrap();
        assert_eq!(entry.vc_text, "vc body 1");
        assert_eq!(entry.key.function_path, "crate::foo");
        assert_eq!(entry.hit_count, 1);
    }

    #[test]
    fn test_cache_lookup_miss() {
        let mut cache = VcCache::new(default_config());
        let result = cache.lookup_vc("nonexistent");
        assert!(result.is_none(), "lookup on empty cache must miss");
        assert_eq!(cache.metrics().misses, 1);
    }

    #[test]
    fn test_cache_hit_count_increments() {
        let mut cache = VcCache::new(default_config());
        let key = make_key("crate::bar", "vc text");
        cache.cache_vc(key.clone(), "vc text".to_string());

        cache.lookup_vc(&key.content_hash);
        cache.lookup_vc(&key.content_hash);
        cache.lookup_vc(&key.content_hash);

        let entry = cache.lookup_vc(&key.content_hash).unwrap();
        assert_eq!(entry.hit_count, 4, "should have 4 hits total");
    }

    // -------------------------------------------------------------------
    // Invalidation
    // -------------------------------------------------------------------

    #[test]
    fn test_invalidate_by_function() {
        let mut cache = VcCache::new(default_config());
        cache.cache_vc(make_key("mod::a", "vc1"), "vc1".to_string());
        cache.cache_vc(make_key("mod::a", "vc2"), "vc2".to_string());
        cache.cache_vc(make_key("mod::b", "vc3"), "vc3".to_string());

        let removed = cache.invalidate_by_function("mod::a");
        assert_eq!(removed, 2);
        assert_eq!(cache.entry_count(), 1);
    }

    #[test]
    fn test_invalidate_by_hash() {
        let mut cache = VcCache::new(default_config());
        let key = make_key("crate::f", "body");
        cache.cache_vc(key.clone(), "body".to_string());

        assert!(cache.invalidate_by_hash(&key.content_hash));
        assert!(!cache.invalidate_by_hash(&key.content_hash), "second remove should return false");
        assert_eq!(cache.entry_count(), 0);
    }

    #[test]
    fn test_invalidate_by_function_nonexistent() {
        let mut cache = VcCache::new(default_config());
        cache.cache_vc(make_key("mod::a", "vc1"), "vc1".to_string());
        let removed = cache.invalidate_by_function("mod::nonexistent");
        assert_eq!(removed, 0);
        assert_eq!(cache.entry_count(), 1);
    }

    // -------------------------------------------------------------------
    // Metrics and hit rate
    // -------------------------------------------------------------------

    #[test]
    fn test_cache_hit_rate_no_lookups() {
        let cache = VcCache::new(default_config());
        assert!((cache.cache_hit_rate() - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_cache_hit_rate_all_hits() {
        let mut cache = VcCache::new(default_config());
        let key = make_key("f", "v");
        cache.cache_vc(key.clone(), "v".to_string());
        cache.lookup_vc(&key.content_hash);
        cache.lookup_vc(&key.content_hash);
        assert!((cache.cache_hit_rate() - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_cache_hit_rate_mixed() {
        let mut cache = VcCache::new(default_config());
        let key = make_key("f", "v");
        cache.cache_vc(key.clone(), "v".to_string());

        cache.lookup_vc(&key.content_hash); // hit
        cache.lookup_vc("missing");          // miss

        assert!((cache.cache_hit_rate() - 0.5).abs() < f64::EPSILON);
    }

    #[test]
    fn test_metrics_tracks_evictions() {
        let mut cache = VcCache::new(default_config());
        let key = make_key("f", "v");
        cache.cache_vc(key.clone(), "v".to_string());
        cache.invalidate_by_hash(&key.content_hash);
        assert_eq!(cache.metrics().evictions, 1);
    }

    // -------------------------------------------------------------------
    // Compaction and eviction
    // -------------------------------------------------------------------

    #[test]
    fn test_compact_cache_evicts_over_capacity() {
        let config = CacheConfig {
            max_entries: 2,
            max_memory_bytes: 1024 * 1024,
            ttl_seconds: 3600,
        };
        let mut cache = VcCache::new(config);

        // Insert 3 entries; capacity is 2 so compaction triggers on 3rd insert.
        cache.cache_vc(make_key("a", "v1"), "v1".to_string());
        cache.cache_vc(make_key("b", "v2"), "v2".to_string());
        cache.cache_vc(make_key("c", "v3"), "v3".to_string());

        // Auto-compaction should have fired.
        assert!(cache.entry_count() <= 2, "should be at or under capacity");
    }

    #[test]
    fn test_compact_cache_returns_eviction_count() {
        let config = CacheConfig {
            max_entries: 1,
            max_memory_bytes: 1024 * 1024,
            ttl_seconds: 3600,
        };
        let mut cache = VcCache::new(config);
        cache.cache_vc(make_key("a", "v1"), "v1".to_string());
        cache.cache_vc(make_key("b", "v2"), "v2".to_string());

        // Force another compaction round.
        let evicted = cache.compact_cache();
        // Should be 0 or more depending on whether auto-compact already ran.
        assert!(cache.entry_count() <= 1, "should respect max_entries after compact");
        // Total evictions should be > 0 across the session.
        assert!(cache.metrics().evictions > 0, "should have evicted at least 1 entry: evicted={evicted}");
    }

    // -------------------------------------------------------------------
    // Clear
    // -------------------------------------------------------------------

    #[test]
    fn test_clear_resets_everything() {
        let mut cache = VcCache::new(default_config());
        let key = make_key("f", "v");
        cache.cache_vc(key.clone(), "v".to_string());
        cache.lookup_vc(&key.content_hash);

        cache.clear();
        assert_eq!(cache.entry_count(), 0);
        assert_eq!(cache.metrics().total_lookups, 0);
        assert_eq!(cache.metrics().hits, 0);
        assert_eq!(cache.metrics().misses, 0);
        assert_eq!(cache.metrics().evictions, 0);
    }

    #[test]
    fn test_entry_count_reflects_state() {
        let mut cache = VcCache::new(default_config());
        assert_eq!(cache.entry_count(), 0);
        cache.cache_vc(make_key("a", "v1"), "v1".to_string());
        assert_eq!(cache.entry_count(), 1);
        cache.cache_vc(make_key("b", "v2"), "v2".to_string());
        assert_eq!(cache.entry_count(), 2);
        cache.clear();
        assert_eq!(cache.entry_count(), 0);
    }
}
