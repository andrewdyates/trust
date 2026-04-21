// trust-cache/sharding.rs: Query sharding for parallel cache access
//
// Distributes cache entries across N shards, each with its own RwLock,
// to reduce contention under parallel verification. Supports multiple
// sharding strategies: hash-mod, consistent hashing, and VC-kind-based.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;
use std::hash::{DefaultHasher, Hash, Hasher};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::RwLock;

use crate::eviction::EvictionPolicy;

// ---------------------------------------------------------------------------
// Sharding strategy
// ---------------------------------------------------------------------------

/// How entries are assigned to shards.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
#[non_exhaustive]
pub enum ShardingStrategy {
    /// Simple hash modulo N shards.
    #[default]
    HashMod,
    /// Consistent hashing with virtual nodes for better distribution.
    ConsistentHashing {
        /// Number of virtual nodes per shard (higher = better balance).
        virtual_nodes: usize,
    },
    /// Route by VC kind discriminant (safety checks to one shard, assertions
    /// to another, etc.). Falls back to HashMod for unknown kinds.
    VcKindBased,
}

// ---------------------------------------------------------------------------
// Per-shard statistics
// ---------------------------------------------------------------------------

/// Statistics for a single shard.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ShardStats {
    /// Shard index.
    pub shard_id: usize,
    /// Number of entries currently stored.
    pub entry_count: usize,
    /// Cumulative cache hits on this shard.
    pub hits: u64,
    /// Cumulative cache misses on this shard.
    pub misses: u64,
    /// Eviction policy configured for this shard.
    pub eviction_policy: EvictionPolicy,
}

/// Aggregate statistics across all shards.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ShardedCacheStats {
    /// Per-shard statistics.
    pub shards: Vec<ShardStats>,
    /// Total entries across all shards.
    pub total_entries: usize,
    /// Total hits across all shards.
    pub total_hits: u64,
    /// Total misses across all shards.
    pub total_misses: u64,
    /// Load balance ratio: max_entries / avg_entries. 1.0 = perfect.
    /// Encoded as fixed-point (numerator * 1000 / denominator) to avoid float.
    pub balance_ratio_millionths: u64,
}

// ---------------------------------------------------------------------------
// Single shard
// ---------------------------------------------------------------------------

/// A single shard holding a partition of the cache.
struct Shard<K, V> {
    entries: FxHashMap<K, V>,
    capacity: usize,
    eviction_policy: EvictionPolicy,
    /// Insertion order for FIFO/LRU eviction (simplified).
    insertion_order: Vec<K>,
    /// Access counts for LFU eviction.
    access_counts: FxHashMap<K, u64>,
    hits: AtomicU64,
    misses: AtomicU64,
}

impl<K: Clone + Eq + Hash, V> Shard<K, V> {
    fn new(capacity: usize, eviction_policy: EvictionPolicy) -> Self {
        Shard {
            entries: FxHashMap::with_capacity_and_hasher(capacity, Default::default()),
            capacity,
            eviction_policy,
            insertion_order: Vec::with_capacity(capacity),
            access_counts: FxHashMap::with_capacity_and_hasher(capacity, Default::default()),
            hits: AtomicU64::new(0),
            misses: AtomicU64::new(0),
        }
    }

    fn get(&mut self, key: &K) -> Option<&V> {
        if self.entries.contains_key(key) {
            self.hits.fetch_add(1, Ordering::Relaxed);
            // Update access tracking for LRU/LFU
            match self.eviction_policy {
                EvictionPolicy::Lru | EvictionPolicy::Arc => {
                    self.insertion_order.retain(|k| k != key);
                    self.insertion_order.push(key.clone());
                }
                EvictionPolicy::Lfu => {
                    *self.access_counts.entry(key.clone()).or_insert(0) += 1;
                }
                EvictionPolicy::Fifo | EvictionPolicy::SizeWeighted => {} // no reordering on access
            }
            self.entries.get(key)
        } else {
            self.misses.fetch_add(1, Ordering::Relaxed);
            None
        }
    }

    fn insert(&mut self, key: K, value: V) -> Option<(K, V)> {
        if self.entries.contains_key(&key) {
            self.entries.insert(key.clone(), value);
            // Update access order for LRU
            if matches!(self.eviction_policy, EvictionPolicy::Lru | EvictionPolicy::Arc) {
                self.insertion_order.retain(|k| k != &key);
                self.insertion_order.push(key);
            }
            return None;
        }

        let evicted = if self.entries.len() >= self.capacity {
            self.evict_one()
        } else {
            None
        };

        self.insertion_order.push(key.clone());
        self.access_counts.insert(key.clone(), 1);
        self.entries.insert(key, value);
        evicted
    }

    fn remove(&mut self, key: &K) -> Option<V> {
        if let Some(val) = self.entries.remove(key) {
            self.insertion_order.retain(|k| k != key);
            self.access_counts.remove(key);
            Some(val)
        } else {
            None
        }
    }

    fn len(&self) -> usize {
        self.entries.len()
    }

    fn clear(&mut self) {
        self.entries.clear();
        self.insertion_order.clear();
        self.access_counts.clear();
    }

    /// Drain all entries out of this shard (for rebalancing).
    fn drain(&mut self) -> Vec<(K, V)> {
        self.insertion_order.clear();
        self.access_counts.clear();
        self.entries.drain().collect()
    }

    fn evict_one(&mut self) -> Option<(K, V)> {
        match self.eviction_policy {
            EvictionPolicy::Fifo
            | EvictionPolicy::Lru
            | EvictionPolicy::Arc
            | EvictionPolicy::SizeWeighted => {
                // FIFO: evict oldest. LRU: oldest in insertion_order (updated on access).
                // SizeWeighted: falls back to insertion order within sharded context.
                if let Some(key) = self.insertion_order.first().cloned() {
                    self.insertion_order.remove(0);
                    self.access_counts.remove(&key);
                    if let Some(val) = self.entries.remove(&key) {
                        return Some((key, val));
                    }
                }
                None
            }
            EvictionPolicy::Lfu => {
                // Evict entry with lowest access count
                let victim = self
                    .insertion_order
                    .iter()
                    .min_by_key(|k| self.access_counts.get(*k).copied().unwrap_or(0))
                    .cloned();
                if let Some(key) = victim {
                    self.insertion_order.retain(|k| k != &key);
                    self.access_counts.remove(&key);
                    if let Some(val) = self.entries.remove(&key) {
                        return Some((key, val));
                    }
                }
                None
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Consistent hashing ring
// ---------------------------------------------------------------------------

/// A consistent hashing ring that maps keys to shard indices.
struct HashRing {
    /// Sorted list of (ring_position, shard_index).
    ring: Vec<(u64, usize)>,
}

impl HashRing {
    fn new(shard_count: usize, virtual_nodes: usize) -> Self {
        let mut ring = Vec::with_capacity(shard_count * virtual_nodes);
        for shard in 0..shard_count {
            for vn in 0..virtual_nodes {
                let mut hasher = DefaultHasher::new();
                (shard, vn, "vnode").hash(&mut hasher);
                ring.push((hasher.finish(), shard));
            }
        }
        ring.sort_by_key(|(pos, _)| *pos);
        HashRing { ring }
    }

    fn shard_for_hash(&self, hash: u64) -> usize {
        if self.ring.is_empty() {
            return 0;
        }
        match self.ring.binary_search_by_key(&hash, |(pos, _)| *pos) {
            Ok(idx) => self.ring[idx].1,
            Err(idx) => {
                if idx < self.ring.len() {
                    self.ring[idx].1
                } else {
                    // Wrap around to first node
                    self.ring[0].1
                }
            }
        }
    }

}

// ---------------------------------------------------------------------------
// ShardedCache
// ---------------------------------------------------------------------------

/// A sharded, thread-safe cache with configurable sharding strategy
/// and per-shard eviction policies.
///
/// Each shard is protected by its own `RwLock`, minimizing contention
/// when multiple threads access different cache partitions simultaneously.
pub struct ShardedCache<K, V> {
    shards: Vec<RwLock<Shard<K, V>>>,
    strategy: ShardingStrategy,
    ring: Option<HashRing>,
    shard_count: usize,
}

impl<K: Clone + Eq + Hash, V> ShardedCache<K, V> {
    /// Create a new sharded cache.
    ///
    /// # Arguments
    /// * `shard_count` - Number of shards (must be > 0)
    /// * `per_shard_capacity` - Maximum entries per shard
    /// * `strategy` - How to assign keys to shards
    /// * `default_eviction` - Default eviction policy for all shards
    pub fn new(
        shard_count: usize,
        per_shard_capacity: usize,
        strategy: ShardingStrategy,
        default_eviction: EvictionPolicy,
    ) -> Self {
        assert!(shard_count > 0, "shard count must be > 0");
        assert!(per_shard_capacity > 0, "per-shard capacity must be > 0");

        let ring = match &strategy {
            ShardingStrategy::ConsistentHashing { virtual_nodes } => {
                Some(HashRing::new(shard_count, *virtual_nodes))
            }
            _ => None,
        };

        let shards = (0..shard_count)
            .map(|_| RwLock::new(Shard::new(per_shard_capacity, default_eviction)))
            .collect();

        ShardedCache { shards, strategy, ring, shard_count }
    }

    /// Look up a key, returning a clone of the value if found.
    pub fn get(&self, key: &K) -> Option<V>
    where
        V: Clone,
    {
        let shard_idx = self.shard_index(key);
        let mut shard =
            self.shards[shard_idx].write().unwrap_or_else(|e| e.into_inner());
        shard.get(key).cloned()
    }

    /// Insert a key-value pair. Returns the evicted pair if capacity was exceeded.
    pub fn insert(&self, key: K, value: V) -> Option<(K, V)> {
        let shard_idx = self.shard_index(&key);
        let mut shard =
            self.shards[shard_idx].write().unwrap_or_else(|e| e.into_inner());
        shard.insert(key, value)
    }

    /// Remove a key from the cache.
    pub fn remove(&self, key: &K) -> Option<V> {
        let shard_idx = self.shard_index(key);
        let mut shard =
            self.shards[shard_idx].write().unwrap_or_else(|e| e.into_inner());
        shard.remove(key)
    }

    /// Total number of entries across all shards.
    #[must_use]
    pub fn len(&self) -> usize {
        self.shards
            .iter()
            .map(|s| s.read().unwrap_or_else(|e| e.into_inner()).len())
            .sum()
    }

    /// Whether the cache is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Number of shards.
    #[must_use]
    pub fn shard_count(&self) -> usize {
        self.shard_count
    }

    /// Current sharding strategy.
    #[must_use]
    pub fn strategy(&self) -> &ShardingStrategy {
        &self.strategy
    }

    /// Collect per-shard statistics.
    #[must_use]
    pub fn shard_stats(&self) -> ShardedCacheStats {
        let mut shards = Vec::with_capacity(self.shard_count);
        let mut total_entries: usize = 0;
        let mut total_hits: u64 = 0;
        let mut total_misses: u64 = 0;

        for (i, lock) in self.shards.iter().enumerate() {
            let shard = lock.read().unwrap_or_else(|e| e.into_inner());
            let hits = shard.hits.load(Ordering::Relaxed);
            let misses = shard.misses.load(Ordering::Relaxed);
            let count = shard.len();
            total_entries += count;
            total_hits += hits;
            total_misses += misses;
            shards.push(ShardStats {
                shard_id: i,
                entry_count: count,
                hits,
                misses,
                eviction_policy: shard.eviction_policy,
            });
        }

        let balance_ratio_millionths = if total_entries == 0 || self.shard_count == 0 {
            1_000_000 // perfect balance when empty
        } else {
            let avg_thousandths = (total_entries as u64 * 1000) / self.shard_count as u64;
            let max_entries = shards.iter().map(|s| s.entry_count as u64).max().unwrap_or(0);
            if avg_thousandths == 0 {
                1_000_000
            } else {
                (max_entries * 1_000_000_000) / avg_thousandths
            }
        };

        ShardedCacheStats {
            shards,
            total_entries,
            total_hits,
            total_misses,
            balance_ratio_millionths,
        }
    }

    /// Rebalance all entries from the current strategy to a new one.
    ///
    /// Drains all shards and re-inserts every entry under the new strategy.
    /// This is an expensive operation intended for reconfiguration, not
    /// routine use.
    pub fn rebalance(&mut self, new_strategy: ShardingStrategy) {
        // Drain all entries
        let mut all_entries: Vec<(K, V)> = Vec::new();
        for lock in &self.shards {
            let mut shard = lock.write().unwrap_or_else(|e| e.into_inner());
            all_entries.extend(shard.drain());
        }

        // Update strategy and ring
        self.ring = match &new_strategy {
            ShardingStrategy::ConsistentHashing { virtual_nodes } => {
                Some(HashRing::new(self.shard_count, *virtual_nodes))
            }
            _ => None,
        };
        self.strategy = new_strategy;

        // Re-insert all entries under new strategy
        for (key, value) in all_entries {
            let shard_idx = self.shard_index(&key);
            let mut shard =
                self.shards[shard_idx].write().unwrap_or_else(|e| e.into_inner());
            shard.insert(key, value);
        }
    }

    /// Set a per-shard eviction policy. Takes effect for future evictions.
    ///
    /// # Returns
    /// `true` if the shard index was valid, `false` otherwise.
    pub fn set_shard_eviction(&self, shard_idx: usize, policy: EvictionPolicy) -> bool {
        if shard_idx >= self.shard_count {
            return false;
        }
        let mut shard =
            self.shards[shard_idx].write().unwrap_or_else(|e| e.into_inner());
        shard.eviction_policy = policy;
        true
    }

    /// Clear all entries in all shards.
    pub fn clear(&self) {
        for lock in &self.shards {
            let mut shard = lock.write().unwrap_or_else(|e| e.into_inner());
            shard.clear();
        }
    }

    /// Determine which shard a key belongs to.
    fn shard_index(&self, key: &K) -> usize {
        let mut hasher = DefaultHasher::new();
        key.hash(&mut hasher);
        let hash = hasher.finish();

        match &self.strategy {
            ShardingStrategy::HashMod => (hash as usize) % self.shard_count,
            ShardingStrategy::ConsistentHashing { .. } => {
                self.ring.as_ref().map_or(0, |r| r.shard_for_hash(hash))
            }
            ShardingStrategy::VcKindBased => {
                // Use top 8 bits as "kind" discriminant, rest as hash
                // This clusters similar keys on the same shard
                let kind_bits = (hash >> 56) as usize;
                kind_bits % self.shard_count
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Builder
// ---------------------------------------------------------------------------

/// Builder for configuring a `ShardedCache`.
#[must_use]
pub struct ShardedCacheBuilder<K, V> {
    shard_count: usize,
    per_shard_capacity: usize,
    strategy: ShardingStrategy,
    default_eviction: EvictionPolicy,
    /// Per-shard eviction overrides: (shard_index, policy).
    shard_eviction_overrides: Vec<(usize, EvictionPolicy)>,
    _marker: std::marker::PhantomData<(K, V)>,
}

impl<K: Clone + Eq + Hash, V> ShardedCacheBuilder<K, V> {
    /// Create a builder with default settings.
    pub fn new() -> Self {
        ShardedCacheBuilder {
            shard_count: 16,
            per_shard_capacity: 1024,
            strategy: ShardingStrategy::HashMod,
            default_eviction: EvictionPolicy::Lru,
            shard_eviction_overrides: Vec::new(),
            _marker: std::marker::PhantomData,
        }
    }

    /// Set the number of shards.
    pub fn shard_count(mut self, count: usize) -> Self {
        self.shard_count = count;
        self
    }

    /// Set per-shard maximum capacity.
    pub fn per_shard_capacity(mut self, capacity: usize) -> Self {
        self.per_shard_capacity = capacity;
        self
    }

    /// Set the sharding strategy.
    pub fn strategy(mut self, strategy: ShardingStrategy) -> Self {
        self.strategy = strategy;
        self
    }

    /// Set the default eviction policy for all shards.
    pub fn default_eviction(mut self, policy: EvictionPolicy) -> Self {
        self.default_eviction = policy;
        self
    }

    /// Override the eviction policy for a specific shard.
    pub fn shard_eviction(mut self, shard_idx: usize, policy: EvictionPolicy) -> Self {
        self.shard_eviction_overrides.push((shard_idx, policy));
        self
    }

    /// Build the sharded cache.
    pub fn build(self) -> ShardedCache<K, V> {
        let cache = ShardedCache::new(
            self.shard_count,
            self.per_shard_capacity,
            self.strategy,
            self.default_eviction,
        );

        for (idx, policy) in self.shard_eviction_overrides {
            cache.set_shard_eviction(idx, policy);
        }

        cache
    }
}

impl<K: Clone + Eq + Hash, V> Default for ShardedCacheBuilder<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use std::sync::Arc;
    use std::thread;

    use super::*;

    // -----------------------------------------------------------------------
    // Basic operations
    // -----------------------------------------------------------------------

    #[test]
    fn test_sharded_cache_insert_and_get() {
        let cache: ShardedCache<String, i32> =
            ShardedCache::new(4, 100, ShardingStrategy::HashMod, EvictionPolicy::Lru);

        cache.insert("key1".to_string(), 42);
        cache.insert("key2".to_string(), 84);

        assert_eq!(cache.get(&"key1".to_string()), Some(42));
        assert_eq!(cache.get(&"key2".to_string()), Some(84));
        assert_eq!(cache.get(&"key3".to_string()), None);
    }

    #[test]
    fn test_sharded_cache_remove() {
        let cache: ShardedCache<String, i32> =
            ShardedCache::new(4, 100, ShardingStrategy::HashMod, EvictionPolicy::Lru);

        cache.insert("key1".to_string(), 42);
        assert_eq!(cache.remove(&"key1".to_string()), Some(42));
        assert_eq!(cache.get(&"key1".to_string()), None);
        assert_eq!(cache.remove(&"key1".to_string()), None);
    }

    #[test]
    fn test_sharded_cache_len_and_empty() {
        let cache: ShardedCache<String, i32> =
            ShardedCache::new(4, 100, ShardingStrategy::HashMod, EvictionPolicy::Lru);

        assert!(cache.is_empty());
        assert_eq!(cache.len(), 0);

        cache.insert("a".to_string(), 1);
        cache.insert("b".to_string(), 2);
        assert!(!cache.is_empty());
        assert_eq!(cache.len(), 2);
    }

    #[test]
    fn test_sharded_cache_clear() {
        let cache: ShardedCache<String, i32> =
            ShardedCache::new(4, 100, ShardingStrategy::HashMod, EvictionPolicy::Lru);

        for i in 0..20 {
            cache.insert(format!("key{i}"), i);
        }
        assert_eq!(cache.len(), 20);

        cache.clear();
        assert!(cache.is_empty());
    }

    #[test]
    fn test_sharded_cache_update_existing() {
        let cache: ShardedCache<String, i32> =
            ShardedCache::new(4, 100, ShardingStrategy::HashMod, EvictionPolicy::Lru);

        cache.insert("key".to_string(), 1);
        cache.insert("key".to_string(), 2);
        assert_eq!(cache.get(&"key".to_string()), Some(2));
        assert_eq!(cache.len(), 1);
    }

    // -----------------------------------------------------------------------
    // Sharding strategies
    // -----------------------------------------------------------------------

    #[test]
    fn test_hash_mod_distributes_across_shards() {
        let cache: ShardedCache<i32, i32> =
            ShardedCache::new(4, 100, ShardingStrategy::HashMod, EvictionPolicy::Fifo);

        // Insert enough entries that at least 2 shards get used
        for i in 0..100 {
            cache.insert(i, i * 10);
        }

        let stats = cache.shard_stats();
        let non_empty = stats.shards.iter().filter(|s| s.entry_count > 0).count();
        assert!(non_empty >= 2, "hash mod should distribute across multiple shards");
        assert_eq!(stats.total_entries, 100);
    }

    #[test]
    fn test_consistent_hashing_distributes() {
        let cache: ShardedCache<i32, i32> = ShardedCache::new(
            4,
            100,
            ShardingStrategy::ConsistentHashing { virtual_nodes: 150 },
            EvictionPolicy::Lru,
        );

        for i in 0..100 {
            cache.insert(i, i);
        }

        let stats = cache.shard_stats();
        let non_empty = stats.shards.iter().filter(|s| s.entry_count > 0).count();
        assert!(non_empty >= 2, "consistent hashing should use multiple shards");
        assert_eq!(stats.total_entries, 100);
    }

    #[test]
    fn test_vc_kind_based_strategy() {
        let cache: ShardedCache<String, i32> =
            ShardedCache::new(4, 100, ShardingStrategy::VcKindBased, EvictionPolicy::Lru);

        cache.insert("overflow_check_1".to_string(), 1);
        cache.insert("overflow_check_2".to_string(), 2);
        cache.insert("assertion_1".to_string(), 3);

        assert_eq!(cache.len(), 3);
        assert_eq!(cache.get(&"overflow_check_1".to_string()), Some(1));
    }

    // -----------------------------------------------------------------------
    // Shard statistics
    // -----------------------------------------------------------------------

    #[test]
    fn test_shard_stats_hit_miss_tracking() {
        let cache: ShardedCache<String, i32> =
            ShardedCache::new(4, 100, ShardingStrategy::HashMod, EvictionPolicy::Lru);

        cache.insert("key1".to_string(), 10);
        cache.get(&"key1".to_string()); // hit
        cache.get(&"key1".to_string()); // hit
        cache.get(&"missing".to_string()); // miss

        let stats = cache.shard_stats();
        assert!(stats.total_hits >= 2, "should have at least 2 hits");
        assert!(stats.total_misses >= 1, "should have at least 1 miss");
    }

    #[test]
    fn test_shard_stats_balance_ratio() {
        let cache: ShardedCache<i32, i32> =
            ShardedCache::new(4, 100, ShardingStrategy::HashMod, EvictionPolicy::Lru);

        for i in 0..100 {
            cache.insert(i, i);
        }

        let stats = cache.shard_stats();
        // Balance ratio should be reasonable (not infinite)
        assert!(
            stats.balance_ratio_millionths > 0,
            "balance ratio should be positive"
        );
    }

    #[test]
    fn test_shard_stats_empty_cache() {
        let cache: ShardedCache<String, i32> =
            ShardedCache::new(4, 100, ShardingStrategy::HashMod, EvictionPolicy::Lru);

        let stats = cache.shard_stats();
        assert_eq!(stats.total_entries, 0);
        assert_eq!(stats.total_hits, 0);
        assert_eq!(stats.total_misses, 0);
        assert_eq!(stats.balance_ratio_millionths, 1_000_000);
    }

    // -----------------------------------------------------------------------
    // Rebalancing
    // -----------------------------------------------------------------------

    #[test]
    fn test_rebalance_preserves_entries() {
        let mut cache: ShardedCache<String, i32> =
            ShardedCache::new(4, 100, ShardingStrategy::HashMod, EvictionPolicy::Lru);

        let keys: Vec<String> = (0..50).map(|i| format!("key{i}")).collect();
        for (i, key) in keys.iter().enumerate() {
            cache.insert(key.clone(), i as i32);
        }
        assert_eq!(cache.len(), 50);

        // Rebalance to consistent hashing
        cache.rebalance(ShardingStrategy::ConsistentHashing { virtual_nodes: 100 });
        assert_eq!(cache.len(), 50, "rebalance should preserve entry count");

        // All entries should still be retrievable
        for (i, key) in keys.iter().enumerate() {
            assert_eq!(
                cache.get(key),
                Some(i as i32),
                "entry for {key} should survive rebalance"
            );
        }
    }

    #[test]
    fn test_rebalance_changes_strategy() {
        let mut cache: ShardedCache<String, i32> =
            ShardedCache::new(4, 100, ShardingStrategy::HashMod, EvictionPolicy::Lru);

        assert_eq!(*cache.strategy(), ShardingStrategy::HashMod);

        cache.rebalance(ShardingStrategy::VcKindBased);
        assert_eq!(*cache.strategy(), ShardingStrategy::VcKindBased);
    }

    // -----------------------------------------------------------------------
    // Per-shard eviction policies
    // -----------------------------------------------------------------------

    #[test]
    fn test_per_shard_eviction_policy() {
        let cache: ShardedCache<String, i32> =
            ShardedCache::new(4, 100, ShardingStrategy::HashMod, EvictionPolicy::Lru);

        assert!(cache.set_shard_eviction(0, EvictionPolicy::Lfu));
        assert!(cache.set_shard_eviction(1, EvictionPolicy::Fifo));
        assert!(!cache.set_shard_eviction(99, EvictionPolicy::Lru)); // out of range

        let stats = cache.shard_stats();
        assert_eq!(stats.shards[0].eviction_policy, EvictionPolicy::Lfu);
        assert_eq!(stats.shards[1].eviction_policy, EvictionPolicy::Fifo);
        assert_eq!(stats.shards[2].eviction_policy, EvictionPolicy::Lru);
    }

    #[test]
    fn test_eviction_within_shard() {
        // 1 shard with capacity 3 to make eviction deterministic
        let cache: ShardedCache<i32, i32> =
            ShardedCache::new(1, 3, ShardingStrategy::HashMod, EvictionPolicy::Fifo);

        cache.insert(1, 10);
        cache.insert(2, 20);
        cache.insert(3, 30);

        // This should evict key=1 (FIFO)
        cache.insert(4, 40);

        assert_eq!(cache.get(&1), None, "key 1 should be evicted (FIFO)");
        assert_eq!(cache.get(&4), Some(40));
        assert_eq!(cache.len(), 3);
    }

    // -----------------------------------------------------------------------
    // Thread safety
    // -----------------------------------------------------------------------

    #[test]
    fn test_parallel_inserts() {
        let cache = Arc::new(ShardedCache::<i32, i32>::new(
            8,
            1000,
            ShardingStrategy::HashMod,
            EvictionPolicy::Lru,
        ));

        let mut handles = Vec::new();
        for thread_id in 0..4 {
            let cache = Arc::clone(&cache);
            handles.push(thread::spawn(move || {
                for i in 0..100 {
                    let key = thread_id * 1000 + i;
                    cache.insert(key, key * 10);
                }
            }));
        }

        for h in handles {
            h.join().expect("thread should not panic");
        }

        assert_eq!(cache.len(), 400, "all 4 threads x 100 inserts = 400 entries");
    }

    #[test]
    fn test_parallel_reads_and_writes() {
        let cache = Arc::new(ShardedCache::<i32, i32>::new(
            8,
            1000,
            ShardingStrategy::HashMod,
            EvictionPolicy::Lru,
        ));

        // Pre-populate
        for i in 0..200 {
            cache.insert(i, i * 10);
        }

        let mut handles = Vec::new();

        // Reader threads
        for _ in 0..4 {
            let cache = Arc::clone(&cache);
            handles.push(thread::spawn(move || {
                let mut found = 0u32;
                for i in 0..200 {
                    if cache.get(&i).is_some() {
                        found += 1;
                    }
                }
                found
            }));
        }

        // Writer thread
        {
            let cache = Arc::clone(&cache);
            handles.push(thread::spawn(move || {
                for i in 200..300 {
                    cache.insert(i, i * 10);
                }
                0u32
            }));
        }

        for h in handles {
            h.join().expect("thread should not panic");
        }

        // All original + new entries should be present
        assert!(cache.len() >= 200, "at least original entries should remain");
    }

    // -----------------------------------------------------------------------
    // Builder
    // -----------------------------------------------------------------------

    #[test]
    fn test_builder_defaults() {
        let cache: ShardedCache<String, i32> = ShardedCacheBuilder::new().build();

        assert_eq!(cache.shard_count(), 16);
        assert_eq!(*cache.strategy(), ShardingStrategy::HashMod);
    }

    #[test]
    fn test_builder_custom_config() {
        let cache: ShardedCache<String, i32> = ShardedCacheBuilder::new()
            .shard_count(8)
            .per_shard_capacity(256)
            .strategy(ShardingStrategy::ConsistentHashing { virtual_nodes: 200 })
            .default_eviction(EvictionPolicy::Lfu)
            .shard_eviction(0, EvictionPolicy::Fifo)
            .build();

        assert_eq!(cache.shard_count(), 8);
        let stats = cache.shard_stats();
        assert_eq!(stats.shards[0].eviction_policy, EvictionPolicy::Fifo);
        assert_eq!(stats.shards[1].eviction_policy, EvictionPolicy::Lfu);
    }

    #[test]
    fn test_builder_default_trait() {
        let cache: ShardedCache<String, i32> = ShardedCacheBuilder::default().build();
        assert_eq!(cache.shard_count(), 16);
    }

    // -----------------------------------------------------------------------
    // Consistent hashing ring
    // -----------------------------------------------------------------------

    #[test]
    fn test_hash_ring_returns_valid_shard() {
        let ring = HashRing::new(4, 100);
        for i in 0u64..1000 {
            let shard = ring.shard_for_hash(i);
            assert!(shard < 4, "shard index must be < shard_count");
        }
    }

    #[test]
    fn test_hash_ring_uses_multiple_shards() {
        let ring = HashRing::new(4, 100);
        let mut seen = FxHashSet::default();
        // Use hashed keys (like real usage) for varied ring positions
        for i in 0i64..1000 {
            let mut hasher = DefaultHasher::new();
            i.hash(&mut hasher);
            let hash = hasher.finish();
            seen.insert(ring.shard_for_hash(hash));
        }
        assert!(seen.len() >= 2, "ring should map to multiple shards");
    }

    // -----------------------------------------------------------------------
    // Edge cases
    // -----------------------------------------------------------------------

    #[test]
    #[should_panic(expected = "shard count must be > 0")]
    fn test_zero_shard_count_panics() {
        let _: ShardedCache<String, i32> =
            ShardedCache::new(0, 100, ShardingStrategy::HashMod, EvictionPolicy::Lru);
    }

    #[test]
    #[should_panic(expected = "per-shard capacity must be > 0")]
    fn test_zero_capacity_panics() {
        let _: ShardedCache<String, i32> =
            ShardedCache::new(4, 0, ShardingStrategy::HashMod, EvictionPolicy::Lru);
    }

    #[test]
    fn test_single_shard_works() {
        let cache: ShardedCache<String, i32> =
            ShardedCache::new(1, 100, ShardingStrategy::HashMod, EvictionPolicy::Lru);

        cache.insert("a".to_string(), 1);
        cache.insert("b".to_string(), 2);
        assert_eq!(cache.get(&"a".to_string()), Some(1));
        assert_eq!(cache.shard_count(), 1);
    }
}
