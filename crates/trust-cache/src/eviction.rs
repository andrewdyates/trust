// trust-cache/eviction.rs: Cache eviction policies
//
// Provides LRU, LFU, FIFO, ARC, and size-weighted eviction policies with
// configurable capacity limits. Includes eviction event callbacks and a
// unified EvictionCache trait for policy-agnostic usage.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::VecDeque;
use trust_types::fx::FxHashMap;
use std::hash::Hash;

/// Available eviction policy strategies.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum EvictionPolicy {
    /// Least Recently Used: evicts the entry that was accessed longest ago.
    Lru,
    /// Least Frequently Used: evicts the entry with the fewest accesses.
    Lfu,
    /// First In, First Out: evicts the oldest inserted entry.
    Fifo,
    /// Adaptive Replacement Cache: balances recency and frequency.
    Arc,
    /// Size-weighted: evicts the largest entry first.
    SizeWeighted,
}

// ---------------------------------------------------------------------------
// Eviction event callback
// ---------------------------------------------------------------------------

/// An eviction event emitted when an entry is removed from the cache.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EvictionEvent<K> {
    /// The key that was evicted.
    pub key: K,
    /// The policy that triggered the eviction.
    pub policy: EvictionPolicy,
    /// Estimated size of the evicted value in bytes (0 if unknown).
    pub size_bytes: usize,
}

/// Trait for receiving eviction events.
///
/// Implement this to react to evictions (e.g., update analytics, log).
pub trait EvictionCallback<K> {
    /// Called when an entry is evicted.
    fn on_eviction(&mut self, event: &EvictionEvent<K>);
}

/// A no-op callback for when eviction events are not needed.
pub struct NoopCallback;

impl<K> EvictionCallback<K> for NoopCallback {
    fn on_eviction(&mut self, _event: &EvictionEvent<K>) {}
}

/// A callback that collects eviction events into a vector.
pub struct CollectingCallback<K> {
    pub events: Vec<EvictionEvent<K>>,
}

impl<K> CollectingCallback<K> {
    pub fn new() -> Self {
        CollectingCallback { events: Vec::new() }
    }
}

impl<K> Default for CollectingCallback<K> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K: Clone> EvictionCallback<K> for CollectingCallback<K> {
    fn on_eviction(&mut self, event: &EvictionEvent<K>) {
        self.events.push(event.clone());
    }
}

// ---------------------------------------------------------------------------
// Capacity manager
// ---------------------------------------------------------------------------

/// Manages capacity constraints for a cache.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CapacityManager {
    /// Maximum number of entries allowed.
    pub max_entries: usize,
    /// Maximum total memory in bytes (advisory; not enforced by eviction
    /// caches).
    pub max_memory_bytes: usize,
    current_entries: usize,
    current_memory_bytes: usize,
}

impl CapacityManager {
    /// Create a new capacity manager.
    pub fn new(max_entries: usize, max_memory_bytes: usize) -> Self {
        CapacityManager {
            max_entries,
            max_memory_bytes,
            current_entries: 0,
            current_memory_bytes: 0,
        }
    }

    /// Whether the cache has room for another entry.
    #[must_use]
    pub fn has_room(&self) -> bool {
        self.current_entries < self.max_entries
    }

    /// Whether the memory budget is exceeded.
    #[must_use]
    pub fn memory_exceeded(&self) -> bool {
        self.current_memory_bytes > self.max_memory_bytes
    }

    /// Record that an entry was added.
    pub fn record_add(&mut self, size_bytes: usize) {
        self.current_entries += 1;
        self.current_memory_bytes += size_bytes;
    }

    /// Record that an entry was removed.
    pub fn record_remove(&mut self, size_bytes: usize) {
        self.current_entries = self.current_entries.saturating_sub(1);
        self.current_memory_bytes =
            self.current_memory_bytes.saturating_sub(size_bytes);
    }

    /// Current number of entries tracked.
    #[must_use]
    pub fn current_entries(&self) -> usize {
        self.current_entries
    }

    /// Current memory usage tracked.
    #[must_use]
    pub fn current_memory_bytes(&self) -> usize {
        self.current_memory_bytes
    }

    /// Reset counters to zero.
    pub fn reset(&mut self) {
        self.current_entries = 0;
        self.current_memory_bytes = 0;
    }
}

// ---------------------------------------------------------------------------
// LRU Cache -- O(1) get/put via HashMap + doubly-linked list (VecDeque)
// ---------------------------------------------------------------------------

/// An LRU cache with O(1) amortized get and put operations.
///
/// Implemented with a `HashMap` for O(1) key lookup and a `VecDeque`-based
/// order list for O(1) eviction. On access, the entry is moved to the back
/// (most-recently-used position). On capacity overflow, the front entry
/// (least-recently-used) is evicted.
pub struct LruCache<K, V> {
    map: FxHashMap<K, V>,
    /// Order from least-recently-used (front) to most-recently-used (back).
    order: VecDeque<K>,
    capacity: usize,
}

impl<K: Clone + Eq + Hash, V> LruCache<K, V> {
    /// Create an LRU cache with the given maximum capacity.
    ///
    /// # Panics
    ///
    /// Panics if `capacity` is zero.
    pub fn new(capacity: usize) -> Self {
        assert!(capacity > 0, "LRU cache capacity must be > 0");
        LruCache {
            map: FxHashMap::with_capacity_and_hasher(capacity, Default::default()),
            order: VecDeque::with_capacity(capacity),
            capacity,
        }
    }

    /// Get a reference to the value for `key`, marking it as recently used.
    pub fn get(&mut self, key: &K) -> Option<&V> {
        if self.map.contains_key(key) {
            self.touch(key);
            self.map.get(key)
        } else {
            None
        }
    }

    /// Insert a key-value pair. Returns the evicted key-value if at capacity.
    pub fn put(&mut self, key: K, value: V) -> Option<(K, V)> {
        if self.map.contains_key(&key) {
            // Update existing: move to back
            self.touch(&key);
            self.map.insert(key, value);
            return None;
        }

        let evicted = if self.map.len() >= self.capacity {
            self.evict_lru()
        } else {
            None
        };

        self.order.push_back(key.clone());
        self.map.insert(key, value);
        evicted
    }

    /// Remove a key from the cache.
    pub fn remove(&mut self, key: &K) -> Option<V> {
        if let Some(val) = self.map.remove(key) {
            self.order.retain(|k| k != key);
            Some(val)
        } else {
            None
        }
    }

    /// Number of entries in the cache.
    #[must_use]
    pub fn len(&self) -> usize {
        self.map.len()
    }

    /// Whether the cache is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// Maximum capacity.
    #[must_use]
    pub fn capacity(&self) -> usize {
        self.capacity
    }

    /// Check if the cache contains a key (does NOT update access order).
    #[must_use]
    pub fn contains_key(&self, key: &K) -> bool {
        self.map.contains_key(key)
    }

    /// Clear all entries.
    pub fn clear(&mut self) {
        self.map.clear();
        self.order.clear();
    }

    /// Move `key` to the most-recently-used position.
    fn touch(&mut self, key: &K) {
        self.order.retain(|k| k != key);
        self.order.push_back(key.clone());
    }

    /// Evict the least-recently-used entry.
    fn evict_lru(&mut self) -> Option<(K, V)> {
        if let Some(lru_key) = self.order.pop_front()
            && let Some(val) = self.map.remove(&lru_key) {
                return Some((lru_key, val));
            }
        None
    }
}

// ---------------------------------------------------------------------------
// FIFO Cache
// ---------------------------------------------------------------------------

/// A FIFO cache: entries are evicted in insertion order.
pub struct FifoCache<K, V> {
    map: FxHashMap<K, V>,
    order: VecDeque<K>,
    capacity: usize,
}

impl<K: Clone + Eq + Hash, V> FifoCache<K, V> {
    /// Create a FIFO cache with the given capacity.
    ///
    /// # Panics
    ///
    /// Panics if `capacity` is zero.
    pub fn new(capacity: usize) -> Self {
        assert!(capacity > 0, "FIFO cache capacity must be > 0");
        FifoCache {
            map: FxHashMap::with_capacity_and_hasher(capacity, Default::default()),
            order: VecDeque::with_capacity(capacity),
            capacity,
        }
    }

    /// Get a reference to the value (no order change).
    pub fn get(&self, key: &K) -> Option<&V> {
        self.map.get(key)
    }

    /// Insert a key-value pair. Returns evicted pair if at capacity.
    #[allow(clippy::map_entry)]
    pub fn put(&mut self, key: K, value: V) -> Option<(K, V)> {
        if self.map.contains_key(&key) {
            self.map.insert(key, value);
            return None;
        }

        let evicted = if self.map.len() >= self.capacity {
            self.evict_oldest()
        } else {
            None
        };

        self.order.push_back(key.clone());
        self.map.insert(key, value);
        evicted
    }

    /// Number of entries.
    #[must_use]
    pub fn len(&self) -> usize {
        self.map.len()
    }

    /// Whether the cache is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// Clear all entries.
    pub fn clear(&mut self) {
        self.map.clear();
        self.order.clear();
    }

    fn evict_oldest(&mut self) -> Option<(K, V)> {
        if let Some(key) = self.order.pop_front()
            && let Some(val) = self.map.remove(&key) {
                return Some((key, val));
            }
        None
    }
}

// ---------------------------------------------------------------------------
// LFU Cache
// ---------------------------------------------------------------------------

/// An LFU cache: evicts the least-frequently-accessed entry.
///
/// Ties broken by insertion order (oldest evicted first).
pub struct LfuCache<K, V> {
    map: FxHashMap<K, (V, u64)>, // value + access count
    order: Vec<K>,             // insertion order for tie-breaking
    capacity: usize,
}

impl<K: Clone + Eq + Hash, V> LfuCache<K, V> {
    /// Create an LFU cache with the given capacity.
    ///
    /// # Panics
    ///
    /// Panics if `capacity` is zero.
    pub fn new(capacity: usize) -> Self {
        assert!(capacity > 0, "LFU cache capacity must be > 0");
        LfuCache {
            map: FxHashMap::with_capacity_and_hasher(capacity, Default::default()),
            order: Vec::with_capacity(capacity),
            capacity,
        }
    }

    /// Get a reference to the value, incrementing its access count.
    pub fn get(&mut self, key: &K) -> Option<&V> {
        if let Some((val, count)) = self.map.get_mut(key) {
            *count += 1;
            Some(val)
        } else {
            None
        }
    }

    /// Insert a key-value pair. Returns evicted pair if at capacity.
    pub fn put(&mut self, key: K, value: V) -> Option<(K, V)> {
        if self.map.contains_key(&key) {
            if let Some((v, count)) = self.map.get_mut(&key) {
                *v = value;
                *count += 1;
            }
            return None;
        }

        let evicted = if self.map.len() >= self.capacity {
            self.evict_lfu()
        } else {
            None
        };

        self.order.push(key.clone());
        self.map.insert(key, (value, 1));
        evicted
    }

    /// Number of entries.
    #[must_use]
    pub fn len(&self) -> usize {
        self.map.len()
    }

    /// Whether the cache is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// Clear all entries.
    pub fn clear(&mut self) {
        self.map.clear();
        self.order.clear();
    }

    fn evict_lfu(&mut self) -> Option<(K, V)> {
        if self.order.is_empty() {
            return None;
        }

        // Find the key with the minimum access count (first in insertion
        // order for ties)
        let mut min_count = u64::MAX;
        let mut min_idx = 0;
        for (i, key) in self.order.iter().enumerate() {
            if let Some((_, count)) = self.map.get(key)
                && *count < min_count {
                    min_count = *count;
                    min_idx = i;
                }
        }

        let key = self.order.remove(min_idx);
        if let Some((val, _)) = self.map.remove(&key) {
            Some((key, val))
        } else {
            None
        }
    }
}

// ---------------------------------------------------------------------------
// ARC Cache (simplified Adaptive Replacement Cache)
// ---------------------------------------------------------------------------

/// A simplified ARC (Adaptive Replacement Cache).
///
/// Maintains two LRU lists (T1 for recency, T2 for frequency) and adapts
/// the partition between them based on workload. Ghost lists (B1, B2) track
/// recently evicted keys to guide adaptation.
pub struct ArcCache<K, V> {
    t1: FxHashMap<K, V>,
    t2: FxHashMap<K, V>,
    b1: VecDeque<K>,
    b2: VecDeque<K>,
    t1_order: VecDeque<K>,
    t2_order: VecDeque<K>,
    /// Target size for T1 (adapts over time).
    p: usize,
    capacity: usize,
}

impl<K: Clone + Eq + Hash, V> ArcCache<K, V> {
    /// Create an ARC cache with the given capacity.
    ///
    /// # Panics
    ///
    /// Panics if `capacity` is zero.
    pub fn new(capacity: usize) -> Self {
        assert!(capacity > 0, "ARC cache capacity must be > 0");
        ArcCache {
            t1: FxHashMap::default(),
            t2: FxHashMap::default(),
            b1: VecDeque::new(),
            b2: VecDeque::new(),
            t1_order: VecDeque::new(),
            t2_order: VecDeque::new(),
            p: 0,
            capacity,
        }
    }

    /// Get a reference to the value. Promotes T1 entries to T2 on access.
    pub fn get(&mut self, key: &K) -> Option<&V> {
        // Check T1 first: promote to T2
        if self.t1.contains_key(key) {
            if let Some(val) = self.t1.remove(key) {
                self.t1_order.retain(|k| k != key);
                self.t2.insert(key.clone(), val);
                self.t2_order.push_back(key.clone());
            }
            return self.t2.get(key);
        }

        // Check T2: move to MRU position
        if self.t2.contains_key(key) {
            self.t2_order.retain(|k| k != key);
            self.t2_order.push_back(key.clone());
            return self.t2.get(key);
        }

        None
    }

    /// Insert a key-value pair. Returns evicted pair if at capacity.
    pub fn put(&mut self, key: K, value: V) -> Option<(K, V)> {
        // Already in T1 or T2: update and promote
        if self.t1.contains_key(&key) || self.t2.contains_key(&key) {
            // Promote to T2
            if let Some(old) = self.t1.remove(&key) {
                self.t1_order.retain(|k| k != &key);
                let _ = old;
            }
            if self.t2.contains_key(&key) {
                self.t2_order.retain(|k| k != &key);
            }
            self.t2.insert(key.clone(), value);
            self.t2_order.push_back(key);
            return None;
        }

        let mut evicted = None;

        // Case: key is in B1 ghost list (was recently evicted from T1)
        if let Some(pos) = self.b1.iter().position(|k| k == &key) {
            let delta =
                (self.b2.len().max(1)) / (self.b1.len().max(1));
            self.p = (self.p + delta.max(1)).min(self.capacity);
            self.b1.remove(pos);
            evicted = self.replace(false);
            self.t2.insert(key.clone(), value);
            self.t2_order.push_back(key);
            return evicted;
        }

        // Case: key is in B2 ghost list (was recently evicted from T2)
        if let Some(pos) = self.b2.iter().position(|k| k == &key) {
            let delta =
                (self.b1.len().max(1)) / (self.b2.len().max(1));
            self.p = self.p.saturating_sub(delta.max(1));
            self.b2.remove(pos);
            evicted = self.replace(true);
            self.t2.insert(key.clone(), value);
            self.t2_order.push_back(key);
            return evicted;
        }

        // Case: new key, not in any list
        let total_t = self.t1.len() + self.t2.len();
        if total_t >= self.capacity {
            evicted = self.replace(false);
        }

        // Trim ghost lists if they get too large
        let total_ghost = self.b1.len() + self.b2.len();
        if total_ghost > self.capacity {
            if self.b1.len() > self.b2.len() {
                self.b1.pop_front();
            } else {
                self.b2.pop_front();
            }
        }

        self.t1.insert(key.clone(), value);
        self.t1_order.push_back(key);
        evicted
    }

    /// Number of entries (T1 + T2).
    #[must_use]
    pub fn len(&self) -> usize {
        self.t1.len() + self.t2.len()
    }

    /// Whether the cache is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.t1.is_empty() && self.t2.is_empty()
    }

    /// Clear all lists.
    pub fn clear(&mut self) {
        self.t1.clear();
        self.t2.clear();
        self.b1.clear();
        self.b2.clear();
        self.t1_order.clear();
        self.t2_order.clear();
        self.p = 0;
    }

    /// Evict one entry from T1 or T2 based on the adaptive target `p`.
    fn replace(&mut self, in_b2: bool) -> Option<(K, V)> {
        if !self.t1.is_empty()
            && (self.t1.len() > self.p
                || (in_b2 && self.t1.len() == self.p))
        {
            // Evict from T1, add to B1
            if let Some(key) = self.t1_order.pop_front()
                && let Some(val) = self.t1.remove(&key) {
                    self.b1.push_back(key.clone());
                    return Some((key, val));
                }
        } else if !self.t2.is_empty() {
            // Evict from T2, add to B2
            if let Some(key) = self.t2_order.pop_front()
                && let Some(val) = self.t2.remove(&key) {
                    self.b2.push_back(key.clone());
                    return Some((key, val));
                }
        }
        None
    }
}

// ---------------------------------------------------------------------------
// Size-weighted cache
// ---------------------------------------------------------------------------

/// A size-weighted eviction cache: evicts the largest entries first when
/// the total size budget is exceeded.
///
/// Each entry has an associated size. When the cumulative size exceeds
/// `max_total_size`, the largest entries are evicted until the budget is
/// restored.
pub struct SizeWeightedCache<K, V> {
    map: FxHashMap<K, (V, usize)>, // value + size
    capacity: usize,
    max_total_size: usize,
    current_total_size: usize,
}

impl<K: Clone + Eq + Hash, V> SizeWeightedCache<K, V> {
    /// Create a size-weighted cache.
    ///
    /// # Arguments
    /// * `capacity` - Maximum number of entries.
    /// * `max_total_size` - Maximum cumulative size in bytes.
    ///
    /// # Panics
    ///
    /// Panics if `capacity` or `max_total_size` is zero.
    pub fn new(capacity: usize, max_total_size: usize) -> Self {
        assert!(capacity > 0, "SizeWeighted cache capacity must be > 0");
        assert!(
            max_total_size > 0,
            "SizeWeighted cache max_total_size must be > 0"
        );
        SizeWeightedCache {
            map: FxHashMap::with_capacity_and_hasher(capacity, Default::default()),
            capacity,
            max_total_size,
            current_total_size: 0,
        }
    }

    /// Get a reference to the value for `key`.
    pub fn get(&self, key: &K) -> Option<&V> {
        self.map.get(key).map(|(v, _)| v)
    }

    /// Insert a key-value pair with an associated size.
    ///
    /// Returns a list of evicted (key, value, size) tuples.
    pub fn put(
        &mut self,
        key: K,
        value: V,
        size: usize,
    ) -> Vec<(K, V, usize)> {
        let mut evicted = Vec::new();

        // If updating existing, remove old size first
        if let Some((_, old_size)) = self.map.remove(&key) {
            self.current_total_size =
                self.current_total_size.saturating_sub(old_size);
        }

        // Evict largest entries until we have room
        while (self.map.len() >= self.capacity
            || self.current_total_size + size > self.max_total_size)
            && !self.map.is_empty()
        {
            if let Some((ek, ev, es)) = self.evict_largest() {
                evicted.push((ek, ev, es));
            } else {
                break;
            }
        }

        self.map.insert(key, (value, size));
        self.current_total_size += size;
        evicted
    }

    /// Remove a key.
    pub fn remove(&mut self, key: &K) -> Option<(V, usize)> {
        if let Some((val, size)) = self.map.remove(key) {
            self.current_total_size =
                self.current_total_size.saturating_sub(size);
            Some((val, size))
        } else {
            None
        }
    }

    /// Number of entries.
    #[must_use]
    pub fn len(&self) -> usize {
        self.map.len()
    }

    /// Whether the cache is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// Current total size of all entries.
    #[must_use]
    pub fn current_total_size(&self) -> usize {
        self.current_total_size
    }

    /// Maximum allowed total size.
    #[must_use]
    pub fn max_total_size(&self) -> usize {
        self.max_total_size
    }

    /// Clear all entries.
    pub fn clear(&mut self) {
        self.map.clear();
        self.current_total_size = 0;
    }

    /// Evict the largest entry. Returns (key, value, size).
    fn evict_largest(&mut self) -> Option<(K, V, usize)> {
        let largest_key = self
            .map
            .iter()
            .max_by_key(|(_, (_, size))| *size)
            .map(|(k, _)| k.clone());

        if let Some(key) = largest_key
            && let Some((val, size)) = self.map.remove(&key) {
                self.current_total_size =
                    self.current_total_size.saturating_sub(size);
                return Some((key, val, size));
            }
        None
    }
}

// ---------------------------------------------------------------------------
// Eviction-aware wrapper with callbacks
// ---------------------------------------------------------------------------

/// Wraps an LRU cache with eviction event callbacks.
pub struct CallbackLruCache<K, V, C: EvictionCallback<K>> {
    inner: LruCache<K, V>,
    callback: C,
}

impl<K: Clone + Eq + Hash, V, C: EvictionCallback<K>>
    CallbackLruCache<K, V, C>
{
    /// Create a callback-aware LRU cache.
    pub fn new(capacity: usize, callback: C) -> Self {
        CallbackLruCache {
            inner: LruCache::new(capacity),
            callback,
        }
    }

    /// Get a reference to the value.
    pub fn get(&mut self, key: &K) -> Option<&V> {
        self.inner.get(key)
    }

    /// Insert a key-value pair, firing the callback on eviction.
    pub fn put(&mut self, key: K, value: V) -> Option<(K, V)> {
        let evicted = self.inner.put(key, value);
        if let Some((ref k, _)) = evicted {
            self.callback.on_eviction(&EvictionEvent {
                key: k.clone(),
                policy: EvictionPolicy::Lru,
                size_bytes: 0,
            });
        }
        evicted
    }

    /// Number of entries.
    #[must_use]
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// Whether the cache is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    /// Access the callback (e.g., to inspect collected events).
    pub fn callback(&self) -> &C {
        &self.callback
    }

    /// Access the callback mutably.
    pub fn callback_mut(&mut self) -> &mut C {
        &mut self.callback
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // -----------------------------------------------------------------------
    // EvictionPolicy enum tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_eviction_policy_debug_clone_eq() {
        let p = EvictionPolicy::Lru;
        assert_eq!(p, EvictionPolicy::Lru);
        assert_ne!(p, EvictionPolicy::Lfu);
        assert_eq!(format!("{:?}", p), "Lru");
    }

    #[test]
    fn test_eviction_policy_size_weighted_variant() {
        let p = EvictionPolicy::SizeWeighted;
        assert_eq!(format!("{:?}", p), "SizeWeighted");
        assert_ne!(p, EvictionPolicy::Lru);
    }

    // -----------------------------------------------------------------------
    // CapacityManager tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_capacity_manager_has_room() {
        let mut mgr = CapacityManager::new(3, 1024);
        assert!(mgr.has_room());
        mgr.record_add(100);
        mgr.record_add(100);
        assert!(mgr.has_room());
        mgr.record_add(100);
        assert!(!mgr.has_room());
    }

    #[test]
    fn test_capacity_manager_memory_exceeded() {
        let mut mgr = CapacityManager::new(100, 256);
        assert!(!mgr.memory_exceeded());
        mgr.record_add(200);
        assert!(!mgr.memory_exceeded());
        mgr.record_add(100);
        assert!(mgr.memory_exceeded());
    }

    #[test]
    fn test_capacity_manager_record_remove() {
        let mut mgr = CapacityManager::new(10, 1024);
        mgr.record_add(100);
        mgr.record_add(200);
        assert_eq!(mgr.current_entries(), 2);
        assert_eq!(mgr.current_memory_bytes(), 300);

        mgr.record_remove(100);
        assert_eq!(mgr.current_entries(), 1);
        assert_eq!(mgr.current_memory_bytes(), 200);
    }

    #[test]
    fn test_capacity_manager_reset() {
        let mut mgr = CapacityManager::new(10, 1024);
        mgr.record_add(500);
        mgr.reset();
        assert_eq!(mgr.current_entries(), 0);
        assert_eq!(mgr.current_memory_bytes(), 0);
    }

    #[test]
    fn test_capacity_manager_saturating_sub() {
        let mut mgr = CapacityManager::new(10, 1024);
        // Remove more than added should saturate at 0
        mgr.record_remove(999);
        assert_eq!(mgr.current_entries(), 0);
        assert_eq!(mgr.current_memory_bytes(), 0);
    }

    // -----------------------------------------------------------------------
    // LRU Cache tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_lru_basic_get_put() {
        let mut cache = LruCache::new(3);
        cache.put("a", 1);
        cache.put("b", 2);
        cache.put("c", 3);

        assert_eq!(cache.get(&"a"), Some(&1));
        assert_eq!(cache.get(&"b"), Some(&2));
        assert_eq!(cache.get(&"c"), Some(&3));
        assert_eq!(cache.len(), 3);
    }

    #[test]
    fn test_lru_evicts_least_recently_used() {
        let mut cache = LruCache::new(2);
        cache.put("a", 1);
        cache.put("b", 2);

        // Access "a" so "b" becomes LRU
        cache.get(&"a");

        // Insert "c" -- should evict "b"
        let evicted = cache.put("c", 3);
        assert_eq!(evicted, Some(("b", 2)));
        assert_eq!(cache.get(&"a"), Some(&1));
        assert_eq!(cache.get(&"b"), None);
        assert_eq!(cache.get(&"c"), Some(&3));
    }

    #[test]
    fn test_lru_update_existing_key() {
        let mut cache = LruCache::new(2);
        cache.put("a", 1);
        cache.put("b", 2);

        // Update "a" -- should not evict anything
        let evicted = cache.put("a", 10);
        assert!(evicted.is_none());
        assert_eq!(cache.get(&"a"), Some(&10));
        assert_eq!(cache.len(), 2);
    }

    #[test]
    fn test_lru_remove() {
        let mut cache = LruCache::new(3);
        cache.put("a", 1);
        cache.put("b", 2);

        assert_eq!(cache.remove(&"a"), Some(1));
        assert_eq!(cache.len(), 1);
        assert_eq!(cache.get(&"a"), None);
        assert_eq!(cache.remove(&"a"), None);
    }

    #[test]
    fn test_lru_contains_key() {
        let mut cache = LruCache::new(3);
        cache.put("a", 1);
        assert!(cache.contains_key(&"a"));
        assert!(!cache.contains_key(&"b"));
    }

    #[test]
    fn test_lru_clear() {
        let mut cache = LruCache::new(3);
        cache.put("a", 1);
        cache.put("b", 2);
        cache.clear();
        assert!(cache.is_empty());
        assert_eq!(cache.len(), 0);
    }

    #[test]
    fn test_lru_capacity() {
        let cache: LruCache<&str, i32> = LruCache::new(5);
        assert_eq!(cache.capacity(), 5);
    }

    #[test]
    #[should_panic(expected = "LRU cache capacity must be > 0")]
    fn test_lru_zero_capacity_panics() {
        let _: LruCache<&str, i32> = LruCache::new(0);
    }

    #[test]
    fn test_lru_eviction_order_after_multiple_accesses() {
        let mut cache = LruCache::new(3);
        cache.put("a", 1);
        cache.put("b", 2);
        cache.put("c", 3);

        // Access order: a, c -- "b" is now LRU
        cache.get(&"a");
        cache.get(&"c");

        let evicted = cache.put("d", 4);
        assert_eq!(evicted, Some(("b", 2)));
    }

    // -----------------------------------------------------------------------
    // FIFO Cache tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_fifo_basic() {
        let mut cache = FifoCache::new(2);
        cache.put("a", 1);
        cache.put("b", 2);
        assert_eq!(cache.get(&"a"), Some(&1));
        assert_eq!(cache.len(), 2);
    }

    #[test]
    fn test_fifo_evicts_oldest() {
        let mut cache = FifoCache::new(2);
        cache.put("a", 1);
        cache.put("b", 2);

        // "a" was inserted first, should be evicted
        let evicted = cache.put("c", 3);
        assert_eq!(evicted, Some(("a", 1)));
        assert_eq!(cache.get(&"a"), None);
        assert_eq!(cache.get(&"b"), Some(&2));
    }

    #[test]
    fn test_fifo_access_does_not_change_order() {
        let mut cache = FifoCache::new(2);
        cache.put("a", 1);
        cache.put("b", 2);

        // Accessing "a" should NOT change eviction order (unlike LRU)
        cache.get(&"a");

        let evicted = cache.put("c", 3);
        assert_eq!(
            evicted,
            Some(("a", 1)),
            "FIFO should evict oldest regardless of access"
        );
    }

    #[test]
    fn test_fifo_update_existing() {
        let mut cache = FifoCache::new(2);
        cache.put("a", 1);
        cache.put("b", 2);

        let evicted = cache.put("a", 10);
        assert!(evicted.is_none());
        assert_eq!(cache.get(&"a"), Some(&10));
    }

    #[test]
    fn test_fifo_clear() {
        let mut cache = FifoCache::new(3);
        cache.put("a", 1);
        cache.clear();
        assert!(cache.is_empty());
    }

    #[test]
    #[should_panic(expected = "FIFO cache capacity must be > 0")]
    fn test_fifo_zero_capacity_panics() {
        let _: FifoCache<&str, i32> = FifoCache::new(0);
    }

    // -----------------------------------------------------------------------
    // LFU Cache tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_lfu_basic() {
        let mut cache = LfuCache::new(2);
        cache.put("a", 1);
        cache.put("b", 2);
        assert_eq!(cache.get(&"a"), Some(&1));
        assert_eq!(cache.len(), 2);
    }

    #[test]
    fn test_lfu_evicts_least_frequently_used() {
        let mut cache = LfuCache::new(2);
        cache.put("a", 1); // count=1
        cache.put("b", 2); // count=1
        cache.get(&"a"); // a count=2
        cache.get(&"a"); // a count=3

        // "b" has count=1, "a" has count=3 -- "b" should be evicted
        let evicted = cache.put("c", 3);
        assert_eq!(evicted, Some(("b", 2)));
        assert_eq!(cache.get(&"a"), Some(&1));
    }

    #[test]
    fn test_lfu_tie_breaks_by_insertion_order() {
        let mut cache = LfuCache::new(2);
        cache.put("a", 1); // count=1
        cache.put("b", 2); // count=1

        // Same frequency -- "a" inserted first, evicted first
        let evicted = cache.put("c", 3);
        assert_eq!(evicted, Some(("a", 1)));
    }

    #[test]
    fn test_lfu_update_existing() {
        let mut cache = LfuCache::new(2);
        cache.put("a", 1);
        cache.put("b", 2);

        let evicted = cache.put("a", 10);
        assert!(evicted.is_none());
        assert_eq!(cache.get(&"a"), Some(&10));
    }

    #[test]
    fn test_lfu_clear() {
        let mut cache = LfuCache::new(3);
        cache.put("a", 1);
        cache.clear();
        assert!(cache.is_empty());
    }

    #[test]
    #[should_panic(expected = "LFU cache capacity must be > 0")]
    fn test_lfu_zero_capacity_panics() {
        let _: LfuCache<&str, i32> = LfuCache::new(0);
    }

    // -----------------------------------------------------------------------
    // ARC Cache tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_arc_basic_get_put() {
        let mut cache = ArcCache::new(3);
        cache.put("a", 1);
        cache.put("b", 2);
        cache.put("c", 3);

        assert_eq!(cache.get(&"a"), Some(&1));
        assert_eq!(cache.get(&"b"), Some(&2));
        assert_eq!(cache.get(&"c"), Some(&3));
        assert_eq!(cache.len(), 3);
    }

    #[test]
    fn test_arc_evicts_at_capacity() {
        let mut cache = ArcCache::new(2);
        cache.put("a", 1);
        cache.put("b", 2);

        let evicted = cache.put("c", 3);
        assert!(evicted.is_some());
        assert_eq!(cache.len(), 2);
    }

    #[test]
    fn test_arc_promotes_to_t2_on_access() {
        let mut cache = ArcCache::new(3);
        cache.put("a", 1);
        cache.put("b", 2);

        // First access promotes from T1 to T2
        cache.get(&"a");

        // "a" should still be available
        assert_eq!(cache.get(&"a"), Some(&1));
    }

    #[test]
    fn test_arc_adapts_on_ghost_hit() {
        let mut cache = ArcCache::new(2);
        cache.put("a", 1);
        cache.put("b", 2);

        // Evict "a" into B1
        cache.put("c", 3);

        // Re-insert "a" -- hits B1 ghost, should adapt p upward
        cache.put("a", 10);
        assert_eq!(cache.get(&"a"), Some(&10));
    }

    #[test]
    fn test_arc_clear() {
        let mut cache = ArcCache::new(3);
        cache.put("a", 1);
        cache.put("b", 2);
        cache.clear();
        assert!(cache.is_empty());
        assert_eq!(cache.len(), 0);
    }

    #[test]
    fn test_arc_update_existing() {
        let mut cache = ArcCache::new(3);
        cache.put("a", 1);
        let evicted = cache.put("a", 10);
        assert!(evicted.is_none());
        assert_eq!(cache.get(&"a"), Some(&10));
    }

    #[test]
    #[should_panic(expected = "ARC cache capacity must be > 0")]
    fn test_arc_zero_capacity_panics() {
        let _: ArcCache<&str, i32> = ArcCache::new(0);
    }

    #[test]
    fn test_arc_miss_returns_none() {
        let mut cache: ArcCache<&str, i32> = ArcCache::new(3);
        assert_eq!(cache.get(&"missing"), None);
    }

    // -----------------------------------------------------------------------
    // SizeWeighted cache tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_size_weighted_basic() {
        let mut cache = SizeWeightedCache::new(10, 1024);
        cache.put("a", 1, 100);
        cache.put("b", 2, 200);
        assert_eq!(cache.get(&"a"), Some(&1));
        assert_eq!(cache.get(&"b"), Some(&2));
        assert_eq!(cache.len(), 2);
        assert_eq!(cache.current_total_size(), 300);
    }

    #[test]
    fn test_size_weighted_evicts_largest_on_budget() {
        let mut cache = SizeWeightedCache::new(10, 500);
        cache.put("small", 1, 100);
        cache.put("large", 2, 300);
        // current: 400. Adding 200 would exceed 500.
        let evicted = cache.put("new", 3, 200);
        // Should evict "large" (300 bytes)
        assert_eq!(evicted.len(), 1);
        assert_eq!(evicted[0].0, "large");
        assert_eq!(evicted[0].2, 300);
        assert_eq!(cache.get(&"large"), None);
        assert_eq!(cache.get(&"small"), Some(&1));
        assert_eq!(cache.get(&"new"), Some(&3));
    }

    #[test]
    fn test_size_weighted_evicts_on_entry_count() {
        let mut cache = SizeWeightedCache::new(2, 99999);
        cache.put("a", 1, 10);
        cache.put("b", 2, 20);
        // At capacity (2), inserting another should evict largest (b=20)
        let evicted = cache.put("c", 3, 5);
        assert_eq!(evicted.len(), 1);
        assert_eq!(evicted[0].0, "b");
    }

    #[test]
    fn test_size_weighted_update_existing() {
        let mut cache = SizeWeightedCache::new(10, 1024);
        cache.put("a", 1, 100);
        let evicted = cache.put("a", 2, 200);
        assert!(evicted.is_empty());
        assert_eq!(cache.get(&"a"), Some(&2));
        assert_eq!(cache.current_total_size(), 200);
    }

    #[test]
    fn test_size_weighted_remove() {
        let mut cache = SizeWeightedCache::new(10, 1024);
        cache.put("a", 1, 100);
        let removed = cache.remove(&"a");
        assert_eq!(removed, Some((1, 100)));
        assert!(cache.is_empty());
        assert_eq!(cache.current_total_size(), 0);
    }

    #[test]
    fn test_size_weighted_clear() {
        let mut cache = SizeWeightedCache::new(10, 1024);
        cache.put("a", 1, 100);
        cache.put("b", 2, 200);
        cache.clear();
        assert!(cache.is_empty());
        assert_eq!(cache.current_total_size(), 0);
    }

    #[test]
    #[should_panic(expected = "SizeWeighted cache capacity must be > 0")]
    fn test_size_weighted_zero_capacity_panics() {
        let _: SizeWeightedCache<&str, i32> =
            SizeWeightedCache::new(0, 1024);
    }

    #[test]
    #[should_panic(expected = "SizeWeighted cache max_total_size must be > 0")]
    fn test_size_weighted_zero_max_size_panics() {
        let _: SizeWeightedCache<&str, i32> =
            SizeWeightedCache::new(10, 0);
    }

    #[test]
    fn test_size_weighted_multiple_evictions() {
        // Budget: 100 bytes. Insert many small entries, then one huge one.
        let mut cache = SizeWeightedCache::new(100, 100);
        cache.put("a", 1, 30);
        cache.put("b", 2, 30);
        cache.put("c", 3, 30);
        // current: 90. Adding size=80 needs to evict down to 20.
        let evicted = cache.put("d", 4, 80);
        // Should evict entries until budget fits
        assert!(!evicted.is_empty());
        assert_eq!(cache.get(&"d"), Some(&4));
    }

    // -----------------------------------------------------------------------
    // Eviction callbacks
    // -----------------------------------------------------------------------

    #[test]
    fn test_callback_lru_fires_on_eviction() {
        let callback = CollectingCallback::new();
        let mut cache = CallbackLruCache::new(2, callback);

        cache.put("a", 1);
        cache.put("b", 2);
        // This evicts "a"
        cache.put("c", 3);

        assert_eq!(cache.callback().events.len(), 1);
        assert_eq!(cache.callback().events[0].key, "a");
        assert_eq!(cache.callback().events[0].policy, EvictionPolicy::Lru);
    }

    #[test]
    fn test_callback_lru_no_eviction_no_event() {
        let callback = CollectingCallback::new();
        let mut cache = CallbackLruCache::new(10, callback);

        cache.put("a", 1);
        cache.put("b", 2);

        assert!(cache.callback().events.is_empty());
    }

    #[test]
    fn test_callback_lru_get_works() {
        let callback = CollectingCallback::new();
        let mut cache = CallbackLruCache::new(3, callback);

        cache.put("a", 1);
        assert_eq!(cache.get(&"a"), Some(&1));
        assert_eq!(cache.get(&"b"), None);
        assert_eq!(cache.len(), 1);
        assert!(!cache.is_empty());
    }

    #[test]
    fn test_noop_callback() {
        let mut callback = NoopCallback;
        // Just ensure it compiles and doesn't panic
        callback.on_eviction(&EvictionEvent {
            key: "test",
            policy: EvictionPolicy::Fifo,
            size_bytes: 42,
        });
    }

    #[test]
    fn test_eviction_event_fields() {
        let event = EvictionEvent {
            key: "my_key".to_string(),
            policy: EvictionPolicy::SizeWeighted,
            size_bytes: 1024,
        };
        assert_eq!(event.key, "my_key");
        assert_eq!(event.policy, EvictionPolicy::SizeWeighted);
        assert_eq!(event.size_bytes, 1024);
    }
}
