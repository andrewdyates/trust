// trust-cache/distributed.rs: Distributed cache protocol for sharing verification results
//
// Provides a protocol for coordinating cache state across multiple machines.
// Uses consistent hashing to map keys to responsible nodes, replication for
// fault tolerance, and last-writer-wins conflict resolution.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;
use std::hash::{DefaultHasher, Hash, Hasher};

use crate::CacheEntry;

// ---------------------------------------------------------------------------
// Cache node
// ---------------------------------------------------------------------------

/// A participant in the distributed cache protocol.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CacheNode {
    /// Unique identifier for this node.
    pub id: String,
    /// Network address (e.g., "192.168.1.10:9100").
    pub address: String,
}

impl CacheNode {
    /// Create a new cache node.
    #[must_use]
    pub fn new(id: impl Into<String>, address: impl Into<String>) -> Self {
        CacheNode { id: id.into(), address: address.into() }
    }
}

// ---------------------------------------------------------------------------
// Cache messages
// ---------------------------------------------------------------------------

/// Messages exchanged between distributed cache nodes.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum CacheMessage {
    /// Request a cache entry by key.
    Lookup { key: String, from: String },
    /// Response: entry was found.
    Found { key: String, entry: CacheEntry },
    /// Response: entry was not found.
    NotFound { key: String },
    /// Invalidate a cached entry across all nodes.
    Invalidate { key: String, from: String },
    /// Store (replicate) an entry to a peer node.
    Store { key: String, entry: CacheEntry, from: String },
}

// ---------------------------------------------------------------------------
// Distributed statistics
// ---------------------------------------------------------------------------

/// Statistics for distributed cache operations.
///
/// Tracks local vs network hits to measure cache locality effectiveness.
/// Uses u64 counters (no f64 fields) so Eq can be derived.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct DistributedStats {
    /// Number of lookups satisfied from local storage.
    pub local_hits: u64,
    /// Number of lookups satisfied by a remote node.
    pub network_hits: u64,
    /// Number of lookups that missed everywhere.
    pub total_misses: u64,
    /// Number of replication operations performed.
    pub replications: u64,
    /// Number of conflict resolutions performed.
    pub conflicts_resolved: u64,
    /// Number of invalidation messages sent.
    pub invalidations_sent: u64,
}

impl DistributedStats {
    /// Total number of lookups performed.
    #[must_use]
    pub fn total_lookups(&self) -> u64 {
        self.local_hits + self.network_hits + self.total_misses
    }

    /// Local hit rate as parts per thousand (to avoid f64).
    #[must_use]
    pub fn local_hit_rate_permille(&self) -> u64 {
        let total = self.total_lookups();
        if total == 0 { 0 } else { (self.local_hits * 1000) / total }
    }

    /// Network hit rate as parts per thousand.
    #[must_use]
    pub fn network_hit_rate_permille(&self) -> u64 {
        let total = self.total_lookups();
        if total == 0 { 0 } else { (self.network_hits * 1000) / total }
    }
}

// ---------------------------------------------------------------------------
// Consistent hashing
// ---------------------------------------------------------------------------

/// Number of virtual nodes per physical node on the hash ring.
const DEFAULT_VIRTUAL_NODES: usize = 150;

/// Map a cache key to the index of its responsible node using consistent hashing.
///
/// Returns an index into the `nodes` slice. Uses a virtual-node ring for
/// even distribution. Returns `None` if `nodes` is empty.
#[must_use]
pub fn consistent_hash(key: &str, nodes: &[CacheNode]) -> Option<usize> {
    if nodes.is_empty() {
        return None;
    }
    if nodes.len() == 1 {
        return Some(0);
    }

    // Build a ring of (hash_position, node_index) sorted by position.
    let mut ring: Vec<(u64, usize)> = Vec::with_capacity(nodes.len() * DEFAULT_VIRTUAL_NODES);
    for (idx, node) in nodes.iter().enumerate() {
        for vn in 0..DEFAULT_VIRTUAL_NODES {
            let mut hasher = DefaultHasher::new();
            node.id.hash(&mut hasher);
            vn.hash(&mut hasher);
            ring.push((hasher.finish(), idx));
        }
    }
    ring.sort_by_key(|(pos, _)| *pos);

    // Hash the key and find the next node clockwise on the ring.
    let mut hasher = DefaultHasher::new();
    key.hash(&mut hasher);
    let key_hash = hasher.finish();

    let node_idx = match ring.binary_search_by_key(&key_hash, |(pos, _)| *pos) {
        Ok(i) => ring[i].1,
        Err(i) => {
            if i < ring.len() { ring[i].1 } else { ring[0].1 }
        }
    };

    Some(node_idx)
}

// ---------------------------------------------------------------------------
// Distributed cache
// ---------------------------------------------------------------------------

/// Coordinates cache lookups, stores, and invalidations across a set of nodes.
///
/// This is a protocol-level abstraction: it determines *which* messages to send,
/// but does not handle actual network I/O. Callers inspect the `pending_messages`
/// queue and deliver them via their own transport.
pub struct DistributedCache {
    /// The local node identity.
    local_node: CacheNode,
    /// All known nodes in the cluster (including local).
    nodes: Vec<CacheNode>,
    /// Local cache entries.
    local_entries: FxHashMap<String, CacheEntry>,
    /// Messages waiting to be sent to other nodes.
    pending_messages: Vec<(CacheNode, CacheMessage)>,
    /// Number of backup copies per entry.
    replication_factor: usize,
    /// Accumulated statistics.
    stats: DistributedStats,
}

impl DistributedCache {
    /// Create a new distributed cache coordinator.
    ///
    /// `local_node` identifies this machine. `nodes` is the full cluster
    /// membership (must include `local_node`). `replication_factor` controls
    /// how many backup copies are made (0 = no replication).
    pub fn new(
        local_node: CacheNode,
        nodes: Vec<CacheNode>,
        replication_factor: usize,
    ) -> Self {
        DistributedCache {
            local_node,
            nodes,
            local_entries: FxHashMap::default(),
            pending_messages: Vec::new(),
            replication_factor,
            stats: DistributedStats::default(),
        }
    }

    /// Look up a key. Returns `Some` if found locally; otherwise enqueues
    /// a `Lookup` message to the responsible node and returns `None`.
    pub fn lookup(&mut self, key: &str) -> Option<&CacheEntry> {
        if self.local_entries.contains_key(key) {
            self.stats.local_hits += 1;
            return self.local_entries.get(key);
        }

        // Determine responsible node and enqueue lookup.
        if let Some(idx) = consistent_hash(key, &self.nodes) {
            let target = &self.nodes[idx];
            if target != &self.local_node {
                self.pending_messages.push((
                    target.clone(),
                    CacheMessage::Lookup {
                        key: key.to_string(),
                        from: self.local_node.id.clone(),
                    },
                ));
            } else {
                // We are the responsible node and don't have it.
                self.stats.total_misses += 1;
            }
        }

        None
    }

    /// Store an entry locally and enqueue replication messages.
    pub fn store(&mut self, key: &str, entry: CacheEntry) {
        self.local_entries.insert(key.to_string(), entry.clone());
        self.replicate(key, &entry);
    }

    /// Invalidate a key locally and broadcast invalidation to all peers.
    pub fn invalidate(&mut self, key: &str) {
        self.local_entries.remove(key);
        for node in &self.nodes {
            if node != &self.local_node {
                self.pending_messages.push((
                    node.clone(),
                    CacheMessage::Invalidate {
                        key: key.to_string(),
                        from: self.local_node.id.clone(),
                    },
                ));
                self.stats.invalidations_sent += 1;
            }
        }
    }

    /// Handle an incoming message from a peer.
    ///
    /// Returns any response message that should be sent back.
    pub fn handle_message(&mut self, msg: CacheMessage) -> Option<(CacheNode, CacheMessage)> {
        match msg {
            CacheMessage::Lookup { key, from } => {
                let sender = self.find_node(&from)?.clone();
                if let Some(entry) = self.local_entries.get(&key) {
                    Some((sender, CacheMessage::Found { key, entry: entry.clone() }))
                } else {
                    Some((sender, CacheMessage::NotFound { key }))
                }
            }
            CacheMessage::Found { key, entry } => {
                self.stats.network_hits += 1;
                // Cache locally for future lookups.
                self.local_entries.insert(key, entry);
                None
            }
            CacheMessage::NotFound { .. } => {
                self.stats.total_misses += 1;
                None
            }
            CacheMessage::Invalidate { key, .. } => {
                self.local_entries.remove(&key);
                None
            }
            CacheMessage::Store { key, entry, .. } => {
                // Apply conflict resolution: keep the newer entry.
                self.resolve_conflict(&key, entry);
                None
            }
        }
    }

    /// Drain all pending outbound messages.
    pub fn drain_pending(&mut self) -> Vec<(CacheNode, CacheMessage)> {
        std::mem::take(&mut self.pending_messages)
    }

    /// Number of entries stored locally.
    #[must_use]
    pub fn local_entry_count(&self) -> usize {
        self.local_entries.len()
    }

    /// Number of nodes in the cluster.
    #[must_use]
    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }

    /// Current statistics snapshot.
    #[must_use]
    pub fn stats(&self) -> &DistributedStats {
        &self.stats
    }

    /// The local node.
    #[must_use]
    pub fn local_node(&self) -> &CacheNode {
        &self.local_node
    }

    /// Enqueue replication messages to backup nodes.
    ///
    /// Selects the next `replication_factor` nodes clockwise from the primary
    /// on the consistent hash ring.
    pub(crate) fn replicate(&mut self, key: &str, entry: &CacheEntry) {
        if self.replication_factor == 0 || self.nodes.len() <= 1 {
            return;
        }

        let primary_idx = match consistent_hash(key, &self.nodes) {
            Some(idx) => idx,
            None => return,
        };

        let count = self.replication_factor.min(self.nodes.len() - 1);
        for offset in 1..=count {
            let replica_idx = (primary_idx + offset) % self.nodes.len();
            let target = &self.nodes[replica_idx];
            if target != &self.local_node {
                self.pending_messages.push((
                    target.clone(),
                    CacheMessage::Store {
                        key: key.to_string(),
                        entry: entry.clone(),
                        from: self.local_node.id.clone(),
                    },
                ));
                self.stats.replications += 1;
            }
        }
    }

    /// Resolve a conflict between an existing local entry and an incoming one.
    ///
    /// Uses last-writer-wins: the entry with the higher `cached_at` timestamp
    /// is kept. If timestamps are equal, the incoming entry wins (crdt-style
    /// bias toward propagation).
    pub(crate) fn resolve_conflict(&mut self, key: &str, incoming: CacheEntry) {
        if let Some(existing) = self.local_entries.get(key) {
            if incoming.cached_at >= existing.cached_at {
                self.local_entries.insert(key.to_string(), incoming);
                self.stats.conflicts_resolved += 1;
            }
            // else: existing is newer, keep it (still counts as a resolution).
        } else {
            // No conflict — just store.
            self.local_entries.insert(key.to_string(), incoming);
        }
    }

    /// Find a node by its ID.
    fn find_node(&self, id: &str) -> Option<&CacheNode> {
        self.nodes.iter().find(|n| n.id == id)
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use trust_types::FunctionVerdict;

    use super::*;

    fn sample_entry(hash: &str, timestamp: u64) -> CacheEntry {
        CacheEntry {
            content_hash: hash.to_string(),
            verdict: FunctionVerdict::Verified,
            total_obligations: 1,
            proved: 1,
            failed: 0,
            unknown: 0,
            runtime_checked: 0,
            cached_at: timestamp,
            spec_hash: String::new(),
        }
    }

    fn make_nodes(n: usize) -> Vec<CacheNode> {
        (0..n)
            .map(|i| CacheNode::new(format!("node-{i}"), format!("127.0.0.1:{}", 9100 + i)))
            .collect()
    }

    fn make_cache(local_idx: usize, node_count: usize, repl: usize) -> DistributedCache {
        let nodes = make_nodes(node_count);
        let local = nodes[local_idx].clone();
        DistributedCache::new(local, nodes, repl)
    }

    // -----------------------------------------------------------------------
    // consistent_hash tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_consistent_hash_empty_nodes_returns_none() {
        assert_eq!(consistent_hash("key", &[]), None);
    }

    #[test]
    fn test_consistent_hash_single_node_returns_zero() {
        let nodes = make_nodes(1);
        assert_eq!(consistent_hash("any_key", &nodes), Some(0));
        assert_eq!(consistent_hash("another_key", &nodes), Some(0));
    }

    #[test]
    fn test_consistent_hash_deterministic() {
        let nodes = make_nodes(5);
        let idx1 = consistent_hash("my_function::foo", &nodes);
        let idx2 = consistent_hash("my_function::foo", &nodes);
        assert_eq!(idx1, idx2, "same key must map to same node");
    }

    #[test]
    fn test_consistent_hash_distributes_across_nodes() {
        let nodes = make_nodes(4);
        let mut seen = FxHashSet::default();
        for i in 0..200 {
            if let Some(idx) = consistent_hash(&format!("key_{i}"), &nodes) {
                seen.insert(idx);
            }
        }
        assert!(seen.len() >= 2, "keys should distribute across multiple nodes, got {}", seen.len());
    }

    #[test]
    fn test_consistent_hash_valid_indices() {
        let nodes = make_nodes(4);
        for i in 0..100 {
            let idx = consistent_hash(&format!("k{i}"), &nodes).unwrap();
            assert!(idx < 4, "index must be within bounds");
        }
    }

    // -----------------------------------------------------------------------
    // CacheNode tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_cache_node_equality() {
        let n1 = CacheNode::new("a", "addr1");
        let n2 = CacheNode::new("a", "addr1");
        let n3 = CacheNode::new("b", "addr2");
        assert_eq!(n1, n2);
        assert_ne!(n1, n3);
    }

    // -----------------------------------------------------------------------
    // DistributedCache local operations
    // -----------------------------------------------------------------------

    #[test]
    fn test_store_and_local_lookup() {
        let mut cache = make_cache(0, 3, 0);
        let entry = sample_entry("h1", 1000);
        cache.store("func::foo", entry.clone());

        let result = cache.lookup("func::foo");
        assert_eq!(result, Some(&entry));
        assert_eq!(cache.stats().local_hits, 1);
    }

    #[test]
    fn test_lookup_miss_enqueues_message() {
        let mut cache = make_cache(0, 3, 0);
        let result = cache.lookup("func::missing");
        assert!(result.is_none());

        let pending = cache.drain_pending();
        // Either enqueued a Lookup message or counted a miss (if we are the responsible node).
        let total_actions = pending.len() as u64 + cache.stats().total_misses;
        assert!(total_actions >= 1, "should either enqueue Lookup or record miss");
    }

    #[test]
    fn test_invalidate_removes_local_and_broadcasts() {
        let mut cache = make_cache(0, 3, 0);
        cache.store("func::bar", sample_entry("h2", 500));
        assert_eq!(cache.local_entry_count(), 1);

        cache.invalidate("func::bar");
        assert_eq!(cache.local_entry_count(), 0);

        let pending = cache.drain_pending();
        // Should send invalidation to the 2 other nodes.
        assert_eq!(pending.len(), 2, "should broadcast invalidation to 2 peers");
        for (_, msg) in &pending {
            assert!(matches!(msg, CacheMessage::Invalidate { .. }));
        }
    }

    // -----------------------------------------------------------------------
    // Message handling
    // -----------------------------------------------------------------------

    #[test]
    fn test_handle_lookup_found() {
        let mut cache = make_cache(0, 3, 0);
        cache.store("func::x", sample_entry("hx", 100));

        let response = cache.handle_message(CacheMessage::Lookup {
            key: "func::x".to_string(),
            from: "node-1".to_string(),
        });

        assert!(response.is_some());
        let (target, msg) = response.unwrap();
        assert_eq!(target.id, "node-1");
        assert!(matches!(msg, CacheMessage::Found { .. }));
    }

    #[test]
    fn test_handle_lookup_not_found() {
        let mut cache = make_cache(0, 3, 0);

        let response = cache.handle_message(CacheMessage::Lookup {
            key: "func::missing".to_string(),
            from: "node-1".to_string(),
        });

        assert!(response.is_some());
        let (_, msg) = response.unwrap();
        assert!(matches!(msg, CacheMessage::NotFound { .. }));
    }

    #[test]
    fn test_handle_found_caches_locally() {
        let mut cache = make_cache(0, 3, 0);
        let entry = sample_entry("hf", 200);

        cache.handle_message(CacheMessage::Found {
            key: "func::remote".to_string(),
            entry: entry.clone(),
        });

        assert_eq!(cache.local_entry_count(), 1);
        assert_eq!(cache.stats().network_hits, 1);
        // Should now be findable locally.
        let result = cache.lookup("func::remote");
        assert_eq!(result, Some(&entry));
    }

    #[test]
    fn test_handle_invalidate_removes_entry() {
        let mut cache = make_cache(0, 3, 0);
        cache.store("func::del", sample_entry("hd", 100));

        cache.handle_message(CacheMessage::Invalidate {
            key: "func::del".to_string(),
            from: "node-2".to_string(),
        });

        assert_eq!(cache.local_entry_count(), 0);
    }

    // -----------------------------------------------------------------------
    // Replication
    // -----------------------------------------------------------------------

    #[test]
    fn test_replicate_with_factor_zero_no_messages() {
        let mut cache = make_cache(0, 3, 0);
        cache.store("func::norep", sample_entry("h", 100));
        let pending = cache.drain_pending();
        assert!(pending.is_empty(), "replication_factor=0 should produce no replication messages");
    }

    #[test]
    fn test_replicate_sends_to_backup_nodes() {
        let mut cache = make_cache(0, 3, 1);
        cache.store("func::rep", sample_entry("hr", 100));

        let pending = cache.drain_pending();
        // With replication_factor=1, should send Store to 1 backup node
        // (but only if that backup isn't the local node).
        let store_msgs: Vec<_> = pending
            .iter()
            .filter(|(_, m)| matches!(m, CacheMessage::Store { .. }))
            .collect();
        assert!(
            !store_msgs.is_empty(),
            "replication_factor=1 should send at least one Store message"
        );
        assert_eq!(cache.stats().replications, store_msgs.len() as u64);
    }

    // -----------------------------------------------------------------------
    // Conflict resolution
    // -----------------------------------------------------------------------

    #[test]
    fn test_resolve_conflict_newer_wins() {
        let mut cache = make_cache(0, 3, 0);
        let older = sample_entry("old", 100);
        let newer = sample_entry("new", 200);
        cache.store("func::conflict", older);

        cache.resolve_conflict("func::conflict", newer.clone());

        let result = cache.lookup("func::conflict").unwrap();
        assert_eq!(result.content_hash, "new", "newer entry should win");
        assert_eq!(cache.stats().conflicts_resolved, 1);
    }

    #[test]
    fn test_resolve_conflict_older_does_not_overwrite() {
        let mut cache = make_cache(0, 3, 0);
        let newer = sample_entry("new", 200);
        let older = sample_entry("old", 100);
        cache.store("func::keep", newer);

        cache.resolve_conflict("func::keep", older);

        let result = cache.lookup("func::keep").unwrap();
        assert_eq!(result.content_hash, "new", "existing newer entry should be kept");
    }

    #[test]
    fn test_resolve_conflict_equal_timestamp_incoming_wins() {
        let mut cache = make_cache(0, 3, 0);
        let existing = sample_entry("existing", 100);
        let incoming = sample_entry("incoming", 100);
        cache.store("func::tie", existing);

        cache.resolve_conflict("func::tie", incoming.clone());

        let result = cache.lookup("func::tie").unwrap();
        assert_eq!(result.content_hash, "incoming", "on tie, incoming should win");
    }

    #[test]
    fn test_resolve_conflict_no_existing_just_stores() {
        let mut cache = make_cache(0, 3, 0);
        let entry = sample_entry("fresh", 100);

        cache.resolve_conflict("func::new", entry.clone());

        assert_eq!(cache.local_entry_count(), 1);
        let result = cache.lookup("func::new").unwrap();
        assert_eq!(result.content_hash, "fresh");
    }

    // -----------------------------------------------------------------------
    // Statistics
    // -----------------------------------------------------------------------

    #[test]
    fn test_stats_initial_state() {
        let cache = make_cache(0, 3, 0);
        let stats = cache.stats();
        assert_eq!(stats.local_hits, 0);
        assert_eq!(stats.network_hits, 0);
        assert_eq!(stats.total_misses, 0);
        assert_eq!(stats.total_lookups(), 0);
    }

    #[test]
    fn test_stats_hit_rates() {
        let stats = DistributedStats {
            local_hits: 7,
            network_hits: 2,
            total_misses: 1,
            ..Default::default()
        };

        assert_eq!(stats.total_lookups(), 10);
        assert_eq!(stats.local_hit_rate_permille(), 700);
        assert_eq!(stats.network_hit_rate_permille(), 200);
    }

    #[test]
    fn test_stats_zero_lookups_rate_is_zero() {
        let stats = DistributedStats::default();
        assert_eq!(stats.local_hit_rate_permille(), 0);
        assert_eq!(stats.network_hit_rate_permille(), 0);
    }

    // -----------------------------------------------------------------------
    // Integration: store + replicate + handle on peer
    // -----------------------------------------------------------------------

    #[test]
    fn test_end_to_end_store_replicate_receive() {
        // Node 0 stores and replicates to node 1.
        let mut node0 = make_cache(0, 3, 2);
        let entry = sample_entry("e2e", 999);
        node0.store("func::e2e", entry.clone());

        let pending = node0.drain_pending();
        assert!(!pending.is_empty(), "should have replication messages");

        // Simulate delivering one Store message to node 1.
        let mut node1 = make_cache(1, 3, 0);
        for (target, msg) in pending {
            if target.id == "node-1" {
                node1.handle_message(msg);
            }
        }

        // Node 1 should now have the entry.
        let result = node1.lookup("func::e2e");
        assert!(result.is_some(), "node-1 should have received the replicated entry");
        assert_eq!(result.unwrap().content_hash, "e2e");
    }

    #[test]
    fn test_node_count_and_local_node() {
        let cache = make_cache(2, 5, 0);
        assert_eq!(cache.node_count(), 5);
        assert_eq!(cache.local_node().id, "node-2");
    }
}
