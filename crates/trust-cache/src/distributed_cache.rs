// trust-cache/distributed_cache.rs: Distributed verification caching protocol
//
// Provides a higher-level distributed cache protocol for sharing verification
// results between machines. Nodes join/leave dynamically, entries are routed
// via consistent hashing, and configurable consistency levels control replication.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;
use std::hash::{DefaultHasher, Hash, Hasher};

use thiserror::Error;

// ---------------------------------------------------------------------------
// Error type
// ---------------------------------------------------------------------------

/// Errors from distributed cache protocol operations.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum CacheProtocolError {
    /// Attempted to add a node when the cluster is at maximum capacity.
    #[error("node limit reached: max {max} nodes")]
    NodeLimitReached {
        /// The configured maximum number of nodes.
        max: usize,
    },
    /// Attempted to add a node with a duplicate ID.
    #[error("duplicate node id: {id}")]
    DuplicateNode {
        /// The duplicate node ID.
        id: String,
    },
}

// ---------------------------------------------------------------------------
// Consistency level
// ---------------------------------------------------------------------------

/// Controls how many nodes must acknowledge a write before it is considered durable.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum ConsistencyLevel {
    /// Acknowledged by one node (fastest, least durable).
    One,
    /// Acknowledged by a quorum (majority) of replica nodes.
    Quorum,
    /// Acknowledged by all replica nodes (slowest, most durable).
    All,
}

// ---------------------------------------------------------------------------
// CacheNode
// ---------------------------------------------------------------------------

/// A machine participating in the distributed cache cluster.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CacheNode {
    /// Unique identifier for this node.
    pub node_id: String,
    /// Network address (e.g., "192.168.1.10:9100").
    pub address: String,
    /// Maximum number of entries this node can hold.
    pub capacity: usize,
    /// Current number of entries on this node.
    pub entries_count: usize,
}

impl CacheNode {
    /// Create a new cache node.
    #[must_use]
    pub fn new(
        node_id: impl Into<String>,
        address: impl Into<String>,
        capacity: usize,
    ) -> Self {
        CacheNode {
            node_id: node_id.into(),
            address: address.into(),
            capacity,
            entries_count: 0,
        }
    }
}

// ---------------------------------------------------------------------------
// DistributedEntry
// ---------------------------------------------------------------------------

/// A cache entry with provenance metadata for distributed operation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DistributedEntry {
    /// Cache lookup key (typically a function def_path or content hash).
    pub key: String,
    /// SHA-256 content hash of the verified function.
    pub content_hash: String,
    /// Verification verdict (e.g., "Verified", "HasViolations").
    pub verdict: String,
    /// Unix timestamp (seconds since epoch) when this entry was created.
    pub timestamp: u64,
    /// ID of the node that originally produced this entry.
    pub node_origin: String,
}

// ---------------------------------------------------------------------------
// DistributedConfig
// ---------------------------------------------------------------------------

/// Configuration for the distributed cache protocol.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DistributedConfig {
    /// Number of copies of each entry to maintain across nodes.
    pub replication_factor: usize,
    /// Consistency level for write acknowledgments.
    pub consistency_level: ConsistencyLevel,
    /// Time-to-live for entries in seconds (0 = no expiration).
    pub ttl_seconds: u64,
    /// Maximum number of nodes allowed in the cluster.
    pub max_nodes: usize,
}

impl Default for DistributedConfig {
    fn default() -> Self {
        DistributedConfig {
            replication_factor: 2,
            consistency_level: ConsistencyLevel::Quorum,
            ttl_seconds: 3600,
            max_nodes: 64,
        }
    }
}

// ---------------------------------------------------------------------------
// CacheStats
// ---------------------------------------------------------------------------

/// Summary statistics for the distributed cache protocol.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct CacheStats {
    /// Total number of entries across all nodes (as seen by this coordinator).
    pub total_entries: usize,
    /// Number of nodes in the cluster.
    pub total_nodes: usize,
}

// ---------------------------------------------------------------------------
// Consistent hashing (standalone function)
// ---------------------------------------------------------------------------

/// Map a key to a bucket index using consistent hashing.
///
/// Returns an index in `0..num_buckets`. Panics if `num_buckets` is 0.
#[must_use]
pub fn consistent_hash(key: &str, num_buckets: usize) -> usize {
    assert!(num_buckets > 0, "num_buckets must be > 0");
    let mut hasher = DefaultHasher::new();
    key.hash(&mut hasher);
    (hasher.finish() as usize) % num_buckets
}

// ---------------------------------------------------------------------------
// CacheProtocol
// ---------------------------------------------------------------------------

/// Coordinates distributed cache operations across a cluster of nodes.
///
/// This is a protocol-level abstraction: it decides which nodes should store
/// which entries, but does not perform actual network I/O.
pub struct CacheProtocol {
    config: DistributedConfig,
    nodes: Vec<CacheNode>,
    entries: FxHashMap<String, DistributedEntry>,
}

impl CacheProtocol {
    /// Create a new protocol coordinator with the given configuration.
    #[must_use]
    pub fn new(config: DistributedConfig) -> Self {
        CacheProtocol {
            config,
            nodes: Vec::new(),
            entries: FxHashMap::default(),
        }
    }

    /// Add a node to the cluster.
    ///
    /// Returns an error if the cluster is at maximum capacity or the node ID
    /// is already present.
    pub fn add_node(&mut self, node: CacheNode) -> Result<(), CacheProtocolError> {
        if self.nodes.len() >= self.config.max_nodes {
            return Err(CacheProtocolError::NodeLimitReached { max: self.config.max_nodes });
        }
        if self.nodes.iter().any(|n| n.node_id == node.node_id) {
            return Err(CacheProtocolError::DuplicateNode { id: node.node_id });
        }
        self.nodes.push(node);
        Ok(())
    }

    /// Remove a node by ID. Returns `true` if the node was found and removed.
    pub fn remove_node(&mut self, node_id: &str) -> bool {
        let before = self.nodes.len();
        self.nodes.retain(|n| n.node_id != node_id);
        self.nodes.len() < before
    }

    /// Number of nodes currently in the cluster.
    #[must_use]
    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }

    /// Look up an entry by key.
    #[must_use]
    pub fn lookup(&self, key: &str) -> Option<&DistributedEntry> {
        self.entries.get(key)
    }

    /// Store an entry and return the IDs of nodes selected for replication.
    pub fn store(&mut self, entry: DistributedEntry) -> Vec<String> {
        let replica_ids = self.select_nodes(&entry.key)
            .iter()
            .map(|n| n.node_id.clone())
            .collect::<Vec<_>>();
        self.entries.insert(entry.key.clone(), entry);
        replica_ids
    }

    /// Select the nodes responsible for storing a given key.
    ///
    /// Uses consistent hashing to pick a primary node, then selects up to
    /// `replication_factor` additional nodes clockwise on the ring.
    #[must_use]
    pub fn select_nodes(&self, key: &str) -> Vec<&CacheNode> {
        if self.nodes.is_empty() {
            return Vec::new();
        }

        let primary_idx = consistent_hash(key, self.nodes.len());
        let count = (self.config.replication_factor + 1).min(self.nodes.len());
        let mut selected = Vec::with_capacity(count);

        for offset in 0..count {
            let idx = (primary_idx + offset) % self.nodes.len();
            selected.push(&self.nodes[idx]);
        }

        selected
    }

    /// Invalidate an entry by key. Returns the number of replica nodes that
    /// would need to be notified (0 if the key was not found).
    pub fn invalidate(&mut self, key: &str) -> usize {
        if self.entries.remove(key).is_some() {
            // The number of nodes that had a copy is the replication count.
            if self.nodes.is_empty() {
                0
            } else {
                (self.config.replication_factor + 1).min(self.nodes.len())
            }
        } else {
            0
        }
    }

    /// Get summary statistics for the protocol state.
    #[must_use]
    pub fn stats(&self) -> CacheStats {
        CacheStats {
            total_entries: self.entries.len(),
            total_nodes: self.nodes.len(),
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn default_config() -> DistributedConfig {
        DistributedConfig {
            replication_factor: 2,
            consistency_level: ConsistencyLevel::Quorum,
            ttl_seconds: 3600,
            max_nodes: 10,
        }
    }

    fn make_node(id: &str) -> CacheNode {
        CacheNode::new(id, format!("127.0.0.1:{id}"), 1000)
    }

    fn make_entry(key: &str, origin: &str) -> DistributedEntry {
        DistributedEntry {
            key: key.to_string(),
            content_hash: format!("hash_{key}"),
            verdict: "Verified".to_string(),
            timestamp: 1000,
            node_origin: origin.to_string(),
        }
    }

    // -----------------------------------------------------------------------
    // consistent_hash tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_consistent_hash_deterministic() {
        let a = consistent_hash("func::foo", 10);
        let b = consistent_hash("func::foo", 10);
        assert_eq!(a, b, "same key must produce same bucket");
    }

    #[test]
    fn test_consistent_hash_within_bounds() {
        for i in 0..100 {
            let bucket = consistent_hash(&format!("key_{i}"), 7);
            assert!(bucket < 7, "bucket {bucket} out of range for 7 buckets");
        }
    }

    #[test]
    fn test_consistent_hash_single_bucket() {
        assert_eq!(consistent_hash("anything", 1), 0);
    }

    #[test]
    #[should_panic(expected = "num_buckets must be > 0")]
    fn test_consistent_hash_zero_buckets_panics() {
        let _ = consistent_hash("key", 0);
    }

    #[test]
    fn test_consistent_hash_distributes() {
        let mut seen = FxHashSet::default();
        for i in 0..200 {
            seen.insert(consistent_hash(&format!("k{i}"), 5));
        }
        assert!(seen.len() >= 3, "should distribute across multiple buckets, got {}", seen.len());
    }

    // -----------------------------------------------------------------------
    // CacheNode tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_cache_node_new() {
        let node = CacheNode::new("n1", "addr:9100", 500);
        assert_eq!(node.node_id, "n1");
        assert_eq!(node.address, "addr:9100");
        assert_eq!(node.capacity, 500);
        assert_eq!(node.entries_count, 0);
    }

    // -----------------------------------------------------------------------
    // CacheProtocol add/remove node tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_add_node_success() {
        let mut proto = CacheProtocol::new(default_config());
        proto.add_node(make_node("a")).expect("should add node");
        assert_eq!(proto.node_count(), 1);
    }

    #[test]
    fn test_add_duplicate_node_fails() {
        let mut proto = CacheProtocol::new(default_config());
        proto.add_node(make_node("a")).unwrap();
        let err = proto.add_node(make_node("a")).unwrap_err();
        assert!(matches!(err, CacheProtocolError::DuplicateNode { .. }));
    }

    #[test]
    fn test_add_node_limit_reached() {
        let config = DistributedConfig { max_nodes: 2, ..default_config() };
        let mut proto = CacheProtocol::new(config);
        proto.add_node(make_node("a")).unwrap();
        proto.add_node(make_node("b")).unwrap();
        let err = proto.add_node(make_node("c")).unwrap_err();
        assert!(matches!(err, CacheProtocolError::NodeLimitReached { max: 2 }));
    }

    #[test]
    fn test_remove_node_existing() {
        let mut proto = CacheProtocol::new(default_config());
        proto.add_node(make_node("x")).unwrap();
        assert!(proto.remove_node("x"));
        assert_eq!(proto.node_count(), 0);
    }

    #[test]
    fn test_remove_node_nonexistent() {
        let mut proto = CacheProtocol::new(default_config());
        assert!(!proto.remove_node("ghost"));
    }

    // -----------------------------------------------------------------------
    // Store and lookup tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_store_and_lookup() {
        let mut proto = CacheProtocol::new(default_config());
        proto.add_node(make_node("n1")).unwrap();

        let entry = make_entry("func::foo", "n1");
        let replicas = proto.store(entry);
        assert!(!replicas.is_empty());

        let found = proto.lookup("func::foo");
        assert!(found.is_some());
        assert_eq!(found.unwrap().content_hash, "hash_func::foo");
    }

    #[test]
    fn test_lookup_miss() {
        let proto = CacheProtocol::new(default_config());
        assert!(proto.lookup("nonexistent").is_none());
    }

    #[test]
    fn test_store_overwrites() {
        let mut proto = CacheProtocol::new(default_config());
        proto.add_node(make_node("n1")).unwrap();

        proto.store(DistributedEntry {
            key: "k".to_string(),
            content_hash: "old".to_string(),
            verdict: "Verified".to_string(),
            timestamp: 100,
            node_origin: "n1".to_string(),
        });
        proto.store(DistributedEntry {
            key: "k".to_string(),
            content_hash: "new".to_string(),
            verdict: "Verified".to_string(),
            timestamp: 200,
            node_origin: "n1".to_string(),
        });

        assert_eq!(proto.lookup("k").unwrap().content_hash, "new");
    }

    // -----------------------------------------------------------------------
    // select_nodes tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_select_nodes_empty_cluster() {
        let proto = CacheProtocol::new(default_config());
        assert!(proto.select_nodes("key").is_empty());
    }

    #[test]
    fn test_select_nodes_count_bounded() {
        let mut proto = CacheProtocol::new(DistributedConfig {
            replication_factor: 2,
            ..default_config()
        });
        for i in 0..5 {
            proto.add_node(make_node(&format!("n{i}"))).unwrap();
        }
        // replication_factor=2 means primary + 2 replicas = 3 nodes
        let selected = proto.select_nodes("some_key");
        assert_eq!(selected.len(), 3);
    }

    #[test]
    fn test_select_nodes_capped_by_cluster_size() {
        let mut proto = CacheProtocol::new(DistributedConfig {
            replication_factor: 10,
            ..default_config()
        });
        proto.add_node(make_node("only")).unwrap();
        // Only 1 node, can't select more than 1
        let selected = proto.select_nodes("key");
        assert_eq!(selected.len(), 1);
    }

    // -----------------------------------------------------------------------
    // Invalidate tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_invalidate_existing_entry() {
        let mut proto = CacheProtocol::new(default_config());
        proto.add_node(make_node("n1")).unwrap();
        proto.add_node(make_node("n2")).unwrap();
        proto.add_node(make_node("n3")).unwrap();
        proto.store(make_entry("func::bar", "n1"));

        let notified = proto.invalidate("func::bar");
        assert!(notified > 0);
        assert!(proto.lookup("func::bar").is_none());
    }

    #[test]
    fn test_invalidate_nonexistent_returns_zero() {
        let mut proto = CacheProtocol::new(default_config());
        assert_eq!(proto.invalidate("missing"), 0);
    }

    // -----------------------------------------------------------------------
    // Stats tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_stats_empty() {
        let proto = CacheProtocol::new(default_config());
        let stats = proto.stats();
        assert_eq!(stats.total_entries, 0);
        assert_eq!(stats.total_nodes, 0);
    }

    #[test]
    fn test_stats_after_operations() {
        let mut proto = CacheProtocol::new(default_config());
        proto.add_node(make_node("a")).unwrap();
        proto.add_node(make_node("b")).unwrap();
        proto.store(make_entry("k1", "a"));
        proto.store(make_entry("k2", "b"));

        let stats = proto.stats();
        assert_eq!(stats.total_entries, 2);
        assert_eq!(stats.total_nodes, 2);
    }

    // -----------------------------------------------------------------------
    // Config tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_config_default() {
        let config = DistributedConfig::default();
        assert_eq!(config.replication_factor, 2);
        assert_eq!(config.consistency_level, ConsistencyLevel::Quorum);
        assert_eq!(config.ttl_seconds, 3600);
        assert_eq!(config.max_nodes, 64);
    }

    #[test]
    fn test_consistency_level_equality() {
        assert_eq!(ConsistencyLevel::One, ConsistencyLevel::One);
        assert_ne!(ConsistencyLevel::One, ConsistencyLevel::Quorum);
        assert_ne!(ConsistencyLevel::Quorum, ConsistencyLevel::All);
    }

    // -----------------------------------------------------------------------
    // DistributedEntry tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_distributed_entry_clone_eq() {
        let entry = make_entry("func::x", "origin");
        let cloned = entry.clone();
        assert_eq!(entry, cloned);
    }

    // -----------------------------------------------------------------------
    // Integration test
    // -----------------------------------------------------------------------

    #[test]
    fn test_full_lifecycle() {
        let mut proto = CacheProtocol::new(DistributedConfig {
            replication_factor: 1,
            consistency_level: ConsistencyLevel::All,
            ttl_seconds: 600,
            max_nodes: 5,
        });

        // Add nodes
        for i in 0..3 {
            proto.add_node(CacheNode::new(
                format!("node-{i}"),
                format!("10.0.0.{i}:9100"),
                10_000,
            )).unwrap();
        }
        assert_eq!(proto.node_count(), 3);

        // Store entries
        let replicas = proto.store(DistributedEntry {
            key: "crate::math::add".to_string(),
            content_hash: "abc123".to_string(),
            verdict: "Verified".to_string(),
            timestamp: 1_700_000_000,
            node_origin: "node-0".to_string(),
        });
        assert!(!replicas.is_empty());

        // Lookup
        let entry = proto.lookup("crate::math::add").unwrap();
        assert_eq!(entry.verdict, "Verified");
        assert_eq!(entry.node_origin, "node-0");

        // Stats
        let stats = proto.stats();
        assert_eq!(stats.total_entries, 1);
        assert_eq!(stats.total_nodes, 3);

        // Remove a node
        assert!(proto.remove_node("node-1"));
        assert_eq!(proto.node_count(), 2);

        // Invalidate
        let notified = proto.invalidate("crate::math::add");
        assert!(notified > 0);
        assert!(proto.lookup("crate::math::add").is_none());

        assert_eq!(proto.stats().total_entries, 0);
    }
}
