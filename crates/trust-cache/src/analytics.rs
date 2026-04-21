// trust-cache/analytics.rs: Cache analytics engine
//
// Provides hit/miss rate tracking (including time-windowed rates), eviction
// reason classification, per-query-type latency, memory usage estimation,
// top-N expensive queries, and JSON export for trust-report.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;
use std::time::Instant;

use serde::{Deserialize, Serialize};

// ---------------------------------------------------------------------------
// Eviction reason
// ---------------------------------------------------------------------------

/// Reason an entry was evicted from the cache.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum EvictionReason {
    /// Evicted because the cache exceeded its capacity limit.
    Capacity,
    /// Evicted because the entry exceeded its staleness threshold.
    Staleness,
    /// Evicted because a dependency changed (e.g., callee spec changed).
    Invalidation,
    /// Evicted by an explicit user/driver request.
    Manual,
    /// Evicted because its estimated size exceeded the budget.
    SizeBudget,
}

// ---------------------------------------------------------------------------
// Query type
// ---------------------------------------------------------------------------

/// Category of a solver query, used for per-type latency tracking.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum QueryType {
    /// SMT satisfiability check.
    SmtSat,
    /// SMT unsatisfiability (proof) check.
    SmtUnsat,
    /// Bounded model checking query.
    BoundedModelCheck,
    /// Deductive verification query.
    Deductive,
    /// Custom/other query type.
    Custom(String),
}

// ---------------------------------------------------------------------------
// Snapshot types
// ---------------------------------------------------------------------------

/// Snapshot of cache performance metrics.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct CacheAnalytics {
    /// Fraction of lookups that were hits, in `[0.0, 1.0]`.
    pub hit_rate: f64,
    /// Fraction of lookups that were misses, in `[0.0, 1.0]`.
    pub miss_rate: f64,
    /// Total number of evictions across all reasons.
    pub eviction_count: u64,
    /// Average lookup duration in nanoseconds (0 if no lookups recorded).
    pub avg_lookup_time_ns: u64,
    /// Total number of hits.
    pub total_hits: u64,
    /// Total number of misses.
    pub total_misses: u64,
    /// Estimated total memory usage in bytes.
    pub estimated_memory_bytes: u64,
    /// Per-query-type average latency in nanoseconds.
    pub per_query_type_latency_ns: FxHashMap<String, u64>,
    /// Top-N most expensive queries by cumulative latency.
    pub top_expensive_queries: Vec<ExpensiveQuery>,
}

/// Describes a single expensive query seen by the analytics engine.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ExpensiveQuery {
    /// Identifier (typically a content hash or function def_path).
    pub id: String,
    /// Total cumulative latency in nanoseconds.
    pub total_latency_ns: u64,
    /// Number of times this query was seen.
    pub count: u64,
}

/// A time-windowed hit rate measurement.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct WindowedRate {
    /// Window size description (e.g., "last_100").
    pub window: String,
    /// Hit rate within this window.
    pub hit_rate: f64,
    /// Number of lookups in this window.
    pub lookups: u64,
}

// ---------------------------------------------------------------------------
// Internal per-query-type tracker
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Default)]
struct QueryTypeStats {
    total_ns: u128,
    count: u64,
}

// ---------------------------------------------------------------------------
// Internal per-query tracker (for top-N)
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
struct QueryRecord {
    total_ns: u128,
    count: u64,
}

// ---------------------------------------------------------------------------
// Analytics collector
// ---------------------------------------------------------------------------

/// Tracks cache operations and computes analytics on demand.
///
/// Thread-safety is the caller's responsibility (wrap in `Mutex` if shared).
pub struct AnalyticsCollector {
    hits: u64,
    misses: u64,
    evictions_by_reason: FxHashMap<EvictionReason, u64>,
    /// Sum of lookup durations in nanoseconds.
    lookup_time_sum_ns: u128,
    lookup_count: u64,
    /// Per-query-type latency tracking.
    query_type_stats: FxHashMap<QueryType, QueryTypeStats>,
    /// Per-query-id latency tracking (for top-N).
    query_records: FxHashMap<String, QueryRecord>,
    /// Estimated memory usage in bytes (caller-reported).
    estimated_memory_bytes: u64,
    /// Rolling window of recent lookup outcomes (true = hit, false = miss).
    recent_outcomes: Vec<bool>,
    /// Maximum size of the rolling window.
    window_size: usize,
}

impl AnalyticsCollector {
    /// Create a new collector with all counters at zero.
    ///
    /// The rolling window defaults to 100 lookups.
    pub fn new() -> Self {
        Self::with_window_size(100)
    }

    /// Create a collector with a custom rolling window size.
    pub fn with_window_size(window_size: usize) -> Self {
        AnalyticsCollector {
            hits: 0,
            misses: 0,
            evictions_by_reason: FxHashMap::default(),
            lookup_time_sum_ns: 0,
            lookup_count: 0,
            query_type_stats: FxHashMap::default(),
            query_records: FxHashMap::default(),
            estimated_memory_bytes: 0,
            recent_outcomes: Vec::with_capacity(window_size),
            window_size: window_size.max(1),
        }
    }

    /// Record a cache hit.
    pub fn record_hit(&mut self) {
        self.hits += 1;
        self.push_outcome(true);
    }

    /// Record a cache miss.
    pub fn record_miss(&mut self) {
        self.misses += 1;
        self.push_outcome(false);
    }

    /// Record an eviction with its reason.
    pub fn record_eviction(&mut self, reason: EvictionReason) {
        *self.evictions_by_reason.entry(reason).or_insert(0) += 1;
    }

    /// Record a lookup duration. Call with the `Instant` captured before
    /// the lookup.
    pub fn record_lookup_time(&mut self, start: Instant) {
        let elapsed_ns = start.elapsed().as_nanos();
        self.lookup_time_sum_ns += elapsed_ns;
        self.lookup_count += 1;
    }

    /// Record a lookup duration from a pre-computed nanosecond value.
    pub fn record_lookup_time_ns(&mut self, ns: u64) {
        self.lookup_time_sum_ns += ns as u128;
        self.lookup_count += 1;
    }

    /// Record a query latency associated with a specific query type.
    pub fn record_query_latency(&mut self, query_type: QueryType, latency_ns: u64) {
        let entry = self.query_type_stats.entry(query_type).or_default();
        entry.total_ns += latency_ns as u128;
        entry.count += 1;
    }

    /// Record a query latency associated with a specific query identifier
    /// (for top-N tracking).
    pub fn record_query_by_id(&mut self, query_id: &str, latency_ns: u64) {
        let entry = self.query_records.entry(query_id.to_string()).or_insert(
            QueryRecord { total_ns: 0, count: 0 },
        );
        entry.total_ns += latency_ns as u128;
        entry.count += 1;
    }

    /// Update the estimated memory usage (caller-reported).
    pub fn set_estimated_memory_bytes(&mut self, bytes: u64) {
        self.estimated_memory_bytes = bytes;
    }

    /// Add to the estimated memory usage.
    pub fn add_memory_bytes(&mut self, bytes: u64) {
        self.estimated_memory_bytes += bytes;
    }

    /// Subtract from the estimated memory usage (saturating).
    pub fn remove_memory_bytes(&mut self, bytes: u64) {
        self.estimated_memory_bytes = self.estimated_memory_bytes.saturating_sub(bytes);
    }

    /// Get the number of evictions for a specific reason.
    #[must_use]
    pub fn evictions_for(&self, reason: EvictionReason) -> u64 {
        self.evictions_by_reason.get(&reason).copied().unwrap_or(0)
    }

    /// Compute the time-windowed hit rate over the last N lookups.
    #[must_use]
    pub fn windowed_hit_rate(&self) -> WindowedRate {
        let lookups = self.recent_outcomes.len() as u64;
        let hits = self.recent_outcomes.iter().filter(|&&h| h).count() as u64;
        let hit_rate = if lookups == 0 {
            0.0
        } else {
            hits as f64 / lookups as f64
        };
        WindowedRate {
            window: format!("last_{}", self.window_size),
            hit_rate,
            lookups,
        }
    }

    /// Get the top-N most expensive queries by cumulative latency.
    #[must_use]
    pub fn top_expensive_queries(&self, n: usize) -> Vec<ExpensiveQuery> {
        let mut entries: Vec<_> = self.query_records.iter().collect();
        entries.sort_by(|a, b| b.1.total_ns.cmp(&a.1.total_ns));
        entries
            .into_iter()
            .take(n)
            .map(|(id, record)| ExpensiveQuery {
                id: id.clone(),
                total_latency_ns: record.total_ns as u64,
                count: record.count,
            })
            .collect()
    }

    /// Compute a snapshot of current analytics.
    #[must_use]
    pub fn snapshot(&self) -> CacheAnalytics {
        self.snapshot_with_top_n(10)
    }

    /// Compute a snapshot with a configurable top-N expensive queries count.
    #[must_use]
    pub fn snapshot_with_top_n(&self, top_n: usize) -> CacheAnalytics {
        let total = self.hits + self.misses;
        let (hit_rate, miss_rate) = if total == 0 {
            (0.0, 0.0)
        } else {
            (
                self.hits as f64 / total as f64,
                self.misses as f64 / total as f64,
            )
        };

        let eviction_count: u64 = self.evictions_by_reason.values().sum();

        let avg_lookup_time_ns = if self.lookup_count == 0 {
            0
        } else {
            (self.lookup_time_sum_ns / self.lookup_count as u128) as u64
        };

        let per_query_type_latency_ns: FxHashMap<String, u64> = self
            .query_type_stats
            .iter()
            .map(|(qt, stats)| {
                let avg = if stats.count == 0 {
                    0
                } else {
                    (stats.total_ns / stats.count as u128) as u64
                };
                (format!("{qt:?}"), avg)
            })
            .collect();

        CacheAnalytics {
            hit_rate,
            miss_rate,
            eviction_count,
            avg_lookup_time_ns,
            total_hits: self.hits,
            total_misses: self.misses,
            estimated_memory_bytes: self.estimated_memory_bytes,
            per_query_type_latency_ns,
            top_expensive_queries: self.top_expensive_queries(top_n),
        }
    }

    /// Export analytics as a JSON string for trust-report.
    #[must_use]
    pub fn export_json(&self) -> String {
        let snap = self.snapshot();
        serde_json::to_string_pretty(&snap).unwrap_or_else(|_| "{}".to_string())
    }

    /// Reset all counters to zero.
    pub fn reset(&mut self) {
        self.hits = 0;
        self.misses = 0;
        self.evictions_by_reason.clear();
        self.lookup_time_sum_ns = 0;
        self.lookup_count = 0;
        self.query_type_stats.clear();
        self.query_records.clear();
        self.estimated_memory_bytes = 0;
        self.recent_outcomes.clear();
    }

    /// Push an outcome into the rolling window, evicting the oldest if full.
    fn push_outcome(&mut self, hit: bool) {
        if self.recent_outcomes.len() >= self.window_size {
            self.recent_outcomes.remove(0);
        }
        self.recent_outcomes.push(hit);
    }
}

impl Default for AnalyticsCollector {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Memory estimator
// ---------------------------------------------------------------------------

/// Estimates memory usage of cache entries.
///
/// Provides heuristic-based size estimation for entries that don't carry
/// an explicit size field.
pub struct MemoryEstimator {
    /// Per-entry overhead in bytes (HashMap slot + key + metadata).
    pub per_entry_overhead: usize,
    /// Average value size in bytes (calibrated by the caller).
    pub avg_value_size: usize,
}

impl MemoryEstimator {
    /// Create with default estimates (128 bytes overhead, 512 bytes avg value).
    pub fn new() -> Self {
        MemoryEstimator {
            per_entry_overhead: 128,
            avg_value_size: 512,
        }
    }

    /// Create with custom estimates.
    pub fn with_sizes(per_entry_overhead: usize, avg_value_size: usize) -> Self {
        MemoryEstimator {
            per_entry_overhead,
            avg_value_size,
        }
    }

    /// Estimate total memory for `n` entries.
    #[must_use]
    pub fn estimate_total(&self, n: usize) -> u64 {
        (n as u64) * (self.per_entry_overhead as u64 + self.avg_value_size as u64)
    }

    /// Estimate memory for a single entry given its serialized size.
    #[must_use]
    pub fn estimate_entry(&self, serialized_size: usize) -> u64 {
        (self.per_entry_overhead + serialized_size) as u64
    }
}

impl Default for MemoryEstimator {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_analytics_collector_new_is_zero() {
        let collector = AnalyticsCollector::new();
        let snap = collector.snapshot();
        assert_eq!(snap.total_hits, 0);
        assert_eq!(snap.total_misses, 0);
        assert_eq!(snap.eviction_count, 0);
        assert_eq!(snap.avg_lookup_time_ns, 0);
        assert!((snap.hit_rate - 0.0).abs() < f64::EPSILON);
        assert!((snap.miss_rate - 0.0).abs() < f64::EPSILON);
        assert_eq!(snap.estimated_memory_bytes, 0);
    }

    #[test]
    fn test_analytics_hit_miss_rates() {
        let mut collector = AnalyticsCollector::new();
        collector.record_hit();
        collector.record_hit();
        collector.record_hit();
        collector.record_miss();

        let snap = collector.snapshot();
        assert_eq!(snap.total_hits, 3);
        assert_eq!(snap.total_misses, 1);
        assert!((snap.hit_rate - 0.75).abs() < f64::EPSILON);
        assert!((snap.miss_rate - 0.25).abs() < f64::EPSILON);
    }

    #[test]
    fn test_analytics_all_hits() {
        let mut collector = AnalyticsCollector::new();
        collector.record_hit();
        collector.record_hit();

        let snap = collector.snapshot();
        assert!((snap.hit_rate - 1.0).abs() < f64::EPSILON);
        assert!((snap.miss_rate - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_analytics_all_misses() {
        let mut collector = AnalyticsCollector::new();
        collector.record_miss();
        collector.record_miss();

        let snap = collector.snapshot();
        assert!((snap.hit_rate - 0.0).abs() < f64::EPSILON);
        assert!((snap.miss_rate - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_analytics_eviction_counts() {
        let mut collector = AnalyticsCollector::new();
        collector.record_eviction(EvictionReason::Capacity);
        collector.record_eviction(EvictionReason::Capacity);
        collector.record_eviction(EvictionReason::Staleness);
        collector.record_eviction(EvictionReason::Invalidation);
        collector.record_eviction(EvictionReason::Manual);
        collector.record_eviction(EvictionReason::SizeBudget);

        assert_eq!(collector.evictions_for(EvictionReason::Capacity), 2);
        assert_eq!(collector.evictions_for(EvictionReason::Staleness), 1);
        assert_eq!(collector.evictions_for(EvictionReason::Invalidation), 1);
        assert_eq!(collector.evictions_for(EvictionReason::Manual), 1);
        assert_eq!(collector.evictions_for(EvictionReason::SizeBudget), 1);

        let snap = collector.snapshot();
        assert_eq!(snap.eviction_count, 6);
    }

    #[test]
    fn test_analytics_lookup_time_ns() {
        let mut collector = AnalyticsCollector::new();
        collector.record_lookup_time_ns(100);
        collector.record_lookup_time_ns(200);
        collector.record_lookup_time_ns(300);

        let snap = collector.snapshot();
        assert_eq!(snap.avg_lookup_time_ns, 200);
    }

    #[test]
    fn test_analytics_lookup_time_instant() {
        let mut collector = AnalyticsCollector::new();
        let start = Instant::now();
        let _ = (0..100).sum::<u64>();
        collector.record_lookup_time(start);

        // lookup_count should be 1
        assert_eq!(collector.lookup_count, 1);
    }

    #[test]
    fn test_analytics_reset() {
        let mut collector = AnalyticsCollector::new();
        collector.record_hit();
        collector.record_miss();
        collector.record_eviction(EvictionReason::Capacity);
        collector.record_lookup_time_ns(500);
        collector.record_query_latency(QueryType::SmtSat, 1000);
        collector.record_query_by_id("q1", 2000);
        collector.set_estimated_memory_bytes(4096);

        collector.reset();

        let snap = collector.snapshot();
        assert_eq!(snap.total_hits, 0);
        assert_eq!(snap.total_misses, 0);
        assert_eq!(snap.eviction_count, 0);
        assert_eq!(snap.avg_lookup_time_ns, 0);
        assert_eq!(snap.estimated_memory_bytes, 0);
        assert!(snap.per_query_type_latency_ns.is_empty());
        assert!(snap.top_expensive_queries.is_empty());
    }

    #[test]
    fn test_analytics_default_impl() {
        let collector = AnalyticsCollector::default();
        let snap = collector.snapshot();
        assert_eq!(snap.total_hits, 0);
        assert_eq!(snap.eviction_count, 0);
    }

    #[test]
    fn test_eviction_reason_debug_clone_copy() {
        let reason = EvictionReason::Capacity;
        let cloned = reason;
        assert_eq!(reason, cloned);
        assert_eq!(format!("{:?}", reason), "Capacity");
    }

    #[test]
    fn test_cache_analytics_debug_clone() {
        let snap = CacheAnalytics {
            hit_rate: 0.5,
            miss_rate: 0.5,
            eviction_count: 3,
            avg_lookup_time_ns: 100,
            total_hits: 5,
            total_misses: 5,
            estimated_memory_bytes: 1024,
            per_query_type_latency_ns: FxHashMap::default(),
            top_expensive_queries: vec![],
        };
        let cloned = snap.clone();
        assert_eq!(snap, cloned);
        assert!(format!("{:?}", snap).contains("hit_rate"));
    }

    // -----------------------------------------------------------------------
    // Time-windowed hit rates
    // -----------------------------------------------------------------------

    #[test]
    fn test_windowed_hit_rate_empty() {
        let collector = AnalyticsCollector::new();
        let windowed = collector.windowed_hit_rate();
        assert_eq!(windowed.lookups, 0);
        assert!((windowed.hit_rate - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_windowed_hit_rate_tracks_recent() {
        let mut collector = AnalyticsCollector::with_window_size(4);
        collector.record_hit();
        collector.record_hit();
        collector.record_miss();
        collector.record_hit();

        let windowed = collector.windowed_hit_rate();
        assert_eq!(windowed.lookups, 4);
        assert!((windowed.hit_rate - 0.75).abs() < f64::EPSILON);
    }

    #[test]
    fn test_windowed_hit_rate_evicts_oldest() {
        let mut collector = AnalyticsCollector::with_window_size(3);
        // Fill window: miss, miss, miss
        collector.record_miss();
        collector.record_miss();
        collector.record_miss();
        // Now add 3 hits -- oldest misses should be evicted
        collector.record_hit();
        collector.record_hit();
        collector.record_hit();

        let windowed = collector.windowed_hit_rate();
        assert_eq!(windowed.lookups, 3);
        assert!((windowed.hit_rate - 1.0).abs() < f64::EPSILON);
    }

    // -----------------------------------------------------------------------
    // Per-query-type latency
    // -----------------------------------------------------------------------

    #[test]
    fn test_per_query_type_latency() {
        let mut collector = AnalyticsCollector::new();
        collector.record_query_latency(QueryType::SmtSat, 100);
        collector.record_query_latency(QueryType::SmtSat, 200);
        collector.record_query_latency(QueryType::SmtUnsat, 500);

        let snap = collector.snapshot();
        let smt_sat_avg = snap
            .per_query_type_latency_ns
            .get("SmtSat")
            .copied()
            .unwrap_or(0);
        assert_eq!(smt_sat_avg, 150);
        let smt_unsat_avg = snap
            .per_query_type_latency_ns
            .get("SmtUnsat")
            .copied()
            .unwrap_or(0);
        assert_eq!(smt_unsat_avg, 500);
    }

    #[test]
    fn test_per_query_type_custom() {
        let mut collector = AnalyticsCollector::new();
        collector.record_query_latency(QueryType::Custom("my_type".into()), 300);

        let snap = collector.snapshot();
        // The Debug representation of Custom includes the string
        let has_custom = snap
            .per_query_type_latency_ns
            .keys()
            .any(|k| k.contains("my_type"));
        assert!(has_custom, "custom query type should appear in snapshot");
    }

    // -----------------------------------------------------------------------
    // Top-N expensive queries
    // -----------------------------------------------------------------------

    #[test]
    fn test_top_expensive_queries() {
        let mut collector = AnalyticsCollector::new();
        collector.record_query_by_id("fast_query", 100);
        collector.record_query_by_id("slow_query", 5000);
        collector.record_query_by_id("medium_query", 1000);
        collector.record_query_by_id("slow_query", 3000); // cumulative: 8000

        let top = collector.top_expensive_queries(2);
        assert_eq!(top.len(), 2);
        assert_eq!(top[0].id, "slow_query");
        assert_eq!(top[0].total_latency_ns, 8000);
        assert_eq!(top[0].count, 2);
        assert_eq!(top[1].id, "medium_query");
    }

    #[test]
    fn test_top_expensive_queries_empty() {
        let collector = AnalyticsCollector::new();
        let top = collector.top_expensive_queries(5);
        assert!(top.is_empty());
    }

    #[test]
    fn test_top_expensive_queries_fewer_than_n() {
        let mut collector = AnalyticsCollector::new();
        collector.record_query_by_id("only_one", 999);
        let top = collector.top_expensive_queries(10);
        assert_eq!(top.len(), 1);
    }

    // -----------------------------------------------------------------------
    // Memory estimation
    // -----------------------------------------------------------------------

    #[test]
    fn test_memory_tracking() {
        let mut collector = AnalyticsCollector::new();
        collector.set_estimated_memory_bytes(1024);
        assert_eq!(collector.snapshot().estimated_memory_bytes, 1024);

        collector.add_memory_bytes(512);
        assert_eq!(collector.snapshot().estimated_memory_bytes, 1536);

        collector.remove_memory_bytes(256);
        assert_eq!(collector.snapshot().estimated_memory_bytes, 1280);

        // Saturating subtraction
        collector.remove_memory_bytes(99999);
        assert_eq!(collector.snapshot().estimated_memory_bytes, 0);
    }

    #[test]
    fn test_memory_estimator_defaults() {
        let estimator = MemoryEstimator::new();
        assert_eq!(estimator.per_entry_overhead, 128);
        assert_eq!(estimator.avg_value_size, 512);
    }

    #[test]
    fn test_memory_estimator_estimate_total() {
        let estimator = MemoryEstimator::with_sizes(100, 400);
        assert_eq!(estimator.estimate_total(10), 5000);
    }

    #[test]
    fn test_memory_estimator_estimate_entry() {
        let estimator = MemoryEstimator::with_sizes(100, 400);
        // 100 overhead + 256 serialized = 356
        assert_eq!(estimator.estimate_entry(256), 356);
    }

    // -----------------------------------------------------------------------
    // JSON export
    // -----------------------------------------------------------------------

    #[test]
    fn test_export_json_parses() {
        let mut collector = AnalyticsCollector::new();
        collector.record_hit();
        collector.record_miss();
        collector.record_eviction(EvictionReason::Capacity);
        collector.record_query_latency(QueryType::SmtSat, 100);
        collector.record_query_by_id("q1", 200);
        collector.set_estimated_memory_bytes(2048);

        let json = collector.export_json();
        let parsed: serde_json::Value =
            serde_json::from_str(&json).expect("export should produce valid JSON");
        assert_eq!(parsed["total_hits"], 1);
        assert_eq!(parsed["total_misses"], 1);
        assert_eq!(parsed["estimated_memory_bytes"], 2048);
    }

    #[test]
    fn test_export_json_roundtrip() {
        let mut collector = AnalyticsCollector::new();
        collector.record_hit();
        collector.record_hit();
        collector.record_miss();

        let json = collector.export_json();
        let deserialized: CacheAnalytics =
            serde_json::from_str(&json).expect("should deserialize");
        assert_eq!(deserialized.total_hits, 2);
        assert_eq!(deserialized.total_misses, 1);
    }

    // -----------------------------------------------------------------------
    // Snapshot with custom top-N
    // -----------------------------------------------------------------------

    #[test]
    fn test_snapshot_with_top_n() {
        let mut collector = AnalyticsCollector::new();
        for i in 0..20 {
            collector.record_query_by_id(&format!("q{i}"), (i + 1) * 100);
        }

        let snap = collector.snapshot_with_top_n(3);
        assert_eq!(snap.top_expensive_queries.len(), 3);
        // Most expensive should be q19 (2000ns)
        assert_eq!(snap.top_expensive_queries[0].id, "q19");
    }
}
