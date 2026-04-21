// trust-cache/warming.rs: Cache warming strategies
//
// Pre-populates the verification cache before a verification run begins.
// Strategies include call-graph order traversal, hot-function prioritization,
// loading from a previous session's cache, and background warming with
// progress tracking.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::VecDeque;
use trust_types::fx::{FxHashMap, FxHashSet};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::Arc;

use serde::{Deserialize, Serialize};

/// Strategy for warming the cache.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum WarmingStrategy {
    /// Warm callees before callers (bottom-up topological order).
    CallGraphOrder,
    /// Warm functions that were most frequently verified in previous sessions.
    HotFunctions,
    /// Load all entries from a previous session's serialized cache.
    PreviousSession,
}

/// Priority level for warming entries.
#[derive(
    Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default, Serialize, Deserialize,
)]
pub enum WarmingPriority {
    /// Low priority: warm only if time permits.
    Low = 0,
    /// Normal priority.
    #[default]
    Normal = 1,
    /// High priority: warm early.
    High = 2,
    /// Critical: must warm before verification begins.
    Critical = 3,
}

/// A single entry in a warming plan, with priority metadata.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct WarmingEntry {
    /// Function def_path to warm.
    pub def_path: String,
    /// Priority for this entry.
    pub priority: WarmingPriority,
}

/// A warming plan: ordered list of function def_paths to pre-load.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct WarmingPlan {
    /// Ordered list of function def_paths to warm, in priority order.
    pub functions: Vec<String>,
    /// The strategy that produced this plan.
    pub strategy: WarmingStrategy,
    /// Priority-annotated entries (same order as `functions`).
    pub entries: Vec<WarmingEntry>,
}

impl WarmingPlan {
    /// Number of functions in the plan.
    #[must_use]
    pub fn len(&self) -> usize {
        self.functions.len()
    }

    /// Whether the plan is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.functions.is_empty()
    }

    /// Get only functions with at least the given priority.
    #[must_use]
    pub fn filter_by_priority(&self, min_priority: WarmingPriority) -> Vec<&str> {
        self.entries
            .iter()
            .filter(|e| e.priority >= min_priority)
            .map(|e| e.def_path.as_str())
            .collect()
    }
}

// ---------------------------------------------------------------------------
// Warming progress tracker
// ---------------------------------------------------------------------------

/// Tracks the progress of a cache warming operation.
///
/// Thread-safe via atomic operations. Shared between the warming producer
/// and any monitoring code.
#[derive(Debug)]
pub struct WarmingProgress {
    /// Total number of functions to warm.
    total: AtomicU64,
    /// Number of functions warmed so far.
    completed: AtomicU64,
    /// Number of functions that failed to warm.
    failed: AtomicU64,
    /// Whether warming has been cancelled.
    cancelled: AtomicBool,
    /// Whether warming is complete.
    done: AtomicBool,
}

impl WarmingProgress {
    /// Create a new progress tracker for `total` functions.
    pub fn new(total: u64) -> Self {
        WarmingProgress {
            total: AtomicU64::new(total),
            completed: AtomicU64::new(0),
            failed: AtomicU64::new(0),
            cancelled: AtomicBool::new(false),
            done: AtomicBool::new(false),
        }
    }

    /// Record one function successfully warmed.
    pub fn record_completed(&self) {
        self.completed.fetch_add(1, Ordering::Relaxed);
    }

    /// Record one function that failed to warm.
    pub fn record_failed(&self) {
        self.failed.fetch_add(1, Ordering::Relaxed);
    }

    /// Signal that warming should be cancelled.
    pub fn cancel(&self) {
        self.cancelled.store(true, Ordering::Release);
    }

    /// Signal that warming is complete.
    pub fn mark_done(&self) {
        self.done.store(true, Ordering::Release);
    }

    /// Whether warming has been cancelled.
    #[must_use]
    pub fn is_cancelled(&self) -> bool {
        self.cancelled.load(Ordering::Acquire)
    }

    /// Whether warming is complete.
    #[must_use]
    pub fn is_done(&self) -> bool {
        self.done.load(Ordering::Acquire)
    }

    /// Total functions to warm.
    #[must_use]
    pub fn total(&self) -> u64 {
        self.total.load(Ordering::Relaxed)
    }

    /// Number of functions warmed so far.
    #[must_use]
    pub fn completed(&self) -> u64 {
        self.completed.load(Ordering::Relaxed)
    }

    /// Number of functions that failed.
    #[must_use]
    pub fn failed(&self) -> u64 {
        self.failed.load(Ordering::Relaxed)
    }

    /// Progress as a fraction in [0.0, 1.0].
    #[must_use]
    pub fn fraction(&self) -> f64 {
        let total = self.total();
        if total == 0 {
            return 1.0;
        }
        let done = self.completed() + self.failed();
        (done as f64) / (total as f64)
    }

    /// Snapshot of the current state.
    #[must_use]
    pub fn snapshot(&self) -> WarmingProgressSnapshot {
        WarmingProgressSnapshot {
            total: self.total(),
            completed: self.completed(),
            failed: self.failed(),
            is_cancelled: self.is_cancelled(),
            is_done: self.is_done(),
            fraction: self.fraction(),
        }
    }
}

/// Serializable snapshot of warming progress.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct WarmingProgressSnapshot {
    pub total: u64,
    pub completed: u64,
    pub failed: u64,
    pub is_cancelled: bool,
    pub is_done: bool,
    pub fraction: f64,
}

// ---------------------------------------------------------------------------
// Background warming handle
// ---------------------------------------------------------------------------

/// Handle returned by `CacheWarmer::start_background_warming`.
///
/// Allows monitoring progress and cancelling warming from the main thread.
pub struct BackgroundWarmingHandle {
    /// Shared progress tracker.
    pub progress: Arc<WarmingProgress>,
    /// The plan being executed.
    pub plan: WarmingPlan,
}

impl BackgroundWarmingHandle {
    /// Cancel the background warming operation.
    pub fn cancel(&self) {
        self.progress.cancel();
    }

    /// Whether the background warming is complete.
    #[must_use]
    pub fn is_done(&self) -> bool {
        self.progress.is_done()
    }

    /// Current progress snapshot.
    #[must_use]
    pub fn snapshot(&self) -> WarmingProgressSnapshot {
        self.progress.snapshot()
    }
}

// ---------------------------------------------------------------------------
// Cache warmer
// ---------------------------------------------------------------------------

/// Builds cache warming plans from program metadata.
///
/// The warmer does not touch the cache directly; it produces a `WarmingPlan`
/// that the driver uses to pre-populate entries.
pub struct CacheWarmer {
    /// Call graph: caller -> set of callees.
    call_graph: FxHashMap<String, Vec<String>>,
    /// Historical access counts: def_path -> number of previous verifications.
    hot_counts: FxHashMap<String, u64>,
    /// Previous session entries: def_path -> content_hash.
    previous_entries: FxHashMap<String, String>,
    /// Per-function priority overrides.
    priority_overrides: FxHashMap<String, WarmingPriority>,
}

impl CacheWarmer {
    /// Create an empty warmer.
    pub fn new() -> Self {
        CacheWarmer {
            call_graph: FxHashMap::default(),
            hot_counts: FxHashMap::default(),
            previous_entries: FxHashMap::default(),
            priority_overrides: FxHashMap::default(),
        }
    }

    /// Register a call edge: `caller` calls `callee`.
    pub fn add_call_edge(&mut self, caller: &str, callee: &str) {
        self.call_graph
            .entry(caller.to_string())
            .or_default()
            .push(callee.to_string());
    }

    /// Register a function's historical verification count.
    pub fn set_hot_count(&mut self, def_path: &str, count: u64) {
        self.hot_counts.insert(def_path.to_string(), count);
    }

    /// Register a previous session cache entry.
    pub fn add_previous_entry(&mut self, def_path: &str, content_hash: &str) {
        self.previous_entries
            .insert(def_path.to_string(), content_hash.to_string());
    }

    /// Set a priority override for a specific function.
    pub fn set_priority(&mut self, def_path: &str, priority: WarmingPriority) {
        self.priority_overrides
            .insert(def_path.to_string(), priority);
    }

    /// Produce a warming plan for the given strategy.
    #[must_use]
    pub fn plan(&self, strategy: WarmingStrategy) -> WarmingPlan {
        let functions = match strategy {
            WarmingStrategy::CallGraphOrder => self.call_graph_order(),
            WarmingStrategy::HotFunctions => self.hot_function_order(),
            WarmingStrategy::PreviousSession => self.previous_session_order(),
        };
        let entries = self.build_entries(&functions, strategy);
        WarmingPlan { functions, strategy, entries }
    }

    /// Produce a combined plan merging multiple strategies.
    ///
    /// Later strategies' functions are appended only if not already present.
    #[must_use]
    pub fn plan_combined(&self, strategies: &[WarmingStrategy]) -> WarmingPlan {
        let mut seen = FxHashSet::default();
        let mut functions = Vec::new();

        for &strategy in strategies {
            let plan = self.plan(strategy);
            for f in plan.functions {
                if seen.insert(f.clone()) {
                    functions.push(f);
                }
            }
        }

        let strategy = strategies
            .first()
            .copied()
            .unwrap_or(WarmingStrategy::PreviousSession);
        let entries = self.build_entries(&functions, strategy);

        WarmingPlan { functions, strategy, entries }
    }

    /// Start a background warming operation.
    ///
    /// Returns a handle with a shared progress tracker. The caller is
    /// responsible for iterating `plan.functions` and calling
    /// `progress.record_completed()` / `progress.record_failed()` as each
    /// function is warmed -- this method only creates the tracking
    /// infrastructure.
    pub fn start_background_warming(
        &self,
        strategy: WarmingStrategy,
    ) -> BackgroundWarmingHandle {
        let plan = self.plan(strategy);
        let progress = Arc::new(WarmingProgress::new(plan.functions.len() as u64));
        BackgroundWarmingHandle { progress, plan }
    }

    /// Build priority-annotated entries for a list of functions.
    fn build_entries(
        &self,
        functions: &[String],
        strategy: WarmingStrategy,
    ) -> Vec<WarmingEntry> {
        functions
            .iter()
            .enumerate()
            .map(|(i, def_path)| {
                let priority = if let Some(&p) = self.priority_overrides.get(def_path) {
                    p
                } else {
                    self.infer_priority(def_path, i, functions.len(), strategy)
                };
                WarmingEntry {
                    def_path: def_path.clone(),
                    priority,
                }
            })
            .collect()
    }

    /// Infer a priority based on position, hot count, and strategy.
    fn infer_priority(
        &self,
        def_path: &str,
        position: usize,
        total: usize,
        strategy: WarmingStrategy,
    ) -> WarmingPriority {
        // Hot functions with high counts get higher priority
        if let Some(&count) = self.hot_counts.get(def_path) {
            if count >= 100 {
                return WarmingPriority::Critical;
            }
            if count >= 10 {
                return WarmingPriority::High;
            }
        }

        // For call-graph order, early entries (callees) are higher priority
        if strategy == WarmingStrategy::CallGraphOrder && total > 0 {
            let frac = position as f64 / total as f64;
            if frac < 0.25 {
                return WarmingPriority::High;
            }
        }

        WarmingPriority::Normal
    }

    /// Bottom-up topological order: callees before callers.
    fn call_graph_order(&self) -> Vec<String> {
        // Collect all nodes
        let mut all_nodes: FxHashSet<&str> = FxHashSet::default();
        for (caller, callees) in &self.call_graph {
            all_nodes.insert(caller.as_str());
            for callee in callees {
                all_nodes.insert(callee.as_str());
            }
        }

        // Compute in-degree (how many callers each function has)
        // For bottom-up: we want to process callees first.
        // Reverse the graph: edge from callee -> caller.
        let mut reverse_adj: FxHashMap<&str, Vec<&str>> = FxHashMap::default();
        let mut in_degree: FxHashMap<&str, usize> = FxHashMap::default();
        for node in &all_nodes {
            in_degree.entry(node).or_insert(0);
        }
        for (caller, callees) in &self.call_graph {
            for callee in callees {
                reverse_adj
                    .entry(callee.as_str())
                    .or_default()
                    .push(caller.as_str());
                *in_degree.entry(caller.as_str()).or_insert(0) += 1;
            }
        }

        // Kahn's algorithm on the reversed graph
        let mut queue: VecDeque<&str> = VecDeque::new();
        for (&node, &deg) in &in_degree {
            if deg == 0 {
                queue.push_back(node);
            }
        }

        // Sort the initial queue for determinism
        let mut sorted_queue: Vec<&str> = queue.drain(..).collect();
        sorted_queue.sort();
        queue.extend(sorted_queue);

        let mut result = Vec::new();
        while let Some(node) = queue.pop_front() {
            result.push(node.to_string());
            if let Some(neighbors) = reverse_adj.get(node) {
                let mut next_batch = Vec::new();
                for &neighbor in neighbors {
                    if let Some(deg) = in_degree.get_mut(neighbor) {
                        *deg = deg.saturating_sub(1);
                        if *deg == 0 {
                            next_batch.push(neighbor);
                        }
                    }
                }
                // Sort for determinism
                next_batch.sort();
                queue.extend(next_batch);
            }
        }

        // Any remaining nodes (cycles) -- add sorted
        let result_set: FxHashSet<&str> =
            result.iter().map(|s| s.as_str()).collect();
        let mut remaining: Vec<String> = all_nodes
            .iter()
            .filter(|n| !result_set.contains(**n))
            .map(|n| n.to_string())
            .collect();
        remaining.sort();
        result.extend(remaining);

        result
    }

    /// Order by descending hot count (most-verified first).
    fn hot_function_order(&self) -> Vec<String> {
        let mut entries: Vec<(&String, &u64)> = self.hot_counts.iter().collect();
        // Sort by descending count, then alphabetically for ties
        entries.sort_by(|a, b| b.1.cmp(a.1).then_with(|| a.0.cmp(b.0)));
        entries.into_iter().map(|(k, _)| k.clone()).collect()
    }

    /// All previous session entries in alphabetical order.
    fn previous_session_order(&self) -> Vec<String> {
        let mut keys: Vec<String> = self.previous_entries.keys().cloned().collect();
        keys.sort();
        keys
    }
}

impl Default for CacheWarmer {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // -----------------------------------------------------------------------
    // WarmingStrategy tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_warming_strategy_debug_clone_eq() {
        let s = WarmingStrategy::CallGraphOrder;
        assert_eq!(s, WarmingStrategy::CallGraphOrder);
        assert_ne!(s, WarmingStrategy::HotFunctions);
        assert_eq!(format!("{:?}", s), "CallGraphOrder");
    }

    // -----------------------------------------------------------------------
    // CallGraphOrder tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_call_graph_order_simple_chain() {
        let mut warmer = CacheWarmer::new();
        // a -> b -> c (a calls b, b calls c)
        warmer.add_call_edge("a", "b");
        warmer.add_call_edge("b", "c");

        let plan = warmer.plan(WarmingStrategy::CallGraphOrder);
        assert_eq!(plan.strategy, WarmingStrategy::CallGraphOrder);

        // c should come before b, b before a (callees first)
        let pos_a = plan.functions.iter().position(|f| f == "a").unwrap();
        let pos_b = plan.functions.iter().position(|f| f == "b").unwrap();
        let pos_c = plan.functions.iter().position(|f| f == "c").unwrap();
        assert!(pos_c < pos_b, "callee c should come before caller b");
        assert!(pos_b < pos_a, "callee b should come before caller a");
    }

    #[test]
    fn test_call_graph_order_diamond() {
        let mut warmer = CacheWarmer::new();
        // a -> b, a -> c, b -> d, c -> d
        warmer.add_call_edge("a", "b");
        warmer.add_call_edge("a", "c");
        warmer.add_call_edge("b", "d");
        warmer.add_call_edge("c", "d");

        let plan = warmer.plan(WarmingStrategy::CallGraphOrder);

        let pos_a = plan.functions.iter().position(|f| f == "a").unwrap();
        let pos_b = plan.functions.iter().position(|f| f == "b").unwrap();
        let pos_c = plan.functions.iter().position(|f| f == "c").unwrap();
        let pos_d = plan.functions.iter().position(|f| f == "d").unwrap();

        assert!(pos_d < pos_b, "d before b");
        assert!(pos_d < pos_c, "d before c");
        assert!(pos_b < pos_a, "b before a");
        assert!(pos_c < pos_a, "c before a");
    }

    #[test]
    fn test_call_graph_order_no_edges() {
        let warmer = CacheWarmer::new();
        let plan = warmer.plan(WarmingStrategy::CallGraphOrder);
        assert!(plan.functions.is_empty());
    }

    #[test]
    fn test_call_graph_order_cycle_handled() {
        let mut warmer = CacheWarmer::new();
        // a -> b -> a (cycle)
        warmer.add_call_edge("a", "b");
        warmer.add_call_edge("b", "a");

        let plan = warmer.plan(WarmingStrategy::CallGraphOrder);
        // Both nodes should appear exactly once
        assert_eq!(plan.functions.len(), 2);
        assert!(plan.functions.contains(&"a".to_string()));
        assert!(plan.functions.contains(&"b".to_string()));
    }

    #[test]
    fn test_call_graph_order_isolated_node() {
        let mut warmer = CacheWarmer::new();
        warmer.add_call_edge("a", "b");
        warmer.add_call_edge("a", "c");

        let plan = warmer.plan(WarmingStrategy::CallGraphOrder);
        assert_eq!(plan.functions.len(), 3);
        let pos_a = plan.functions.iter().position(|f| f == "a").unwrap();
        let pos_b = plan.functions.iter().position(|f| f == "b").unwrap();
        let pos_c = plan.functions.iter().position(|f| f == "c").unwrap();
        assert!(pos_b < pos_a);
        assert!(pos_c < pos_a);
    }

    // -----------------------------------------------------------------------
    // HotFunctions tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_hot_functions_order() {
        let mut warmer = CacheWarmer::new();
        warmer.set_hot_count("low", 5);
        warmer.set_hot_count("high", 100);
        warmer.set_hot_count("mid", 50);

        let plan = warmer.plan(WarmingStrategy::HotFunctions);
        assert_eq!(plan.functions, vec!["high", "mid", "low"]);
    }

    #[test]
    fn test_hot_functions_tie_breaks_alphabetically() {
        let mut warmer = CacheWarmer::new();
        warmer.set_hot_count("b", 10);
        warmer.set_hot_count("a", 10);
        warmer.set_hot_count("c", 10);

        let plan = warmer.plan(WarmingStrategy::HotFunctions);
        assert_eq!(plan.functions, vec!["a", "b", "c"]);
    }

    #[test]
    fn test_hot_functions_empty() {
        let warmer = CacheWarmer::new();
        let plan = warmer.plan(WarmingStrategy::HotFunctions);
        assert!(plan.functions.is_empty());
    }

    // -----------------------------------------------------------------------
    // PreviousSession tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_previous_session_order() {
        let mut warmer = CacheWarmer::new();
        warmer.add_previous_entry("c::func", "hash3");
        warmer.add_previous_entry("a::func", "hash1");
        warmer.add_previous_entry("b::func", "hash2");

        let plan = warmer.plan(WarmingStrategy::PreviousSession);
        assert_eq!(plan.functions, vec!["a::func", "b::func", "c::func"]);
    }

    #[test]
    fn test_previous_session_empty() {
        let warmer = CacheWarmer::new();
        let plan = warmer.plan(WarmingStrategy::PreviousSession);
        assert!(plan.functions.is_empty());
    }

    // -----------------------------------------------------------------------
    // Combined plan tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_combined_plan_deduplicates() {
        let mut warmer = CacheWarmer::new();
        warmer.add_call_edge("a", "b");
        warmer.set_hot_count("b", 100);
        warmer.set_hot_count("c", 50);

        let plan = warmer.plan_combined(&[
            WarmingStrategy::CallGraphOrder,
            WarmingStrategy::HotFunctions,
        ]);

        // "b" should appear only once
        let b_count = plan
            .functions
            .iter()
            .filter(|f| f.as_str() == "b")
            .count();
        assert_eq!(b_count, 1);

        // "c" should be added from hot functions
        assert!(plan.functions.contains(&"c".to_string()));
    }

    #[test]
    fn test_combined_plan_empty_strategies() {
        let warmer = CacheWarmer::new();
        let plan = warmer.plan_combined(&[]);
        assert!(plan.functions.is_empty());
    }

    // -----------------------------------------------------------------------
    // WarmingPlan tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_warming_plan_debug_clone() {
        let plan = WarmingPlan {
            functions: vec!["a".to_string()],
            strategy: WarmingStrategy::CallGraphOrder,
            entries: vec![WarmingEntry {
                def_path: "a".to_string(),
                priority: WarmingPriority::Normal,
            }],
        };
        let cloned = plan.clone();
        assert_eq!(plan, cloned);
        assert!(format!("{:?}", plan).contains("CallGraphOrder"));
    }

    #[test]
    fn test_warming_plan_len_is_empty() {
        let plan = WarmingPlan {
            functions: vec!["a".to_string(), "b".to_string()],
            strategy: WarmingStrategy::HotFunctions,
            entries: vec![],
        };
        assert_eq!(plan.len(), 2);
        assert!(!plan.is_empty());

        let empty = WarmingPlan {
            functions: vec![],
            strategy: WarmingStrategy::PreviousSession,
            entries: vec![],
        };
        assert!(empty.is_empty());
    }

    // -----------------------------------------------------------------------
    // Default impl tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_cache_warmer_default() {
        let warmer = CacheWarmer::default();
        let plan = warmer.plan(WarmingStrategy::HotFunctions);
        assert!(plan.functions.is_empty());
    }

    // -----------------------------------------------------------------------
    // Priority tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_priority_ordering() {
        assert!(WarmingPriority::Low < WarmingPriority::Normal);
        assert!(WarmingPriority::Normal < WarmingPriority::High);
        assert!(WarmingPriority::High < WarmingPriority::Critical);
    }

    #[test]
    fn test_priority_override() {
        let mut warmer = CacheWarmer::new();
        warmer.add_call_edge("a", "b");
        warmer.set_priority("b", WarmingPriority::Critical);

        let plan = warmer.plan(WarmingStrategy::CallGraphOrder);
        let b_entry = plan.entries.iter().find(|e| e.def_path == "b").unwrap();
        assert_eq!(b_entry.priority, WarmingPriority::Critical);
    }

    #[test]
    fn test_hot_count_infers_priority() {
        let mut warmer = CacheWarmer::new();
        warmer.set_hot_count("hot_fn", 200);
        warmer.set_hot_count("warm_fn", 50);
        warmer.set_hot_count("cold_fn", 2);

        let plan = warmer.plan(WarmingStrategy::HotFunctions);
        let hot = plan
            .entries
            .iter()
            .find(|e| e.def_path == "hot_fn")
            .unwrap();
        assert_eq!(hot.priority, WarmingPriority::Critical);

        let warm = plan
            .entries
            .iter()
            .find(|e| e.def_path == "warm_fn")
            .unwrap();
        assert_eq!(warm.priority, WarmingPriority::High);
    }

    #[test]
    fn test_filter_by_priority() {
        let plan = WarmingPlan {
            functions: vec!["a".into(), "b".into(), "c".into()],
            strategy: WarmingStrategy::PreviousSession,
            entries: vec![
                WarmingEntry {
                    def_path: "a".into(),
                    priority: WarmingPriority::Low,
                },
                WarmingEntry {
                    def_path: "b".into(),
                    priority: WarmingPriority::High,
                },
                WarmingEntry {
                    def_path: "c".into(),
                    priority: WarmingPriority::Critical,
                },
            ],
        };

        let high_plus = plan.filter_by_priority(WarmingPriority::High);
        assert_eq!(high_plus, vec!["b", "c"]);

        let critical = plan.filter_by_priority(WarmingPriority::Critical);
        assert_eq!(critical, vec!["c"]);

        let all = plan.filter_by_priority(WarmingPriority::Low);
        assert_eq!(all.len(), 3);
    }

    // -----------------------------------------------------------------------
    // Progress tracking tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_warming_progress_basic() {
        let progress = WarmingProgress::new(10);
        assert_eq!(progress.total(), 10);
        assert_eq!(progress.completed(), 0);
        assert_eq!(progress.failed(), 0);
        assert!(!progress.is_done());
        assert!(!progress.is_cancelled());
        assert!((progress.fraction() - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_warming_progress_completion() {
        let progress = WarmingProgress::new(4);
        progress.record_completed();
        progress.record_completed();
        progress.record_failed();
        progress.record_completed();

        assert_eq!(progress.completed(), 3);
        assert_eq!(progress.failed(), 1);
        assert!((progress.fraction() - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_warming_progress_cancel() {
        let progress = WarmingProgress::new(10);
        assert!(!progress.is_cancelled());
        progress.cancel();
        assert!(progress.is_cancelled());
    }

    #[test]
    fn test_warming_progress_done() {
        let progress = WarmingProgress::new(10);
        assert!(!progress.is_done());
        progress.mark_done();
        assert!(progress.is_done());
    }

    #[test]
    fn test_warming_progress_zero_total() {
        let progress = WarmingProgress::new(0);
        // fraction should be 1.0 (nothing to do = complete)
        assert!((progress.fraction() - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_warming_progress_snapshot() {
        let progress = WarmingProgress::new(5);
        progress.record_completed();
        progress.record_completed();
        progress.record_failed();

        let snap = progress.snapshot();
        assert_eq!(snap.total, 5);
        assert_eq!(snap.completed, 2);
        assert_eq!(snap.failed, 1);
        assert!(!snap.is_cancelled);
        assert!(!snap.is_done);
        assert!((snap.fraction - 0.6).abs() < f64::EPSILON);
    }

    // -----------------------------------------------------------------------
    // Background warming handle tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_background_warming_handle() {
        let mut warmer = CacheWarmer::new();
        warmer.set_hot_count("fn_a", 100);
        warmer.set_hot_count("fn_b", 50);

        let handle = warmer.start_background_warming(WarmingStrategy::HotFunctions);
        assert!(!handle.is_done());
        assert_eq!(handle.plan.functions.len(), 2);

        // Simulate warming
        handle.progress.record_completed();
        handle.progress.record_completed();
        handle.progress.mark_done();

        assert!(handle.is_done());
        let snap = handle.snapshot();
        assert_eq!(snap.completed, 2);
        assert_eq!(snap.total, 2);
    }

    #[test]
    fn test_background_warming_cancel() {
        let mut warmer = CacheWarmer::new();
        warmer.set_hot_count("fn_a", 10);

        let handle = warmer.start_background_warming(WarmingStrategy::HotFunctions);
        handle.cancel();

        assert!(handle.progress.is_cancelled());
    }

    #[test]
    fn test_background_warming_shared_progress() {
        let mut warmer = CacheWarmer::new();
        warmer.set_hot_count("fn_a", 10);

        let handle = warmer.start_background_warming(WarmingStrategy::HotFunctions);
        let progress = Arc::clone(&handle.progress);

        // Simulate another "thread" updating progress
        progress.record_completed();
        assert_eq!(handle.progress.completed(), 1);
    }
}
