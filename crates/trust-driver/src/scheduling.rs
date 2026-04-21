// trust-driver/scheduling.rs: Verification scheduling and prioritization
//
// Determines the order in which functions are verified, grouping independent
// functions into parallel batches and applying various scheduling strategies
// (topological, priority-based, critical-path-first, parallel waves).
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::{FxHashMap, FxHashSet};
use std::time::Duration;

use crate::incremental::DependencyGraph;

// ---------------------------------------------------------------------------
// Scheduling strategy
// ---------------------------------------------------------------------------

/// Strategy for ordering functions during verification.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum ScheduleOrder {
    /// Verify callees before callers (topological order of call graph).
    TopologicalCallGraph,
    /// Sort by user-assigned priority (highest first).
    PriorityBased,
    /// Verify the critical path (longest dependency chain) first.
    CriticalPathFirst,
    /// Group independent functions into parallel waves.
    ParallelWaves,
}

// ---------------------------------------------------------------------------
// Verification batch
// ---------------------------------------------------------------------------

/// A batch of functions that can be verified in parallel.
///
/// Functions within a batch have no mutual dependencies, so they can
/// be dispatched to parallel workers simultaneously.
#[derive(Debug, Clone)]
pub(crate) struct VerificationBatch {
    /// Functions in this batch (can be verified concurrently).
    pub functions: Vec<String>,
    /// Wave number (0-indexed). Wave 0 runs first.
    pub wave: usize,
}

impl VerificationBatch {
    /// Number of functions in this batch.
    #[must_use]
    pub(crate) fn len(&self) -> usize {
        self.functions.len()
    }

    /// Whether this batch is empty.
    #[must_use]
    pub(crate) fn is_empty(&self) -> bool {
        self.functions.is_empty()
    }
}

// ---------------------------------------------------------------------------
// Resource budget
// ---------------------------------------------------------------------------

/// Tracks the remaining verification budget (time and memory).
#[derive(Debug, Clone)]
pub(crate) struct ResourceBudget {
    /// Total time budget for all verification.
    pub total_time: Duration,
    /// Time remaining.
    pub remaining_time: Duration,
    /// Maximum memory in bytes (0 = unlimited).
    pub max_memory_bytes: u64,
    /// Functions verified so far.
    pub functions_verified: usize,
    /// Total functions to verify.
    pub total_functions: usize,
}

impl ResourceBudget {
    /// Create a new budget with the given time limit.
    #[must_use]
    pub(crate) fn new(total_time: Duration, total_functions: usize) -> Self {
        Self {
            total_time,
            remaining_time: total_time,
            max_memory_bytes: 0,
            functions_verified: 0,
            total_functions,
        }
    }

    /// Create an unlimited budget.
    #[must_use]
    pub(crate) fn unlimited(total_functions: usize) -> Self {
        Self {
            total_time: Duration::from_secs(u64::MAX),
            remaining_time: Duration::from_secs(u64::MAX),
            max_memory_bytes: 0,
            functions_verified: 0,
            total_functions,
        }
    }

    /// Record that a function was verified, consuming time from the budget.
    pub(crate) fn record(&mut self, elapsed: Duration) {
        self.remaining_time = self.remaining_time.saturating_sub(elapsed);
        self.functions_verified += 1;
    }

    /// Whether the budget has been exhausted.
    #[must_use]
    pub(crate) fn is_exhausted(&self) -> bool {
        self.remaining_time.is_zero()
    }

    /// Fraction of the budget remaining (0.0 to 1.0).
    #[must_use]
    pub(crate) fn fraction_remaining(&self) -> f64 {
        if self.total_time.is_zero() {
            return 0.0;
        }
        self.remaining_time.as_secs_f64() / self.total_time.as_secs_f64()
    }

    /// Estimated time per function based on elapsed history.
    #[must_use]
    pub(crate) fn avg_time_per_function(&self) -> Duration {
        if self.functions_verified == 0 {
            return Duration::ZERO;
        }
        let elapsed = self.total_time.saturating_sub(self.remaining_time);
        elapsed / self.functions_verified as u32
    }
}

// ---------------------------------------------------------------------------
// Cost estimation
// ---------------------------------------------------------------------------

/// Estimate the verification cost of a function based on heuristics.
///
/// Uses a simple model: cost is proportional to the number of basic blocks
/// (approximated by `complexity_hint`), with a minimum floor.
#[must_use]
pub(crate) fn estimate_cost(complexity_hint: usize) -> Duration {
    // Base cost: 100ms. Each unit of complexity adds 50ms.
    let base_ms = 100u64;
    let per_unit_ms = 50u64;
    Duration::from_millis(base_ms + per_unit_ms * complexity_hint as u64)
}

/// Estimate cost for a named function given a complexity map.
#[must_use]
pub(crate) fn estimate_cost_for(fn_name: &str, complexity_map: &FxHashMap<String, usize>) -> Duration {
    let complexity = complexity_map.get(fn_name).copied().unwrap_or(1);
    estimate_cost(complexity)
}

// ---------------------------------------------------------------------------
// Critical path analysis
// ---------------------------------------------------------------------------

/// Compute the critical path: the longest chain in the dependency graph,
/// measured by estimated verification cost.
///
/// Returns the functions on the critical path in order (leaf to root),
/// along with the total estimated cost.
#[must_use]
pub(crate) fn critical_path(
    graph: &DependencyGraph,
    complexity_map: &FxHashMap<String, usize>,
) -> (Vec<String>, Duration) {
    let all_fns = graph.all_functions();
    if all_fns.is_empty() {
        return (Vec::new(), Duration::ZERO);
    }

    // Compute longest path using dynamic programming on topological order.
    let topo = match graph.topological_order() {
        Some(order) => order,
        None => {
            // Graph has cycles -- fall back to returning all functions
            // sorted by complexity descending.
            let mut fns: Vec<String> = all_fns.into_iter().collect();
            fns.sort_by(|a, b| {
                let ca = complexity_map.get(a).copied().unwrap_or(1);
                let cb = complexity_map.get(b).copied().unwrap_or(1);
                cb.cmp(&ca)
            });
            let total: Duration = fns.iter().map(|f| estimate_cost_for(f, complexity_map)).sum();
            return (fns, total);
        }
    };

    // dist[f] = longest path ending at f (in ms)
    let mut dist: FxHashMap<String, u64> = FxHashMap::default();
    // pred[f] = predecessor on the longest path
    let mut pred: FxHashMap<String, Option<String>> = FxHashMap::default();

    for func in &topo {
        let cost = estimate_cost_for(func, complexity_map).as_millis() as u64;
        dist.insert(func.clone(), cost);
        pred.insert(func.clone(), None);
    }

    // Process in topological order. For each function, update its callers.
    for func in &topo {
        let func_dist = dist[func];
        let callers = graph.callers_of(func);
        for caller in callers {
            let caller_cost = estimate_cost_for(&caller, complexity_map).as_millis() as u64;
            let new_dist = func_dist + caller_cost;
            let current = dist.get(&caller).copied().unwrap_or(0);
            if new_dist > current {
                dist.insert(caller.clone(), new_dist);
                pred.insert(caller.clone(), Some(func.clone()));
            }
        }
    }

    // Find the function with the longest path.
    let (end_fn, max_cost) =
        dist.iter().max_by_key(|(_, &d)| d).map(|(f, &d)| (f.clone(), d)).unwrap_or_default();

    // Trace back the path.
    let mut path = Vec::new();
    let mut current = Some(end_fn);
    let mut visited = FxHashSet::default();
    while let Some(ref func) = current {
        if !visited.insert(func.clone()) {
            break; // Safety: prevent infinite loop on unexpected cycle.
        }
        path.push(func.clone());
        current = pred.get(func).cloned().flatten();
    }

    // Path is from end (root) to start (leaf). Reverse for leaf-to-root.
    path.reverse();
    (path, Duration::from_millis(max_cost))
}

// ---------------------------------------------------------------------------
// Scheduler
// ---------------------------------------------------------------------------

/// Plans verification schedules based on dependency graphs and strategies.
pub(crate) struct VerificationScheduler {
    /// User-assigned priorities (higher = more important).
    priorities: FxHashMap<String, u32>,
    /// Complexity hints for cost estimation.
    complexity: FxHashMap<String, usize>,
}

impl VerificationScheduler {
    /// Create a scheduler with no priorities or complexity hints.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self { priorities: FxHashMap::default(), complexity: FxHashMap::default() }
    }

    /// Set the priority for a function (higher = verified sooner).
    pub(crate) fn set_priority(&mut self, fn_name: &str, priority: u32) {
        self.priorities.insert(fn_name.to_string(), priority);
    }

    /// Set the complexity hint for a function.
    pub(crate) fn set_complexity(&mut self, fn_name: &str, complexity: usize) {
        self.complexity.insert(fn_name.to_string(), complexity);
    }

    /// Plan a verification schedule for the given functions.
    ///
    /// Returns a sequence of `VerificationBatch`es. Each batch contains
    /// functions that can be verified in parallel. Batches must be
    /// executed in order.
    #[must_use]
    pub(crate) fn plan_schedule(
        &self,
        functions: &[String],
        deps: &DependencyGraph,
        order: ScheduleOrder,
    ) -> Vec<VerificationBatch> {
        match order {
            ScheduleOrder::TopologicalCallGraph => self.plan_topological(functions, deps),
            ScheduleOrder::PriorityBased => self.plan_priority(functions),
            ScheduleOrder::CriticalPathFirst => self.plan_critical_path(functions, deps),
            ScheduleOrder::ParallelWaves => self.plan_parallel_waves(functions, deps),
        }
    }

    /// Topological ordering: verify callees before callers.
    /// Each batch contains functions at the same depth level.
    fn plan_topological(
        &self,
        functions: &[String],
        deps: &DependencyGraph,
    ) -> Vec<VerificationBatch> {
        let fn_set: FxHashSet<String> = functions.iter().cloned().collect();

        // Build a sub-graph restricted to the requested functions.
        let mut in_degree: FxHashMap<String, usize> = FxHashMap::default();
        for func in functions {
            let callees = deps.callees_of(func);
            let relevant_callees: usize = callees.iter().filter(|c| fn_set.contains(*c)).count();
            in_degree.insert(func.clone(), relevant_callees);
        }

        let mut batches = Vec::new();
        let mut remaining: FxHashSet<String> = fn_set;
        let mut wave = 0usize;

        while !remaining.is_empty() {
            // Find functions with in-degree 0 (all dependencies resolved).
            let mut ready: Vec<String> = remaining
                .iter()
                .filter(|f| in_degree.get(*f).copied().unwrap_or(0) == 0)
                .cloned()
                .collect();
            ready.sort(); // Deterministic ordering.

            if ready.is_empty() {
                // Cycle in remaining functions -- break the cycle by
                // taking all remaining functions.
                let mut all: Vec<String> = remaining.into_iter().collect();
                all.sort();
                batches.push(VerificationBatch { functions: all, wave });
                break;
            }

            // Remove ready functions and update in-degrees.
            for func in &ready {
                remaining.remove(func);
                let callers = deps.callers_of(func);
                for caller in callers {
                    if let Some(deg) = in_degree.get_mut(&caller) {
                        *deg = deg.saturating_sub(1);
                    }
                }
            }

            batches.push(VerificationBatch { functions: ready, wave });
            wave += 1;
        }

        batches
    }

    /// Priority-based: sort by priority descending, put all in one batch.
    fn plan_priority(&self, functions: &[String]) -> Vec<VerificationBatch> {
        let mut sorted: Vec<String> = functions.to_vec();
        sorted.sort_by(|a, b| {
            let pa = self.priorities.get(a).copied().unwrap_or(0);
            let pb = self.priorities.get(b).copied().unwrap_or(0);
            pb.cmp(&pa).then_with(|| a.cmp(b))
        });

        if sorted.is_empty() {
            return Vec::new();
        }

        vec![VerificationBatch { functions: sorted, wave: 0 }]
    }

    /// Critical-path-first: put the critical path functions first, then the rest.
    fn plan_critical_path(
        &self,
        functions: &[String],
        deps: &DependencyGraph,
    ) -> Vec<VerificationBatch> {
        let (cp, _cost) = critical_path(deps, &self.complexity);
        let fn_set: FxHashSet<String> = functions.iter().cloned().collect();

        // Critical path functions that are in our function set.
        let cp_fns: Vec<String> = cp.into_iter().filter(|f| fn_set.contains(f)).collect();
        let cp_set: FxHashSet<String> = cp_fns.iter().cloned().collect();

        // Non-critical functions.
        let mut rest: Vec<String> =
            functions.iter().filter(|f| !cp_set.contains(*f)).cloned().collect();
        rest.sort();

        let mut batches = Vec::new();
        if !cp_fns.is_empty() {
            batches.push(VerificationBatch { functions: cp_fns, wave: 0 });
        }
        if !rest.is_empty() {
            batches.push(VerificationBatch { functions: rest, wave: batches.len() });
        }

        batches
    }

    /// Parallel waves: group independent functions into waves using the
    /// topological level-set approach.
    fn plan_parallel_waves(
        &self,
        functions: &[String],
        deps: &DependencyGraph,
    ) -> Vec<VerificationBatch> {
        // Same as topological, which already produces wave-based batches.
        self.plan_topological(functions, deps)
    }

    /// Dynamically reorder a schedule based on early verification results.
    ///
    /// If a function in an early batch failed, promote its callers to
    /// earlier batches so they can be skipped / given reduced budgets.
    /// If a function succeeded quickly, deprioritize its callers (they
    /// are less likely to have issues).
    #[must_use]
    pub(crate) fn dynamic_reorder(
        &self,
        schedule: &[VerificationBatch],
        results: &FxHashMap<String, VerificationOutcome>,
        deps: &DependencyGraph,
    ) -> Vec<VerificationBatch> {
        // Collect failed and fast functions.
        let mut failed_callers: FxHashSet<String> = FxHashSet::default();
        let mut fast_callers: FxHashSet<String> = FxHashSet::default();

        for (fn_name, outcome) in results {
            match outcome {
                VerificationOutcome::Failed | VerificationOutcome::Timeout => {
                    // Promote callers: they depend on a failed function.
                    let callers = deps.callers_of(fn_name);
                    failed_callers.extend(callers);
                }
                VerificationOutcome::ProvedFast => {
                    let callers = deps.callers_of(fn_name);
                    fast_callers.extend(callers);
                }
                _ => {}
            }
        }

        // Remove already-verified functions from the schedule.
        let verified: FxHashSet<String> = results.keys().cloned().collect();

        let mut reordered: Vec<VerificationBatch> = Vec::new();

        // First batch: callers of failed functions (need attention).
        let promoted: Vec<String> =
            failed_callers.iter().filter(|f| !verified.contains(*f)).cloned().collect();

        let promoted_set: FxHashSet<String> = promoted.iter().cloned().collect();

        if !promoted.is_empty() {
            let mut sorted = promoted;
            sorted.sort();
            reordered.push(VerificationBatch { functions: sorted, wave: 0 });
        }

        // Remaining batches: filter out verified and promoted functions,
        // deprioritize callers of fast functions by moving them last.
        let mut normal = Vec::new();
        let mut deprioritized = Vec::new();

        for batch in schedule {
            for func in &batch.functions {
                if verified.contains(func) || promoted_set.contains(func) {
                    continue;
                }
                if fast_callers.contains(func) {
                    deprioritized.push(func.clone());
                } else {
                    normal.push(func.clone());
                }
            }
        }

        if !normal.is_empty() {
            normal.sort();
            reordered.push(VerificationBatch { functions: normal, wave: reordered.len() });
        }

        if !deprioritized.is_empty() {
            deprioritized.sort();
            reordered.push(VerificationBatch { functions: deprioritized, wave: reordered.len() });
        }

        reordered
    }
}

impl Default for VerificationScheduler {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Verification outcome (for dynamic reordering)
// ---------------------------------------------------------------------------

/// Simplified outcome for scheduling decisions.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum VerificationOutcome {
    /// Proved and took a long time.
    Proved,
    /// Proved and completed quickly (< estimated cost).
    ProvedFast,
    /// Verification failed.
    Failed,
    /// Timed out.
    Timeout,
    /// Unknown / inconclusive.
    Unknown,
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // -- Helpers --

    fn make_linear_graph() -> DependencyGraph {
        let mut g = DependencyGraph::new();
        // entry -> middle -> leaf
        g.add_edge("entry", "middle");
        g.add_edge("middle", "leaf");
        g
    }

    fn make_diamond_graph() -> DependencyGraph {
        let mut g = DependencyGraph::new();
        // top -> left, top -> right, left -> bottom, right -> bottom
        g.add_edge("top", "left");
        g.add_edge("top", "right");
        g.add_edge("left", "bottom");
        g.add_edge("right", "bottom");
        g
    }

    fn all_functions(batches: &[VerificationBatch]) -> Vec<String> {
        batches.iter().flat_map(|b| b.functions.clone()).collect()
    }

    // -- VerificationBatch tests --

    #[test]
    fn test_batch_len_and_empty() {
        let batch = VerificationBatch { functions: vec!["a".into(), "b".into()], wave: 0 };
        assert_eq!(batch.len(), 2);
        assert!(!batch.is_empty());

        let empty_batch = VerificationBatch { functions: Vec::new(), wave: 0 };
        assert!(empty_batch.is_empty());
    }

    // -- ResourceBudget tests --

    #[test]
    fn test_budget_record_and_exhaustion() {
        let mut budget = ResourceBudget::new(Duration::from_secs(10), 5);
        assert!(!budget.is_exhausted());
        assert_eq!(budget.functions_verified, 0);

        budget.record(Duration::from_secs(6));
        assert_eq!(budget.functions_verified, 1);
        assert_eq!(budget.remaining_time, Duration::from_secs(4));
        assert!(!budget.is_exhausted());

        budget.record(Duration::from_secs(5));
        assert!(budget.is_exhausted());
        assert_eq!(budget.functions_verified, 2);
    }

    #[test]
    fn test_budget_fraction_remaining() {
        let mut budget = ResourceBudget::new(Duration::from_secs(100), 10);
        assert!((budget.fraction_remaining() - 1.0).abs() < f64::EPSILON);

        budget.record(Duration::from_secs(25));
        assert!((budget.fraction_remaining() - 0.75).abs() < 0.01);
    }

    #[test]
    fn test_budget_unlimited() {
        let budget = ResourceBudget::unlimited(100);
        assert!(!budget.is_exhausted());
    }

    #[test]
    fn test_budget_avg_time_no_functions() {
        let budget = ResourceBudget::new(Duration::from_secs(10), 5);
        assert_eq!(budget.avg_time_per_function(), Duration::ZERO);
    }

    #[test]
    fn test_budget_avg_time_with_functions() {
        let mut budget = ResourceBudget::new(Duration::from_secs(10), 5);
        budget.record(Duration::from_secs(2));
        budget.record(Duration::from_secs(4));
        // Elapsed: 6s, verified: 2 -> avg 3s
        assert_eq!(budget.avg_time_per_function(), Duration::from_secs(3));
    }

    // -- Cost estimation tests --

    #[test]
    fn test_estimate_cost_baseline() {
        let cost = estimate_cost(0);
        assert_eq!(cost, Duration::from_millis(100));
    }

    #[test]
    fn test_estimate_cost_scales_with_complexity() {
        let c1 = estimate_cost(1);
        let c5 = estimate_cost(5);
        assert!(c5 > c1);
        assert_eq!(c1, Duration::from_millis(150));
        assert_eq!(c5, Duration::from_millis(350));
    }

    #[test]
    fn test_estimate_cost_for_missing_function() {
        let map = FxHashMap::default();
        let cost = estimate_cost_for("unknown_fn", &map);
        // Default complexity = 1 -> 150ms
        assert_eq!(cost, Duration::from_millis(150));
    }

    // -- Critical path tests --

    #[test]
    fn test_critical_path_linear() {
        let g = make_linear_graph();
        let complexity = FxHashMap::default(); // all default
        let (path, cost) = critical_path(&g, &complexity);

        // Linear chain: leaf -> middle -> entry
        // Each has cost 150ms (complexity 1), total chain = 450ms
        assert_eq!(path.len(), 3);
        assert_eq!(path[0], "leaf");
        assert_eq!(path[2], "entry");
        assert_eq!(cost, Duration::from_millis(450));
    }

    #[test]
    fn test_critical_path_diamond() {
        let g = make_diamond_graph();
        let mut complexity = FxHashMap::default();
        complexity.insert("left".to_string(), 10); // Make left expensive
        let (path, _cost) = critical_path(&g, &complexity);

        // Critical path should go through the expensive left branch:
        // bottom -> left -> top
        assert!(path.contains(&"left".to_string()));
        assert!(path.contains(&"bottom".to_string()));
        assert!(path.contains(&"top".to_string()));
    }

    #[test]
    fn test_critical_path_empty_graph() {
        let g = DependencyGraph::new();
        let (path, cost) = critical_path(&g, &FxHashMap::default());
        assert!(path.is_empty());
        assert_eq!(cost, Duration::ZERO);
    }

    // -- Topological scheduling tests --

    #[test]
    fn test_schedule_topological_linear() {
        let g = make_linear_graph();
        let scheduler = VerificationScheduler::new();
        let fns = vec!["entry".into(), "middle".into(), "leaf".into()];

        let batches = scheduler.plan_schedule(&fns, &g, ScheduleOrder::TopologicalCallGraph);

        // Wave 0: leaf (no callees in set)
        // Wave 1: middle (depends on leaf)
        // Wave 2: entry (depends on middle)
        assert_eq!(batches.len(), 3);
        assert_eq!(batches[0].functions, vec!["leaf"]);
        assert_eq!(batches[1].functions, vec!["middle"]);
        assert_eq!(batches[2].functions, vec!["entry"]);
    }

    #[test]
    fn test_schedule_topological_diamond() {
        let g = make_diamond_graph();
        let scheduler = VerificationScheduler::new();
        let fns = vec!["top".into(), "left".into(), "right".into(), "bottom".into()];

        let batches = scheduler.plan_schedule(&fns, &g, ScheduleOrder::TopologicalCallGraph);

        // Wave 0: bottom
        // Wave 1: left, right (parallel)
        // Wave 2: top
        assert_eq!(batches.len(), 3);
        assert_eq!(batches[0].functions, vec!["bottom"]);
        assert!(batches[1].functions.contains(&"left".to_string()));
        assert!(batches[1].functions.contains(&"right".to_string()));
        assert_eq!(batches[2].functions, vec!["top"]);
    }

    #[test]
    fn test_schedule_topological_subset() {
        let g = make_linear_graph();
        let scheduler = VerificationScheduler::new();
        // Only verify entry and leaf, skip middle
        let fns = vec!["entry".into(), "leaf".into()];

        let batches = scheduler.plan_schedule(&fns, &g, ScheduleOrder::TopologicalCallGraph);

        let all = all_functions(&batches);
        assert_eq!(all.len(), 2);
        assert!(all.contains(&"entry".to_string()));
        assert!(all.contains(&"leaf".to_string()));
    }

    // -- Priority scheduling tests --

    #[test]
    fn test_schedule_priority() {
        let g = DependencyGraph::new();
        let mut scheduler = VerificationScheduler::new();
        scheduler.set_priority("low_fn", 1);
        scheduler.set_priority("high_fn", 10);
        scheduler.set_priority("mid_fn", 5);

        let fns = vec!["low_fn".into(), "high_fn".into(), "mid_fn".into()];
        let batches = scheduler.plan_schedule(&fns, &g, ScheduleOrder::PriorityBased);

        assert_eq!(batches.len(), 1);
        assert_eq!(batches[0].functions[0], "high_fn");
        assert_eq!(batches[0].functions[1], "mid_fn");
        assert_eq!(batches[0].functions[2], "low_fn");
    }

    #[test]
    fn test_schedule_priority_default_zero() {
        let g = DependencyGraph::new();
        let mut scheduler = VerificationScheduler::new();
        scheduler.set_priority("important", 100);

        let fns = vec!["important".into(), "normal".into()];
        let batches = scheduler.plan_schedule(&fns, &g, ScheduleOrder::PriorityBased);

        assert_eq!(batches[0].functions[0], "important");
    }

    // -- Critical path scheduling tests --

    #[test]
    fn test_schedule_critical_path_first() {
        let g = make_linear_graph();
        let scheduler = VerificationScheduler::new();
        let mut fns = vec!["entry".into(), "middle".into(), "leaf".into(), "isolated".into()];

        // Add an isolated function to the graph
        let mut g2 = g;
        g2.add_function("isolated");
        fns.sort();

        let batches = scheduler.plan_schedule(&fns, &g2, ScheduleOrder::CriticalPathFirst);

        // First batch: critical path (leaf, middle, entry)
        // Second batch: isolated
        assert!(!batches.is_empty());
        let first_batch_set: FxHashSet<String> = batches[0].functions.iter().cloned().collect();
        assert!(first_batch_set.contains("leaf"));
        assert!(first_batch_set.contains("middle"));
        assert!(first_batch_set.contains("entry"));
    }

    // -- Parallel waves scheduling tests --

    #[test]
    fn test_schedule_parallel_waves() {
        let g = make_diamond_graph();
        let scheduler = VerificationScheduler::new();
        let fns = vec!["top".into(), "left".into(), "right".into(), "bottom".into()];

        let batches = scheduler.plan_schedule(&fns, &g, ScheduleOrder::ParallelWaves);

        // Same as topological: wave 0 = bottom, wave 1 = left+right, wave 2 = top
        assert_eq!(batches.len(), 3);
        assert_eq!(batches[0].wave, 0);
        assert_eq!(batches[1].wave, 1);
        assert_eq!(batches[2].wave, 2);
        assert_eq!(batches[1].functions.len(), 2); // left and right in parallel
    }

    // -- Dynamic reordering tests --

    #[test]
    fn test_dynamic_reorder_promotes_failed_callers() {
        let g = make_linear_graph();
        let scheduler = VerificationScheduler::new();

        let initial = vec![
            VerificationBatch { functions: vec!["leaf".into()], wave: 0 },
            VerificationBatch { functions: vec!["middle".into()], wave: 1 },
            VerificationBatch { functions: vec!["entry".into()], wave: 2 },
        ];

        // leaf failed -> middle (its caller) should be promoted
        let mut results = FxHashMap::default();
        results.insert("leaf".to_string(), VerificationOutcome::Failed);

        let reordered = scheduler.dynamic_reorder(&initial, &results, &g);

        // First batch should contain middle (promoted)
        let first_fns: FxHashSet<String> = reordered[0].functions.iter().cloned().collect();
        assert!(first_fns.contains("middle"));
    }

    #[test]
    fn test_dynamic_reorder_deprioritizes_fast_callers() {
        let g = make_linear_graph();
        let scheduler = VerificationScheduler::new();

        let initial =
            vec![VerificationBatch { functions: vec!["middle".into(), "entry".into()], wave: 0 }];

        // leaf proved fast -> middle (its caller) gets deprioritized
        let mut results = FxHashMap::default();
        results.insert("leaf".to_string(), VerificationOutcome::ProvedFast);

        let reordered = scheduler.dynamic_reorder(&initial, &results, &g);

        // entry should come before middle (middle is deprioritized)
        let all = all_functions(&reordered);
        let pos_entry = all.iter().position(|f| f == "entry");
        let pos_middle = all.iter().position(|f| f == "middle");
        assert!(pos_entry < pos_middle);
    }

    #[test]
    fn test_dynamic_reorder_removes_verified() {
        let g = DependencyGraph::new();
        let scheduler = VerificationScheduler::new();

        let initial = vec![VerificationBatch {
            functions: vec!["a".into(), "b".into(), "c".into()],
            wave: 0,
        }];

        let mut results = FxHashMap::default();
        results.insert("a".to_string(), VerificationOutcome::Proved);
        results.insert("b".to_string(), VerificationOutcome::Proved);

        let reordered = scheduler.dynamic_reorder(&initial, &results, &g);
        let all = all_functions(&reordered);

        assert!(!all.contains(&"a".to_string()));
        assert!(!all.contains(&"b".to_string()));
        assert!(all.contains(&"c".to_string()));
    }

    // -- Empty/edge case tests --

    #[test]
    fn test_schedule_empty_functions() {
        let g = DependencyGraph::new();
        let scheduler = VerificationScheduler::new();
        let batches = scheduler.plan_schedule(&[], &g, ScheduleOrder::TopologicalCallGraph);
        assert!(batches.is_empty());
    }

    #[test]
    fn test_schedule_single_function() {
        let mut g = DependencyGraph::new();
        g.add_function("solo");
        let scheduler = VerificationScheduler::new();
        let batches =
            scheduler.plan_schedule(&["solo".into()], &g, ScheduleOrder::TopologicalCallGraph);
        assert_eq!(batches.len(), 1);
        assert_eq!(batches[0].functions, vec!["solo"]);
    }

    #[test]
    fn test_schedule_priority_empty() {
        let g = DependencyGraph::new();
        let scheduler = VerificationScheduler::new();
        let batches = scheduler.plan_schedule(&[], &g, ScheduleOrder::PriorityBased);
        assert!(batches.is_empty());
    }

    #[test]
    fn test_all_schedule_orders_cover_all_functions() {
        let g = make_diamond_graph();
        let scheduler = VerificationScheduler::new();
        let fns: Vec<String> = vec!["top".into(), "left".into(), "right".into(), "bottom".into()];

        for order in [
            ScheduleOrder::TopologicalCallGraph,
            ScheduleOrder::PriorityBased,
            ScheduleOrder::CriticalPathFirst,
            ScheduleOrder::ParallelWaves,
        ] {
            let batches = scheduler.plan_schedule(&fns, &g, order);
            let all = all_functions(&batches);
            let all_set: FxHashSet<String> = all.into_iter().collect();
            let expected: FxHashSet<String> = fns.iter().cloned().collect();
            assert_eq!(all_set, expected, "order {order:?} should cover all functions");
        }
    }
}
