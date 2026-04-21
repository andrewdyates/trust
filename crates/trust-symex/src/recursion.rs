// trust-symex/recursion.rs: Bounded recursion analysis (#253)
//
// Detects recursive function calls in call graphs, enforces recursion
// depth bounds for verification, and generates ranking functions for
// termination proofs.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::{FxHashMap, FxHashSet};

// ---------------------------------------------------------------------------
// Recursion detection
// ---------------------------------------------------------------------------

/// A call graph for recursion analysis.
#[derive(Debug, Clone)]
pub(crate) struct CallGraph {
    /// Adjacency list: caller -> list of callees.
    edges: FxHashMap<String, Vec<String>>,
}

impl CallGraph {
    /// Create a new empty call graph.
    pub(crate) fn new() -> Self {
        Self {
            edges: FxHashMap::default(),
        }
    }

    /// Add a call edge from `caller` to `callee`.
    pub(crate) fn add_edge(&mut self, caller: impl Into<String>, callee: impl Into<String>) {
        self.edges.entry(caller.into()).or_default().push(callee.into());
    }

    /// Get callees of a function.
    #[must_use]
    pub(crate) fn callees(&self, func: &str) -> &[String] {
        self.edges.get(func).map_or(&[], |v| v.as_slice())
    }

    /// Get all function names in the graph.
    #[must_use]
    pub(crate) fn functions(&self) -> Vec<&str> {
        let mut fns: FxHashSet<&str> = FxHashSet::default();
        for (caller, callees) in &self.edges {
            fns.insert(caller);
            for callee in callees {
                fns.insert(callee);
            }
        }
        let mut result: Vec<_> = fns.into_iter().collect();
        result.sort();
        result
    }
}

impl Default for CallGraph {
    fn default() -> Self {
        Self::new()
    }
}

/// Result of recursion detection.
#[derive(Debug, Clone)]
pub(crate) struct RecursionInfo {
    /// Direct self-recursive functions (A calls A).
    pub self_recursive: Vec<String>,
    /// Mutually recursive groups (A calls B calls A).
    pub mutual_groups: Vec<Vec<String>>,
    /// All functions involved in any recursion.
    pub recursive_functions: FxHashSet<String>,
}

/// Detect all recursive patterns in a call graph.
pub(crate) fn detect_recursion(graph: &CallGraph) -> RecursionInfo {
    let mut info = RecursionInfo {
        self_recursive: Vec::new(),
        mutual_groups: Vec::new(),
        recursive_functions: FxHashSet::default(),
    };

    // Detect self-recursion.
    for (caller, callees) in &graph.edges {
        if callees.contains(caller) {
            info.self_recursive.push(caller.clone());
            info.recursive_functions.insert(caller.clone());
        }
    }

    // Detect mutual recursion via Tarjan's SCC algorithm.
    let sccs = tarjan_scc(graph);
    for scc in &sccs {
        if scc.len() > 1 {
            info.mutual_groups.push(scc.clone());
            for func in scc {
                info.recursive_functions.insert(func.clone());
            }
        }
    }

    info
}

/// Tarjan's algorithm for strongly connected components.
fn tarjan_scc(graph: &CallGraph) -> Vec<Vec<String>> {
    struct TarjanState {
        index_counter: usize,
        stack: Vec<String>,
        on_stack: FxHashSet<String>,
        indices: FxHashMap<String, usize>,
        lowlinks: FxHashMap<String, usize>,
        sccs: Vec<Vec<String>>,
    }

    fn strongconnect(v: &str, graph: &CallGraph, state: &mut TarjanState) {
        state.indices.insert(v.to_string(), state.index_counter);
        state.lowlinks.insert(v.to_string(), state.index_counter);
        state.index_counter += 1;
        state.stack.push(v.to_string());
        state.on_stack.insert(v.to_string());

        for w in graph.callees(v) {
            if !state.indices.contains_key(w.as_str()) {
                strongconnect(w, graph, state);
                let w_low = state.lowlinks[w.as_str()];
                let v_low = state.lowlinks[v];
                if w_low < v_low {
                    state.lowlinks.insert(v.to_string(), w_low);
                }
            } else if state.on_stack.contains(w.as_str()) {
                let w_idx = state.indices[w.as_str()];
                let v_low = state.lowlinks[v];
                if w_idx < v_low {
                    state.lowlinks.insert(v.to_string(), w_idx);
                }
            }
        }

        if state.lowlinks[v] == state.indices[v] {
            let mut scc = Vec::new();
            while let Some(w) = state.stack.pop() {
                state.on_stack.remove(&w);
                scc.push(w.clone());
                if w == v {
                    break;
                }
            }
            scc.reverse();
            state.sccs.push(scc);
        }
    }

    let mut state = TarjanState {
        index_counter: 0,
        stack: Vec::new(),
        on_stack: FxHashSet::default(),
        indices: FxHashMap::default(),
        lowlinks: FxHashMap::default(),
        sccs: Vec::new(),
    };

    for func in graph.functions() {
        if !state.indices.contains_key(func) {
            strongconnect(func, graph, &mut state);
        }
    }

    state.sccs
}

// ---------------------------------------------------------------------------
// Bounded recursion
// ---------------------------------------------------------------------------

/// Configuration for bounded recursion analysis.
#[derive(Debug, Clone)]
pub(crate) struct RecursionBound {
    /// Maximum recursion depth allowed.
    pub max_depth: u32,
    /// Whether to generate VCs for depth violation.
    pub verify_bounds: bool,
}

impl Default for RecursionBound {
    fn default() -> Self {
        Self {
            max_depth: 10,
            verify_bounds: true,
        }
    }
}

/// Tracks recursion depth during symbolic execution.
#[derive(Debug, Clone)]
pub(crate) struct RecursionTracker {
    /// Current depth per function.
    depths: FxHashMap<String, u32>,
    /// Maximum observed depth per function.
    max_observed: FxHashMap<String, u32>,
    /// Bound configuration.
    bound: RecursionBound,
    /// Whether any bound was exceeded.
    exceeded: Vec<BoundExceeded>,
}

/// Record of a recursion bound being exceeded.
#[derive(Debug, Clone)]
pub(crate) struct BoundExceeded {
    /// Function that exceeded its bound.
    pub function: String,
    /// Depth when exceeded.
    pub depth: u32,
    /// Configured maximum.
    pub max_depth: u32,
}

impl RecursionTracker {
    /// Create a new tracker with default bounds.
    pub(crate) fn new() -> Self {
        Self::with_bound(RecursionBound::default())
    }

    /// Create a tracker with a specific bound.
    pub(crate) fn with_bound(bound: RecursionBound) -> Self {
        Self {
            depths: FxHashMap::default(),
            max_observed: FxHashMap::default(),
            bound,
            exceeded: Vec::new(),
        }
    }

    /// Enter a function call. Returns false if bound exceeded.
    pub(crate) fn enter(&mut self, function: &str) -> bool {
        let depth = self.depths.entry(function.to_string()).or_insert(0);
        *depth += 1;

        let max = self.max_observed.entry(function.to_string()).or_insert(0);
        if *depth > *max {
            *max = *depth;
        }

        if *depth > self.bound.max_depth {
            self.exceeded.push(BoundExceeded {
                function: function.to_string(),
                depth: *depth,
                max_depth: self.bound.max_depth,
            });
            false
        } else {
            true
        }
    }

    /// Exit a function call.
    pub(crate) fn exit(&mut self, function: &str) {
        if let Some(depth) = self.depths.get_mut(function)
            && *depth > 0 {
                *depth -= 1;
            }
    }

    /// Get current depth for a function.
    #[must_use]
    pub(crate) fn depth(&self, function: &str) -> u32 {
        self.depths.get(function).copied().unwrap_or(0)
    }

    /// Get maximum observed depth for a function.
    #[must_use]
    pub(crate) fn max_depth(&self, function: &str) -> u32 {
        self.max_observed.get(function).copied().unwrap_or(0)
    }

    /// Get all bound-exceeded records.
    #[must_use]
    pub(crate) fn exceeded(&self) -> &[BoundExceeded] {
        &self.exceeded
    }
}

impl Default for RecursionTracker {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Recursion unroller
// ---------------------------------------------------------------------------

/// Unrolled representation of a recursive function at a specific depth.
#[derive(Debug, Clone)]
pub(crate) struct UnrolledCall {
    /// Function name.
    pub function: String,
    /// Recursion depth of this unrolled call.
    pub depth: u32,
    /// Argument values (symbolic names).
    pub args: Vec<String>,
    /// Child calls at depth+1.
    pub children: Vec<UnrolledCall>,
}

/// Unroll a recursive function to a fixed depth.
///
/// At the maximum depth, the function is modeled as returning a fresh
/// symbolic value (havoc). This is sound but incomplete.
pub(crate) fn unroll_recursion(
    function: &str,
    graph: &CallGraph,
    max_depth: u32,
    args: &[String],
) -> UnrolledCall {
    unroll_recursive(function, graph, max_depth, 0, args)
}

fn unroll_recursive(
    function: &str,
    graph: &CallGraph,
    max_depth: u32,
    current_depth: u32,
    args: &[String],
) -> UnrolledCall {
    let mut call = UnrolledCall {
        function: function.to_string(),
        depth: current_depth,
        args: args.to_vec(),
        children: Vec::new(),
    };

    if current_depth >= max_depth {
        return call; // Base case: stop unrolling.
    }

    // For each callee that is the same function (self-recursion), unroll.
    for callee in graph.callees(function) {
        if callee == function {
            let child_args: Vec<_> = args.iter()
                .enumerate()
                .map(|(i, a)| format!("{a}_d{}_{i}", current_depth + 1))
                .collect();
            let child = unroll_recursive(function, graph, max_depth, current_depth + 1, &child_args);
            call.children.push(child);
        }
    }

    call
}

/// Count total unrolled calls in an unrolled tree.
pub(crate) fn count_unrolled(call: &UnrolledCall) -> usize {
    1 + call.children.iter().map(count_unrolled).sum::<usize>()
}

// ---------------------------------------------------------------------------
// Termination witness
// ---------------------------------------------------------------------------

/// A ranking function for proving recursion terminates.
#[derive(Debug, Clone)]
pub(crate) struct RankingFunction {
    /// Function this ranking applies to.
    pub function: String,
    /// Expression that decreases with each recursive call.
    /// Represented as a string expression over function parameters.
    pub expression: String,
    /// Lower bound (ranking must stay above this).
    pub lower_bound: i64,
}

impl RankingFunction {
    /// Create a simple ranking function from a parameter name.
    pub(crate) fn from_param(function: impl Into<String>, param: impl Into<String>) -> Self {
        let param = param.into();
        Self {
            function: function.into(),
            expression: param,
            lower_bound: 0,
        }
    }

    /// Check if a ranking function is well-founded (decreases and has lower bound).
    #[must_use]
    pub(crate) fn is_well_founded(&self, caller_rank: i64, callee_rank: i64) -> bool {
        callee_rank < caller_rank && callee_rank >= self.lower_bound
    }
}

/// Summarize recursive function behavior at each depth.
#[derive(Debug, Clone)]
pub(crate) struct RecursionSummary {
    /// Function name.
    pub function: String,
    /// Maximum recursion depth explored.
    pub max_depth: u32,
    /// Whether the function is self-recursive.
    pub is_self_recursive: bool,
    /// Whether the function is part of a mutual recursion group.
    pub is_mutual: bool,
    /// Size of the mutual recursion group (1 for self-only).
    pub group_size: usize,
    /// Suggested ranking function (if heuristically determined).
    pub ranking: Option<RankingFunction>,
}

/// Generate a recursion summary for a function.
pub(crate) fn summarize_recursion(
    function: &str,
    _graph: &CallGraph,
    info: &RecursionInfo,
    max_depth: u32,
) -> RecursionSummary {
    let is_self = info.self_recursive.contains(&function.to_string());
    let mutual_group = info.mutual_groups.iter()
        .find(|g| g.contains(&function.to_string()));

    RecursionSummary {
        function: function.to_string(),
        max_depth,
        is_self_recursive: is_self,
        is_mutual: mutual_group.is_some(),
        group_size: mutual_group.map_or(if is_self { 1 } else { 0 }, |g| g.len()),
        ranking: None,
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_self_recursion_detection() {
        let mut graph = CallGraph::new();
        graph.add_edge("factorial", "factorial");
        let info = detect_recursion(&graph);
        assert!(info.self_recursive.contains(&"factorial".to_string()));
        assert!(info.recursive_functions.contains("factorial"));
    }

    #[test]
    fn test_mutual_recursion_detection() {
        let mut graph = CallGraph::new();
        graph.add_edge("is_even", "is_odd");
        graph.add_edge("is_odd", "is_even");
        let info = detect_recursion(&graph);
        assert!(!info.mutual_groups.is_empty());
        let group = &info.mutual_groups[0];
        assert!(group.contains(&"is_even".to_string()));
        assert!(group.contains(&"is_odd".to_string()));
    }

    #[test]
    fn test_no_recursion() {
        let mut graph = CallGraph::new();
        graph.add_edge("main", "helper");
        graph.add_edge("helper", "util");
        let info = detect_recursion(&graph);
        assert!(info.self_recursive.is_empty());
        assert!(info.mutual_groups.is_empty() || info.mutual_groups.iter().all(|g| g.len() <= 1));
    }

    #[test]
    fn test_recursion_tracker_basic() {
        let mut tracker = RecursionTracker::new();
        assert!(tracker.enter("f"));
        assert_eq!(tracker.depth("f"), 1);
        assert!(tracker.enter("f"));
        assert_eq!(tracker.depth("f"), 2);
        tracker.exit("f");
        assert_eq!(tracker.depth("f"), 1);
        tracker.exit("f");
        assert_eq!(tracker.depth("f"), 0);
    }

    #[test]
    fn test_recursion_tracker_bound_exceeded() {
        let bound = RecursionBound { max_depth: 2, verify_bounds: true };
        let mut tracker = RecursionTracker::with_bound(bound);
        assert!(tracker.enter("f")); // depth 1
        assert!(tracker.enter("f")); // depth 2
        assert!(!tracker.enter("f")); // depth 3 > max 2
        assert_eq!(tracker.exceeded().len(), 1);
        assert_eq!(tracker.exceeded()[0].depth, 3);
    }

    #[test]
    fn test_recursion_tracker_max_observed() {
        let mut tracker = RecursionTracker::new();
        tracker.enter("f");
        tracker.enter("f");
        tracker.enter("f");
        tracker.exit("f");
        tracker.exit("f");
        tracker.exit("f");
        assert_eq!(tracker.max_depth("f"), 3);
        assert_eq!(tracker.depth("f"), 0);
    }

    #[test]
    fn test_unroll_recursion_depth_0() {
        let mut graph = CallGraph::new();
        graph.add_edge("f", "f");
        let result = unroll_recursion("f", &graph, 0, &["n".into()]);
        assert_eq!(result.depth, 0);
        assert!(result.children.is_empty());
    }

    #[test]
    fn test_unroll_recursion_depth_3() {
        let mut graph = CallGraph::new();
        graph.add_edge("f", "f");
        let result = unroll_recursion("f", &graph, 3, &["n".into()]);
        assert_eq!(result.depth, 0);
        assert_eq!(result.children.len(), 1);
        assert_eq!(result.children[0].depth, 1);
        assert_eq!(count_unrolled(&result), 4); // depths 0,1,2,3
    }

    #[test]
    fn test_count_unrolled() {
        let call = UnrolledCall {
            function: "f".into(),
            depth: 0,
            args: vec![],
            children: vec![
                UnrolledCall {
                    function: "f".into(),
                    depth: 1,
                    args: vec![],
                    children: vec![],
                },
            ],
        };
        assert_eq!(count_unrolled(&call), 2);
    }

    #[test]
    fn test_ranking_function_well_founded() {
        let rf = RankingFunction::from_param("f", "n");
        assert!(rf.is_well_founded(5, 4)); // decreasing, above lower bound
        assert!(!rf.is_well_founded(5, 5)); // not decreasing
        assert!(!rf.is_well_founded(0, -1)); // below lower bound
    }

    #[test]
    fn test_recursion_summary() {
        let mut graph = CallGraph::new();
        graph.add_edge("fib", "fib");
        let info = detect_recursion(&graph);
        let summary = summarize_recursion("fib", &graph, &info, 10);
        assert!(summary.is_self_recursive);
        assert!(!summary.is_mutual);
        assert_eq!(summary.group_size, 1);
    }

    #[test]
    fn test_call_graph_functions() {
        let mut graph = CallGraph::new();
        graph.add_edge("a", "b");
        graph.add_edge("b", "c");
        let fns = graph.functions();
        assert!(fns.contains(&"a"));
        assert!(fns.contains(&"b"));
        assert!(fns.contains(&"c"));
    }

    #[test]
    fn test_call_graph_callees() {
        let mut graph = CallGraph::new();
        graph.add_edge("main", "foo");
        graph.add_edge("main", "bar");
        assert_eq!(graph.callees("main"), &["foo", "bar"]);
        assert!(graph.callees("unknown").is_empty());
    }

    #[test]
    fn test_tarjan_scc_no_cycles() {
        let mut graph = CallGraph::new();
        graph.add_edge("a", "b");
        graph.add_edge("b", "c");
        let sccs = tarjan_scc(&graph);
        // Each function is its own SCC.
        assert!(sccs.iter().all(|scc| scc.len() == 1));
    }

    #[test]
    fn test_tarjan_scc_with_cycle() {
        let mut graph = CallGraph::new();
        graph.add_edge("a", "b");
        graph.add_edge("b", "a");
        let sccs = tarjan_scc(&graph);
        let big_sccs: Vec<_> = sccs.iter().filter(|s| s.len() > 1).collect();
        assert_eq!(big_sccs.len(), 1);
        assert!(big_sccs[0].contains(&"a".to_string()));
        assert!(big_sccs[0].contains(&"b".to_string()));
    }
}
