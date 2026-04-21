// trust-proof-cert dependency graph
//
// Directed graph of proof dependencies between functions.
// Supports topological sorting for verification order and
// Tarjan's algorithm for strongly connected component (SCC) detection
// to identify mutual recursion.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::{FxHashMap, FxHashSet};

use serde::{Deserialize, Serialize};

use crate::CertError;

/// A node in the proof dependency graph, representing a function.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DepNode {
    /// Fully qualified function name.
    pub function: String,
    /// Functions this function calls (outgoing edges).
    pub callees: Vec<String>,
    /// Whether a proof certificate exists for this function.
    pub has_proof: bool,
}

/// A strongly connected component: a set of mutually recursive functions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StronglyConnectedComponent {
    /// Function names in this SCC.
    pub functions: Vec<String>,
}

impl StronglyConnectedComponent {
    /// Returns true if this SCC represents mutual recursion (more than one function).
    pub fn is_recursive(&self) -> bool {
        self.functions.len() > 1
    }
}

/// Result of analyzing the dependency graph.
#[derive(Debug, Clone, PartialEq)]
pub struct DepGraphAnalysis {
    /// Functions in topological order (callees before callers).
    /// Empty if the graph has cycles.
    pub topological_order: Vec<String>,
    /// Strongly connected components (groups of mutually recursive functions).
    pub sccs: Vec<StronglyConnectedComponent>,
    /// Functions with no proof certificate.
    pub unproven: Vec<String>,
    /// Functions whose callees are all proven (fully discharged).
    pub fully_discharged: Vec<String>,
    /// Coverage: fraction of functions with proofs (0.0 - 1.0).
    pub coverage: f64,
}

/// Directed graph of proof dependencies between functions.
///
/// Each node represents a function. Edges go from caller to callee
/// (function A depends on function B means A calls B). Verification
/// should proceed in reverse topological order: prove callees first,
/// then callers can assume callee contracts.
#[derive(Debug, Clone)]
pub struct DepGraph {
    /// Nodes indexed by function name.
    nodes: FxHashMap<String, DepNode>,
}

impl DepGraph {
    /// Create a new empty dependency graph.
    pub fn new() -> Self {
        DepGraph {
            nodes: FxHashMap::default(),
        }
    }

    /// Add a function node with its callees.
    pub fn add_function(&mut self, function: &str, callees: Vec<String>, has_proof: bool) {
        self.nodes.insert(
            function.to_string(),
            DepNode {
                function: function.to_string(),
                callees,
                has_proof,
            },
        );
    }

    /// Get a node by function name.
    pub fn get_node(&self, function: &str) -> Option<&DepNode> {
        self.nodes.get(function)
    }

    /// Return all function names in the graph.
    pub fn functions(&self) -> Vec<String> {
        let mut names: Vec<String> = self.nodes.keys().cloned().collect();
        names.sort();
        names
    }

    /// Return the number of nodes.
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Return true if the graph has no nodes.
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    /// Compute topological order using Kahn's algorithm.
    ///
    /// Returns functions in dependency order: callees before callers.
    /// Returns `Err` if the graph contains cycles.
    pub fn topological_sort(&self) -> Result<Vec<String>, CertError> {
        // Compute in-degree for each node (only counting edges within the graph)
        let mut in_degree: FxHashMap<&str, usize> = FxHashMap::default();
        for name in self.nodes.keys() {
            in_degree.entry(name.as_str()).or_insert(0);
        }
        for node in self.nodes.values() {
            for callee in &node.callees {
                if self.nodes.contains_key(callee.as_str()) {
                    *in_degree.entry(callee.as_str()).or_insert(0) += 1;
                }
            }
        }

        // Note: in this graph, edges go caller -> callee. A caller "depends on"
        // its callee. In-degree here counts how many callers point to a function.
        // For topological sort where callees come first, we want to process
        // nodes with zero in-degree first (leaf functions nobody calls within the graph).
        // Actually, we need reverse: callees should come before callers.
        // Since edges are caller->callee, we need the *reverse* topological order
        // of the edge direction. Let's compute based on out-edges reversed.

        // Recompute: for "callees before callers", we reverse edges.
        // In reversed graph: edge goes callee -> caller.
        // Topological sort of reversed graph gives callees first.
        let mut rev_in_degree: FxHashMap<&str, usize> = FxHashMap::default();
        for name in self.nodes.keys() {
            rev_in_degree.entry(name.as_str()).or_insert(0);
        }
        for node in self.nodes.values() {
            for callee in &node.callees {
                if self.nodes.contains_key(callee.as_str()) {
                    // In reversed graph, callee -> caller, so caller gains in-degree
                    *rev_in_degree.entry(node.function.as_str()).or_insert(0) += 1;
                }
            }
        }

        let mut queue: Vec<String> = rev_in_degree
            .iter()
            .filter(|(_, deg)| **deg == 0)
            .map(|(&name, _)| name.to_string())
            .collect();
        queue.sort(); // deterministic

        let mut result = Vec::new();
        while let Some(func) = queue.pop() {
            result.push(func.clone());
            // In reversed graph, edges go callee -> caller.
            // When we "remove" a callee node, we decrement in-degree of its callers.
            // Original edge: caller -> callee. So find all callers of `func`.
            for node in self.nodes.values() {
                if node.callees.contains(&func)
                    && let Some(deg) = rev_in_degree.get_mut(node.function.as_str()) {
                        *deg = deg.saturating_sub(1);
                        if *deg == 0 {
                            queue.push(node.function.clone());
                            queue.sort();
                        }
                    }
            }
        }

        if result.len() != self.nodes.len() {
            return Err(CertError::VerificationFailed {
                reason: "dependency graph contains cycles; topological sort incomplete".to_string(),
            });
        }

        Ok(result)
    }

    /// Detect strongly connected components using Tarjan's algorithm.
    ///
    /// Returns SCCs in reverse topological order. SCCs with more than
    /// one function represent mutual recursion.
    pub fn find_sccs(&self) -> Vec<StronglyConnectedComponent> {
        let mut state = TarjanState::new();

        for name in self.nodes.keys() {
            if !state.visited.contains(name.as_str()) {
                self.tarjan_visit(name, &mut state);
            }
        }

        state.sccs
    }

    /// Tarjan's DFS visit.
    fn tarjan_visit<'a>(&'a self, node_name: &'a str, state: &mut TarjanState<'a>) {
        let index = state.next_index;
        state.next_index += 1;
        state.index.insert(node_name, index);
        state.lowlink.insert(node_name, index);
        state.visited.insert(node_name);
        state.stack.push(node_name);
        state.on_stack.insert(node_name);

        if let Some(node) = self.nodes.get(node_name) {
            for callee in &node.callees {
                let callee_str = callee.as_str();
                if !self.nodes.contains_key(callee_str) {
                    continue; // external dependency, skip
                }
                if !state.visited.contains(callee_str) {
                    self.tarjan_visit(callee_str, state);
                    let callee_low = state.lowlink[callee_str];
                    let node_low = state.lowlink[node_name];
                    if callee_low < node_low {
                        state.lowlink.insert(node_name, callee_low);
                    }
                } else if state.on_stack.contains(callee_str) {
                    let callee_idx = state.index[callee_str];
                    let node_low = state.lowlink[node_name];
                    if callee_idx < node_low {
                        state.lowlink.insert(node_name, callee_idx);
                    }
                }
            }
        }

        // If this node is a root of an SCC
        if state.lowlink[node_name] == state.index[node_name] {
            let mut scc_functions = Vec::new();
            loop {
                // SAFETY: Tarjan's algorithm guarantees the stack contains this node.
                // Invariant: Tarjan's algorithm guarantees the stack contains this node.
                let w = state.stack.pop()
                    .expect("invariant: Tarjan stack must contain current SCC root");
                state.on_stack.remove(w);
                scc_functions.push(w.to_string());
                if w == node_name {
                    break;
                }
            }
            scc_functions.sort(); // deterministic ordering
            state.sccs.push(StronglyConnectedComponent {
                functions: scc_functions,
            });
        }
    }

    /// Analyze the dependency graph: topological order, SCCs, coverage.
    pub fn analyze(&self) -> DepGraphAnalysis {
        let sccs = self.find_sccs();

        let topological_order = self.topological_sort().unwrap_or_default();

        let mut unproven = Vec::new();
        let mut fully_discharged = Vec::new();
        let proven_set: FxHashSet<&str> = self
            .nodes
            .values()
            .filter(|n| n.has_proof)
            .map(|n| n.function.as_str())
            .collect();

        for node in self.nodes.values() {
            if !node.has_proof {
                unproven.push(node.function.clone());
            }
            // A function is fully discharged if it has a proof AND all its
            // callees (within the graph) also have proofs
            if node.has_proof {
                let all_callees_proven = node
                    .callees
                    .iter()
                    .filter(|c| self.nodes.contains_key(c.as_str()))
                    .all(|c| proven_set.contains(c.as_str()));
                if all_callees_proven {
                    fully_discharged.push(node.function.clone());
                }
            }
        }

        unproven.sort();
        fully_discharged.sort();

        let total = self.nodes.len();
        let proven_count = total - unproven.len();
        let coverage = if total == 0 {
            0.0
        } else {
            proven_count as f64 / total as f64
        };

        DepGraphAnalysis {
            topological_order,
            sccs,
            unproven,
            fully_discharged,
            coverage,
        }
    }
}

impl Default for DepGraph {
    fn default() -> Self {
        Self::new()
    }
}

/// Internal state for Tarjan's SCC algorithm.
struct TarjanState<'a> {
    next_index: usize,
    index: FxHashMap<&'a str, usize>,
    lowlink: FxHashMap<&'a str, usize>,
    visited: FxHashSet<&'a str>,
    stack: Vec<&'a str>,
    on_stack: FxHashSet<&'a str>,
    sccs: Vec<StronglyConnectedComponent>,
}

impl<'a> TarjanState<'a> {
    fn new() -> Self {
        TarjanState {
            next_index: 0,
            index: FxHashMap::default(),
            lowlink: FxHashMap::default(),
            visited: FxHashSet::default(),
            stack: Vec::new(),
            on_stack: FxHashSet::default(),
            sccs: Vec::new(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_dep_graph_empty() {
        let graph = DepGraph::new();
        assert!(graph.is_empty());
        assert_eq!(graph.len(), 0);
        assert!(graph.functions().is_empty());
    }

    #[test]
    fn test_dep_graph_add_function() {
        let mut graph = DepGraph::new();
        graph.add_function("foo", vec!["bar".to_string()], true);
        graph.add_function("bar", vec![], true);

        assert_eq!(graph.len(), 2);
        assert!(!graph.is_empty());

        let foo = graph.get_node("foo").expect("foo should exist");
        assert_eq!(foo.callees, vec!["bar"]);
        assert!(foo.has_proof);

        let bar = graph.get_node("bar").expect("bar should exist");
        assert!(bar.callees.is_empty());
    }

    #[test]
    fn test_topological_sort_linear() {
        let mut graph = DepGraph::new();
        graph.add_function("a", vec!["b".to_string()], true);
        graph.add_function("b", vec!["c".to_string()], true);
        graph.add_function("c", vec![], true);

        let order = graph.topological_sort().expect("should succeed for acyclic graph");
        let pos_a = order.iter().position(|x| x == "a").expect("a in order");
        let pos_b = order.iter().position(|x| x == "b").expect("b in order");
        let pos_c = order.iter().position(|x| x == "c").expect("c in order");

        assert!(pos_c < pos_b, "c should come before b (callee first)");
        assert!(pos_b < pos_a, "b should come before a (callee first)");
    }

    #[test]
    fn test_topological_sort_diamond() {
        let mut graph = DepGraph::new();
        graph.add_function("main", vec!["left".to_string(), "right".to_string()], true);
        graph.add_function("left", vec!["shared".to_string()], true);
        graph.add_function("right", vec!["shared".to_string()], true);
        graph.add_function("shared", vec![], true);

        let order = graph.topological_sort().expect("should succeed");
        let pos_main = order.iter().position(|x| x == "main").expect("main");
        let pos_left = order.iter().position(|x| x == "left").expect("left");
        let pos_right = order.iter().position(|x| x == "right").expect("right");
        let pos_shared = order.iter().position(|x| x == "shared").expect("shared");

        assert!(pos_shared < pos_left, "shared before left");
        assert!(pos_shared < pos_right, "shared before right");
        assert!(pos_left < pos_main, "left before main");
        assert!(pos_right < pos_main, "right before main");
    }

    #[test]
    fn test_topological_sort_cycle_fails() {
        let mut graph = DepGraph::new();
        graph.add_function("a", vec!["b".to_string()], true);
        graph.add_function("b", vec!["a".to_string()], true);

        let result = graph.topological_sort();
        assert!(result.is_err(), "cycle should cause topological sort to fail");
    }

    #[test]
    fn test_find_sccs_no_cycles() {
        let mut graph = DepGraph::new();
        graph.add_function("a", vec!["b".to_string()], true);
        graph.add_function("b", vec!["c".to_string()], true);
        graph.add_function("c", vec![], true);

        let sccs = graph.find_sccs();
        // Each function is its own SCC (no mutual recursion)
        assert_eq!(sccs.len(), 3);
        for scc in &sccs {
            assert_eq!(scc.functions.len(), 1);
            assert!(!scc.is_recursive());
        }
    }

    #[test]
    fn test_find_sccs_mutual_recursion() {
        let mut graph = DepGraph::new();
        graph.add_function("a", vec!["b".to_string()], true);
        graph.add_function("b", vec!["a".to_string()], true);
        graph.add_function("c", vec![], true);

        let sccs = graph.find_sccs();

        // Should have 2 SCCs: {a, b} and {c}
        let recursive_sccs: Vec<_> = sccs.iter().filter(|s| s.is_recursive()).collect();
        assert_eq!(recursive_sccs.len(), 1, "should find one recursive SCC");
        let scc = &recursive_sccs[0];
        assert!(scc.functions.contains(&"a".to_string()));
        assert!(scc.functions.contains(&"b".to_string()));
    }

    #[test]
    fn test_find_sccs_three_way_cycle() {
        let mut graph = DepGraph::new();
        graph.add_function("a", vec!["b".to_string()], true);
        graph.add_function("b", vec!["c".to_string()], true);
        graph.add_function("c", vec!["a".to_string()], true);

        let sccs = graph.find_sccs();

        let recursive_sccs: Vec<_> = sccs.iter().filter(|s| s.is_recursive()).collect();
        assert_eq!(recursive_sccs.len(), 1);
        assert_eq!(recursive_sccs[0].functions.len(), 3);
    }

    #[test]
    fn test_analyze_full_coverage() {
        let mut graph = DepGraph::new();
        graph.add_function("foo", vec!["bar".to_string()], true);
        graph.add_function("bar", vec![], true);

        let analysis = graph.analyze();
        assert_eq!(analysis.topological_order.len(), 2);
        assert!(analysis.unproven.is_empty());
        assert_eq!(analysis.fully_discharged.len(), 2);
        assert!((analysis.coverage - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_analyze_partial_coverage() {
        let mut graph = DepGraph::new();
        graph.add_function("foo", vec!["bar".to_string()], true);
        graph.add_function("bar", vec![], false);

        let analysis = graph.analyze();
        assert_eq!(analysis.unproven, vec!["bar"]);
        // foo has a proof but its callee bar does not, so foo is NOT fully discharged
        assert!(
            !analysis.fully_discharged.contains(&"foo".to_string()),
            "foo should not be fully discharged when bar is unproven"
        );
        assert!((analysis.coverage - 0.5).abs() < f64::EPSILON);
    }

    #[test]
    fn test_analyze_empty_graph() {
        let graph = DepGraph::new();
        let analysis = graph.analyze();
        assert!(analysis.topological_order.is_empty());
        assert!(analysis.sccs.is_empty());
        assert!(analysis.unproven.is_empty());
        assert!(analysis.fully_discharged.is_empty());
        assert!((analysis.coverage - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_analyze_with_cycles() {
        let mut graph = DepGraph::new();
        graph.add_function("a", vec!["b".to_string()], true);
        graph.add_function("b", vec!["a".to_string()], true);

        let analysis = graph.analyze();
        // Topological order should be empty due to cycle
        assert!(analysis.topological_order.is_empty());
        // Should detect the SCC
        let recursive_sccs: Vec<_> = analysis.sccs.iter().filter(|s| s.is_recursive()).collect();
        assert_eq!(recursive_sccs.len(), 1);
    }

    #[test]
    fn test_dep_graph_external_callee() {
        // If a callee is not in the graph, it's an external dependency
        let mut graph = DepGraph::new();
        graph.add_function("foo", vec!["external::bar".to_string()], true);

        let order = graph.topological_sort().expect("should succeed");
        assert_eq!(order, vec!["foo"]);

        let analysis = graph.analyze();
        // foo is fully discharged because its only callee is external
        assert!(analysis.fully_discharged.contains(&"foo".to_string()));
    }

    #[test]
    fn test_dep_graph_default() {
        let graph = DepGraph::default();
        assert!(graph.is_empty());
    }
}
