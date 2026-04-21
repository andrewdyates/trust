// trust-vcgen/reachability.rs: Call graph reachability analysis
//
// BFS reachability from entry points to detect unreachable public functions.
// Moved from trust-types/call_graph.rs per #162.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::VecDeque;
use trust_types::fx::{FxHashMap, FxHashSet};

use trust_types::call_graph::{
    CallGraph, ReachabilityResult, ReachableFunction, UnreachableFunction,
};

/// Perform BFS reachability from entry points.
///
/// Returns the set of def_paths reachable from any entry point.
/// Uses the callee field for edge resolution: an edge matches a node
/// if the node's def_path ends with the callee string or equals it exactly.
#[must_use]
pub fn reachable_from_entries(graph: &CallGraph) -> FxHashSet<String> {
    let entries: Vec<&str> = graph.entry_points();
    reachable_from(graph, &entries)
}

/// Perform BFS reachability from a given set of root def_paths.
#[must_use]
pub fn reachable_from(graph: &CallGraph, roots: &[&str]) -> FxHashSet<String> {
    // Build adjacency: caller def_path -> set of callee strings
    let mut adjacency: FxHashMap<&str, Vec<&str>> = FxHashMap::default();
    for edge in &graph.edges {
        adjacency
            .entry(edge.caller.as_str())
            .or_default()
            .push(edge.callee.as_str());
    }

    // Build a lookup for resolving callee names to node def_paths.
    // A callee string may be a full def_path or just a function name.
    let node_paths: FxHashSet<&str> = graph.nodes.iter().map(|n| n.def_path.as_str()).collect();

    let mut visited: FxHashSet<String> = FxHashSet::default();
    let mut queue: VecDeque<String> = VecDeque::new();

    for &root in roots {
        if node_paths.contains(root) {
            visited.insert(root.to_string());
            queue.push_back(root.to_string());
        }
    }

    while let Some(current) = queue.pop_front() {
        if let Some(callees) = adjacency.get(current.as_str()) {
            for &callee in callees {
                // Try exact match first
                if node_paths.contains(callee) && visited.insert(callee.to_string()) {
                    queue.push_back(callee.to_string());
                    continue;
                }

                // Try suffix match: node def_path ends with "::callee"
                for &node_path in &node_paths {
                    let suffix = format!("::{callee}");
                    if node_path.ends_with(&suffix) && visited.insert(node_path.to_string()) {
                        queue.push_back(node_path.to_string());
                    }
                }
            }
        }
    }

    visited
}

/// Analyze reachability and return results for all public functions.
///
/// A public function is considered unreachable if it cannot be reached
/// from any entry point via the call graph.
#[must_use]
pub fn analyze_reachability(graph: &CallGraph) -> ReachabilityResult {
    let reachable = reachable_from_entries(graph);

    let mut reachable_fns = Vec::new();
    let mut unreachable_fns = Vec::new();

    for node in &graph.nodes {
        if !node.is_public {
            continue;
        }

        if reachable.contains(&node.def_path) {
            reachable_fns.push(ReachableFunction {
                def_path: node.def_path.clone(),
                name: node.name.clone(),
                span: node.span.clone(),
            });
        } else {
            unreachable_fns.push(UnreachableFunction {
                def_path: node.def_path.clone(),
                name: node.name.clone(),
                span: node.span.clone(),
                reason: if graph.entry_points().is_empty() {
                    "no entry points defined".to_string()
                } else {
                    "not reachable from any entry point".to_string()
                },
            });
        }
    }

    ReachabilityResult {
        entry_points: graph
            .nodes
            .iter()
            .filter(|n| n.is_entry_point)
            .map(|n| n.def_path.clone())
            .collect(),
        reachable: reachable_fns,
        unreachable: unreachable_fns,
        total_functions: graph.nodes.len(),
        total_edges: graph.edges.len(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_types::call_graph::{CallGraphEdge, CallGraphNode};
    use trust_types::SourceSpan;

    fn span(file: &str, line: u32) -> SourceSpan {
        SourceSpan {
            file: file.to_string(),
            line_start: line,
            col_start: 1,
            line_end: line,
            col_end: 40,
        }
    }

    /// Build a simple connected call graph:
    ///   main() -> handler_a() -> helper()
    ///   main() -> handler_b()
    fn build_connected_graph() -> CallGraph {
        let mut graph = CallGraph::new();

        graph.add_node(CallGraphNode {
            def_path: "crate::main".to_string(),
            name: "main".to_string(),
            is_public: true,
            is_entry_point: true,
            span: span("src/main.rs", 1),
        });
        graph.add_node(CallGraphNode {
            def_path: "crate::api::handler_a".to_string(),
            name: "handler_a".to_string(),
            is_public: true,
            is_entry_point: false,
            span: span("src/api.rs", 10),
        });
        graph.add_node(CallGraphNode {
            def_path: "crate::api::handler_b".to_string(),
            name: "handler_b".to_string(),
            is_public: true,
            is_entry_point: false,
            span: span("src/api.rs", 20),
        });
        graph.add_node(CallGraphNode {
            def_path: "crate::util::helper".to_string(),
            name: "helper".to_string(),
            is_public: false,
            is_entry_point: false,
            span: span("src/util.rs", 5),
        });

        graph.add_edge(CallGraphEdge {
            caller: "crate::main".to_string(),
            callee: "crate::api::handler_a".to_string(),
            call_site: span("src/main.rs", 3),
        });
        graph.add_edge(CallGraphEdge {
            caller: "crate::main".to_string(),
            callee: "crate::api::handler_b".to_string(),
            call_site: span("src/main.rs", 4),
        });
        graph.add_edge(CallGraphEdge {
            caller: "crate::api::handler_a".to_string(),
            callee: "crate::util::helper".to_string(),
            call_site: span("src/api.rs", 12),
        });

        graph
    }

    /// Build a disconnected graph with an unreachable public function.
    fn build_disconnected_graph() -> CallGraph {
        let mut graph = CallGraph::new();

        graph.add_node(CallGraphNode {
            def_path: "crate::main".to_string(),
            name: "main".to_string(),
            is_public: true,
            is_entry_point: true,
            span: span("src/main.rs", 1),
        });
        graph.add_node(CallGraphNode {
            def_path: "crate::api::handler_a".to_string(),
            name: "handler_a".to_string(),
            is_public: true,
            is_entry_point: false,
            span: span("src/api.rs", 10),
        });
        graph.add_node(CallGraphNode {
            def_path: "crate::api::orphan_handler".to_string(),
            name: "orphan_handler".to_string(),
            is_public: true,
            is_entry_point: false,
            span: span("src/api.rs", 30),
        });

        graph.add_edge(CallGraphEdge {
            caller: "crate::main".to_string(),
            callee: "crate::api::handler_a".to_string(),
            call_site: span("src/main.rs", 3),
        });

        graph
    }

    #[test]
    fn test_connected_graph_all_public_reachable() {
        let graph = build_connected_graph();
        let result = analyze_reachability(&graph);

        assert!(result.is_fully_connected(), "all public fns should be reachable");
        assert_eq!(result.unreachable_count(), 0);
        assert_eq!(result.reachable.len(), 3);
        assert_eq!(result.entry_points.len(), 1);
        assert_eq!(result.total_functions, 4);
        assert_eq!(result.total_edges, 3);
    }

    #[test]
    fn test_disconnected_graph_detects_orphan() {
        let graph = build_disconnected_graph();
        let result = analyze_reachability(&graph);

        assert!(!result.is_fully_connected());
        assert_eq!(result.unreachable_count(), 1);
        assert_eq!(result.unreachable[0].def_path, "crate::api::orphan_handler");
        assert_eq!(result.unreachable[0].name, "orphan_handler");
        assert_eq!(result.unreachable[0].reason, "not reachable from any entry point");
        assert_eq!(result.reachable.len(), 2);
    }

    #[test]
    fn test_empty_graph_no_panic() {
        let graph = CallGraph::new();
        let result = analyze_reachability(&graph);

        assert!(result.is_fully_connected());
        assert_eq!(result.unreachable_count(), 0);
        assert_eq!(result.total_functions, 0);
        assert_eq!(result.total_edges, 0);
    }

    #[test]
    fn test_no_entry_points_all_public_unreachable() {
        let mut graph = CallGraph::new();
        graph.add_node(CallGraphNode {
            def_path: "crate::api::handler".to_string(),
            name: "handler".to_string(),
            is_public: true,
            is_entry_point: false,
            span: span("src/api.rs", 1),
        });

        let result = analyze_reachability(&graph);

        assert!(!result.is_fully_connected());
        assert_eq!(result.unreachable_count(), 1);
        assert_eq!(result.unreachable[0].reason, "no entry points defined");
    }

    #[test]
    fn test_suffix_matching_for_callee_resolution() {
        let mut graph = CallGraph::new();

        graph.add_node(CallGraphNode {
            def_path: "crate::main".to_string(),
            name: "main".to_string(),
            is_public: true,
            is_entry_point: true,
            span: span("src/main.rs", 1),
        });
        graph.add_node(CallGraphNode {
            def_path: "crate::api::serve".to_string(),
            name: "serve".to_string(),
            is_public: true,
            is_entry_point: false,
            span: span("src/api.rs", 5),
        });

        // Edge uses short name (as MIR sometimes does)
        graph.add_edge(CallGraphEdge {
            caller: "crate::main".to_string(),
            callee: "serve".to_string(),
            call_site: span("src/main.rs", 3),
        });

        let reachable = reachable_from_entries(&graph);
        assert!(reachable.contains("crate::api::serve"), "suffix matching should resolve 'serve'");
    }

    #[test]
    fn test_transitive_reachability() {
        let mut graph = CallGraph::new();

        for (path, name, is_entry) in [
            ("crate::main", "main", true),
            ("crate::a", "a", false),
            ("crate::b", "b", false),
            ("crate::c", "c", false),
        ] {
            graph.add_node(CallGraphNode {
                def_path: path.to_string(),
                name: name.to_string(),
                is_public: true,
                is_entry_point: is_entry,
                span: SourceSpan::default(),
            });
        }

        graph.add_edge(CallGraphEdge {
            caller: "crate::main".to_string(),
            callee: "crate::a".to_string(),
            call_site: SourceSpan::default(),
        });
        graph.add_edge(CallGraphEdge {
            caller: "crate::a".to_string(),
            callee: "crate::b".to_string(),
            call_site: SourceSpan::default(),
        });
        graph.add_edge(CallGraphEdge {
            caller: "crate::b".to_string(),
            callee: "crate::c".to_string(),
            call_site: SourceSpan::default(),
        });

        let result = analyze_reachability(&graph);
        assert!(result.is_fully_connected(), "transitive chain should be fully reachable");
        assert_eq!(result.reachable.len(), 4);
    }

    #[test]
    fn test_cycle_handling() {
        let mut graph = CallGraph::new();

        for (path, name, is_entry) in [
            ("crate::main", "main", true),
            ("crate::a", "a", false),
            ("crate::b", "b", false),
        ] {
            graph.add_node(CallGraphNode {
                def_path: path.to_string(),
                name: name.to_string(),
                is_public: true,
                is_entry_point: is_entry,
                span: SourceSpan::default(),
            });
        }

        graph.add_edge(CallGraphEdge {
            caller: "crate::main".to_string(),
            callee: "crate::a".to_string(),
            call_site: SourceSpan::default(),
        });
        graph.add_edge(CallGraphEdge {
            caller: "crate::a".to_string(),
            callee: "crate::b".to_string(),
            call_site: SourceSpan::default(),
        });
        graph.add_edge(CallGraphEdge {
            caller: "crate::b".to_string(),
            callee: "crate::a".to_string(),
            call_site: SourceSpan::default(),
        });

        let result = analyze_reachability(&graph);
        assert!(result.is_fully_connected(), "cycle should not cause infinite loop");
    }
}
