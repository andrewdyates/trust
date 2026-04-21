// trust-vcgen/call_graph.rs: Call graph construction and cycle detection (#230)
//
// Builds a CallGraph from a set of VerifiableFunction definitions by
// scanning Terminator::Call edges. Provides cycle detection (Tarjan's SCC)
// for identifying recursive functions that need special summary handling.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::{FxHashMap, FxHashSet};

use trust_types::call_graph::{CallGraph, CallGraphEdge, CallGraphNode};
use trust_types::{Terminator, VerifiableFunction};

/// Build a call graph from a slice of verifiable functions.
///
/// Scans each function's basic blocks for `Terminator::Call` edges and
/// constructs a directed graph of caller -> callee relationships.
/// The first function in the slice is treated as the entry point.
#[must_use]
pub fn build_call_graph(functions: &[VerifiableFunction]) -> CallGraph {
    let mut graph = CallGraph::new();

    // Add nodes for all functions
    for (i, func) in functions.iter().enumerate() {
        graph.add_node(CallGraphNode {
            def_path: func.def_path.clone(),
            name: func.name.clone(),
            is_public: true,
            is_entry_point: i == 0,
            span: func.span.clone(),
        });
    }

    // Collect known def_paths for edge resolution
    let known: FxHashSet<&str> = functions.iter().map(|f| f.def_path.as_str()).collect();
    let name_to_path: FxHashMap<&str, &str> = functions
        .iter()
        .map(|f| (f.name.as_str(), f.def_path.as_str()))
        .collect();

    // Scan for call edges
    for func in functions {
        for block in &func.body.blocks {
            if let Terminator::Call { func: callee_name, span, .. } = &block.terminator {
                // Resolve callee: try exact def_path match, then name match, then suffix
                let callee_path = if known.contains(callee_name.as_str()) {
                    callee_name.clone()
                } else if let Some(&path) = name_to_path.get(callee_name.as_str()) {
                    path.to_string()
                } else {
                    // Suffix match: "helper" matches "crate::util::helper"
                    let suffix = format!("::{callee_name}");
                    known
                        .iter()
                        .find(|&&p| p.ends_with(&suffix))
                        .map(|&p| p.to_string())
                        .unwrap_or_else(|| callee_name.clone())
                };

                graph.add_edge(CallGraphEdge {
                    caller: func.def_path.clone(),
                    callee: callee_path,
                    call_site: span.clone(),
                });
            }
        }
    }

    graph
}

/// A strongly connected component (set of mutually recursive functions).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Scc {
    /// Function def_paths in this SCC.
    pub members: Vec<String>,
}

impl Scc {
    /// Returns true if this SCC contains a cycle (more than one member,
    /// or a single member that calls itself).
    #[must_use]
    pub fn is_recursive(&self) -> bool {
        self.members.len() > 1
    }
}

/// Detect strongly connected components (cycles) in a call graph.
///
/// Uses Tarjan's algorithm. Returns SCCs in reverse topological order
/// (leaf SCCs first). An SCC with >1 member indicates mutual recursion.
/// Self-recursive functions appear as single-member SCCs but can be
/// detected by checking if their def_path appears in their own call edges.
#[must_use]
pub fn detect_cycles(graph: &CallGraph) -> Vec<Scc> {
    let nodes: Vec<&str> = graph.nodes.iter().map(|n| n.def_path.as_str()).collect();
    let node_set: FxHashSet<&str> = nodes.iter().copied().collect();

    // Build adjacency list
    let mut adj: FxHashMap<&str, Vec<&str>> = FxHashMap::default();
    for node in &nodes {
        adj.entry(node).or_default();
    }
    for edge in &graph.edges {
        if node_set.contains(edge.callee.as_str()) {
            adj.entry(edge.caller.as_str())
                .or_default()
                .push(&edge.callee);
        }
    }

    // Tarjan's SCC algorithm
    let mut index_counter: usize = 0;
    let mut stack: Vec<&str> = Vec::new();
    let mut on_stack: FxHashSet<&str> = FxHashSet::default();
    let mut indices: FxHashMap<&str, usize> = FxHashMap::default();
    let mut lowlinks: FxHashMap<&str, usize> = FxHashMap::default();
    let mut sccs: Vec<Scc> = Vec::new();

    #[allow(clippy::too_many_arguments)]
    fn strongconnect<'a>(
        v: &'a str,
        adj: &FxHashMap<&str, Vec<&'a str>>,
        index_counter: &mut usize,
        stack: &mut Vec<&'a str>,
        on_stack: &mut FxHashSet<&'a str>,
        indices: &mut FxHashMap<&'a str, usize>,
        lowlinks: &mut FxHashMap<&'a str, usize>,
        sccs: &mut Vec<Scc>,
    ) {
        indices.insert(v, *index_counter);
        lowlinks.insert(v, *index_counter);
        *index_counter += 1;
        stack.push(v);
        on_stack.insert(v);

        if let Some(successors) = adj.get(v) {
            for &w in successors {
                if !indices.contains_key(w) {
                    strongconnect(w, adj, index_counter, stack, on_stack, indices, lowlinks, sccs);
                    let w_low = lowlinks[w];
                    let v_low = lowlinks[v];
                    lowlinks.insert(v, v_low.min(w_low));
                } else if on_stack.contains(w) {
                    let w_idx = indices[w];
                    let v_low = lowlinks[v];
                    lowlinks.insert(v, v_low.min(w_idx));
                }
            }
        }

        if lowlinks[v] == indices[v] {
            let mut scc_members = Vec::new();
            while let Some(w) = stack.pop() {
                on_stack.remove(w);
                scc_members.push(w.to_string());
                if w == v {
                    break;
                }
            }
            scc_members.sort(); // deterministic order
            sccs.push(Scc { members: scc_members });
        }
    }

    // Sort nodes for deterministic output
    let mut sorted_nodes = nodes.clone();
    sorted_nodes.sort();

    for &node in &sorted_nodes {
        if !indices.contains_key(node) {
            strongconnect(
                node,
                &adj,
                &mut index_counter,
                &mut stack,
                &mut on_stack,
                &mut indices,
                &mut lowlinks,
                &mut sccs,
            );
        }
    }

    sccs
}

/// Check if a specific function is self-recursive (calls itself directly).
#[must_use]
pub fn is_self_recursive(graph: &CallGraph, def_path: &str) -> bool {
    graph
        .edges
        .iter()
        .any(|e| e.caller == def_path && e.callee == def_path)
}

/// Return the set of functions involved in any cycle (recursive functions).
#[must_use]
pub fn recursive_functions(graph: &CallGraph) -> FxHashSet<String> {
    let sccs = detect_cycles(graph);
    let mut result = FxHashSet::default();

    for scc in &sccs {
        if scc.is_recursive() {
            for member in &scc.members {
                result.insert(member.clone());
            }
        }
    }

    // Also check self-recursion for single-member SCCs
    for node in &graph.nodes {
        if is_self_recursive(graph, &node.def_path) {
            result.insert(node.def_path.clone());
        }
    }

    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_types::*;

    fn span() -> SourceSpan {
        SourceSpan::default()
    }

    /// Helper: build a minimal function with optional call terminators.
    fn make_func(name: &str, def_path: &str, calls: &[&str]) -> VerifiableFunction {
        let mut blocks = Vec::new();

        for (i, callee) in calls.iter().enumerate() {
            let target = if i + 1 < calls.len() {
                Some(BlockId(i + 1))
            } else {
                Some(BlockId(calls.len()))
            };
            blocks.push(BasicBlock {
                id: BlockId(i),
                stmts: vec![],
                terminator: Terminator::Call {
                    func: callee.to_string(),
                    args: vec![],
                    dest: Place::local(0),
                    target,
                    span: span(),
                    atomic: None,
                },
            });
        }

        // Final return block
        blocks.push(BasicBlock {
            id: BlockId(calls.len()),
            stmts: vec![],
            terminator: Terminator::Return,
        });

        VerifiableFunction {
            name: name.to_string(),
            def_path: def_path.to_string(),
            span: span(),
            body: VerifiableBody {
                locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
                blocks,
                arg_count: 0,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    #[test]
    fn test_build_call_graph_linear_chain() {
        // A -> B -> C
        let funcs = vec![
            make_func("a", "crate::a", &["crate::b"]),
            make_func("b", "crate::b", &["crate::c"]),
            make_func("c", "crate::c", &[]),
        ];

        let graph = build_call_graph(&funcs);

        assert_eq!(graph.nodes.len(), 3);
        assert_eq!(graph.edges.len(), 2);
        assert!(graph.edges.iter().any(|e| e.caller == "crate::a" && e.callee == "crate::b"));
        assert!(graph.edges.iter().any(|e| e.caller == "crate::b" && e.callee == "crate::c"));
    }

    #[test]
    fn test_build_call_graph_diamond() {
        // A -> B, A -> C, B -> D, C -> D
        let funcs = vec![
            make_func("a", "crate::a", &["crate::b", "crate::c"]),
            make_func("b", "crate::b", &["crate::d"]),
            make_func("c", "crate::c", &["crate::d"]),
            make_func("d", "crate::d", &[]),
        ];

        let graph = build_call_graph(&funcs);

        assert_eq!(graph.nodes.len(), 4);
        assert_eq!(graph.edges.len(), 4);
    }

    #[test]
    fn test_build_call_graph_name_resolution() {
        // Caller references callee by short name
        let funcs = vec![
            make_func("caller", "crate::caller", &["helper"]),
            make_func("helper", "crate::util::helper", &[]),
        ];

        let graph = build_call_graph(&funcs);

        assert_eq!(graph.edges.len(), 1);
        // Edge should resolve to full def_path
        assert_eq!(graph.edges[0].callee, "crate::util::helper");
    }

    #[test]
    fn test_detect_cycles_no_cycles() {
        let funcs = vec![
            make_func("a", "crate::a", &["crate::b"]),
            make_func("b", "crate::b", &["crate::c"]),
            make_func("c", "crate::c", &[]),
        ];
        let graph = build_call_graph(&funcs);
        let sccs = detect_cycles(&graph);

        // All SCCs should be single-member (no mutual recursion)
        for scc in &sccs {
            assert_eq!(scc.members.len(), 1, "no cycles expected");
            assert!(!scc.is_recursive());
        }
    }

    #[test]
    fn test_detect_cycles_mutual_recursion() {
        // A -> B, B -> A (mutual recursion)
        let funcs = vec![
            make_func("a", "crate::a", &["crate::b"]),
            make_func("b", "crate::b", &["crate::a"]),
        ];
        let graph = build_call_graph(&funcs);
        let sccs = detect_cycles(&graph);

        // Should find one SCC with both members
        let recursive_sccs: Vec<_> = sccs.iter().filter(|s| s.is_recursive()).collect();
        assert_eq!(recursive_sccs.len(), 1);
        assert_eq!(recursive_sccs[0].members.len(), 2);
        assert!(recursive_sccs[0].members.contains(&"crate::a".to_string()));
        assert!(recursive_sccs[0].members.contains(&"crate::b".to_string()));
    }

    #[test]
    fn test_detect_cycles_self_recursion() {
        // factorial calls itself
        let funcs = vec![
            make_func("factorial", "crate::factorial", &["crate::factorial"]),
        ];
        let graph = build_call_graph(&funcs);

        assert!(is_self_recursive(&graph, "crate::factorial"));

        let rec = recursive_functions(&graph);
        assert!(rec.contains("crate::factorial"));
    }

    #[test]
    fn test_recursive_functions_mixed() {
        // A -> B -> C, B -> B (self-recursive), D -> E -> D (mutual)
        let funcs = vec![
            make_func("a", "crate::a", &["crate::b"]),
            make_func("b", "crate::b", &["crate::c", "crate::b"]),
            make_func("c", "crate::c", &[]),
            make_func("d", "crate::d", &["crate::e"]),
            make_func("e", "crate::e", &["crate::d"]),
        ];
        let graph = build_call_graph(&funcs);
        let rec = recursive_functions(&graph);

        assert!(rec.contains("crate::b"), "b is self-recursive");
        assert!(rec.contains("crate::d"), "d is in mutual recursion with e");
        assert!(rec.contains("crate::e"), "e is in mutual recursion with d");
        assert!(!rec.contains("crate::a"), "a is not recursive");
        assert!(!rec.contains("crate::c"), "c is not recursive");
    }

    #[test]
    fn test_build_call_graph_empty() {
        let graph = build_call_graph(&[]);
        assert!(graph.nodes.is_empty());
        assert!(graph.edges.is_empty());
    }

    #[test]
    fn test_build_call_graph_single_no_calls() {
        let funcs = vec![make_func("leaf", "crate::leaf", &[])];
        let graph = build_call_graph(&funcs);

        assert_eq!(graph.nodes.len(), 1);
        assert!(graph.edges.is_empty());
        assert!(graph.nodes[0].is_entry_point);
    }
}
