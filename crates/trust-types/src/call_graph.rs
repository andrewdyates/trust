// trust-types/call_graph.rs: Call graph types for reachability analysis
//
// Pure data types for call graph representation.
// Analysis logic (BFS reachability) moved to trust-vcgen/reachability.rs per #162.
//
// Part of #52
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};

use crate::model::SourceSpan;

/// A node in the call graph representing a single function.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CallGraphNode {
    /// Fully qualified def_path (e.g., "crate::module::function").
    pub def_path: String,
    /// Human-readable name.
    pub name: String,
    /// Whether this function is a public API entry point.
    pub is_public: bool,
    /// Whether this function is an entry point (main, #[test], #[tokio::main], etc.).
    pub is_entry_point: bool,
    /// Source location.
    pub span: SourceSpan,
}

/// A directed edge in the call graph: caller -> callee.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CallGraphEdge {
    /// Def path of the calling function.
    pub caller: String,
    /// Def path or name of the called function.
    pub callee: String,
    /// Source location of the call site.
    pub call_site: SourceSpan,
}

/// A complete call graph for a crate.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct CallGraph {
    /// All functions in the crate.
    pub nodes: Vec<CallGraphNode>,
    /// All call edges (caller -> callee).
    pub edges: Vec<CallGraphEdge>,
}

impl CallGraph {
    /// Create a new empty call graph.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a function node to the graph.
    pub fn add_node(&mut self, node: CallGraphNode) {
        self.nodes.push(node);
    }

    /// Add a call edge to the graph.
    pub fn add_edge(&mut self, edge: CallGraphEdge) {
        self.edges.push(edge);
    }

    /// Return all entry point def_paths.
    #[must_use]
    pub fn entry_points(&self) -> Vec<&str> {
        self.nodes
            .iter()
            .filter(|n| n.is_entry_point)
            .map(|n| n.def_path.as_str())
            .collect()
    }

    /// Return all public function def_paths.
    #[must_use]
    pub fn public_functions(&self) -> Vec<&str> {
        self.nodes
            .iter()
            .filter(|n| n.is_public)
            .map(|n| n.def_path.as_str())
            .collect()
    }
}

/// Result of reachability analysis on a call graph.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ReachabilityResult {
    /// Entry points used as BFS roots.
    pub entry_points: Vec<String>,
    /// Public functions reachable from entry points.
    pub reachable: Vec<ReachableFunction>,
    /// Public functions NOT reachable from any entry point.
    pub unreachable: Vec<UnreachableFunction>,
    /// Total number of functions in the graph.
    pub total_functions: usize,
    /// Total number of call edges.
    pub total_edges: usize,
}

impl ReachabilityResult {
    /// Returns true if all public functions are reachable.
    #[must_use]
    pub fn is_fully_connected(&self) -> bool {
        self.unreachable.is_empty()
    }

    /// Number of unreachable public functions.
    #[must_use]
    pub fn unreachable_count(&self) -> usize {
        self.unreachable.len()
    }
}

/// A public function that is reachable from entry points.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ReachableFunction {
    pub def_path: String,
    pub name: String,
    pub span: SourceSpan,
}

/// A public function that is NOT reachable from any entry point.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct UnreachableFunction {
    pub def_path: String,
    pub name: String,
    pub span: SourceSpan,
    /// Why the function is considered unreachable.
    pub reason: String,
}
