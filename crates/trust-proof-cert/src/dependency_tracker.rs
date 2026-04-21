// trust-proof-cert/dependency_tracker.rs: Proof certificate dependency tracking (#268)
//
// Tracks fine-grained proof dependencies between functions: which proofs
// depend on which other proofs, and what kind of dependency exists (callee
// summary, contract assumption, invariant assumption, type invariant).
// Used to determine which proofs must be re-verified when a function changes.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::VecDeque;
use trust_types::fx::{FxHashMap, FxHashSet};

/// The kind of proof dependency between two functions.
///
/// Each variant captures a different reason one function's proof
/// relies on another function's verified properties.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum DependencyKind {
    /// The proof uses a verified summary (contract) of the callee
    /// rather than inlining the callee body.
    CalleeSummary,
    /// The proof assumes a contract (requires/ensures) declared on
    /// the target function holds without re-proving it.
    ContractAssumption,
    /// The proof assumes a loop or data-structure invariant declared
    /// in or associated with the target function.
    InvariantAssumption,
    /// The proof relies on a type invariant (e.g., newtype guarantees,
    /// refinement types) associated with the target.
    TypeInvariant,
}

/// A single proof dependency edge: function `function` depends on
/// function `target` with the given `kind`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ProofDependency {
    /// The function whose proof has this dependency.
    pub function: String,
    /// The kind of dependency.
    pub kind: DependencyKind,
    /// The function being depended upon.
    pub target: String,
}

/// A directed graph of proof-level dependencies between functions.
///
/// Unlike [`crate::DepGraph`] which tracks call-graph structure, this
/// graph tracks *proof* dependencies: which function proofs rely on
/// which other function proofs, annotated with the reason for the
/// dependency. This enables precise invalidation when a function
/// changes: only proofs that actually depend on the changed function
/// need re-verification.
#[derive(Debug, Clone)]
pub(crate) struct DependencyGraph {
    /// Adjacency list: function name -> list of its proof dependencies.
    edges: FxHashMap<String, Vec<ProofDependency>>,
}

impl DependencyGraph {
    /// Create a new empty dependency graph.
    pub fn new() -> Self {
        DependencyGraph {
            edges: FxHashMap::default(),
        }
    }

    /// Add a proof dependency: `function` depends on `target` with the given `kind`.
    ///
    /// Both `function` and `target` are registered as nodes in the graph
    /// even if they have no other edges.
    pub fn add_dependency(&mut self, function: &str, kind: DependencyKind, target: &str) {
        // Ensure target node exists in the graph.
        self.edges
            .entry(target.to_string())
            .or_default();

        let dep = ProofDependency {
            function: function.to_string(),
            kind,
            target: target.to_string(),
        };
        self.edges
            .entry(function.to_string())
            .or_default()
            .push(dep);
    }

    /// Return the direct dependencies of a function, or an empty slice
    /// if the function has none or is not in the graph.
    pub fn direct_dependencies(&self, function: &str) -> &[ProofDependency] {
        match self.edges.get(function) {
            Some(deps) => deps.as_slice(),
            None => &[],
        }
    }

    /// Return all functions whose proofs would be invalidated if
    /// `changed_function` is modified.
    ///
    /// A proof is invalidated if it has a direct dependency on the
    /// changed function. This performs a single-hop reverse lookup.
    pub fn invalidated_by(&self, changed_function: &str) -> Vec<String> {
        let mut result = FxHashSet::default();
        for (func, deps) in &self.edges {
            for dep in deps {
                if dep.target == changed_function {
                    result.insert(func.clone());
                }
            }
        }
        let mut sorted: Vec<String> = result.into_iter().collect();
        sorted.sort();
        sorted
    }

    /// Compute the full transitive closure of dependencies for a function.
    ///
    /// Returns all functions that `function` transitively depends on
    /// (directly or through chains of dependencies). The result does
    /// NOT include `function` itself unless there is a cycle.
    pub fn transitive_dependencies(&self, function: &str) -> Vec<String> {
        let mut visited = FxHashSet::default();
        let mut queue = VecDeque::new();

        // Seed with direct dependency targets.
        for dep in self.direct_dependencies(function) {
            if !visited.contains(&dep.target) {
                visited.insert(dep.target.clone());
                queue.push_back(dep.target.clone());
            }
        }

        // BFS over dependency targets.
        while let Some(current) = queue.pop_front() {
            for dep in self.direct_dependencies(&current) {
                if !visited.contains(&dep.target) {
                    visited.insert(dep.target.clone());
                    queue.push_back(dep.target.clone());
                }
            }
        }

        let mut sorted: Vec<String> = visited.into_iter().collect();
        sorted.sort();
        sorted
    }

    /// Return functions in topological (dependency) order.
    ///
    /// Functions with no dependencies appear first; functions that
    /// depend on others appear after their dependencies. Returns
    /// `None` if the graph contains a cycle.
    pub fn topological_order(&self) -> Option<Vec<String>> {
        // Compute in-degree based on dependency edges.
        // Edge: function -> target means function depends on target.
        // For topological order (dependencies first), we reverse: target before function.
        let mut in_degree: FxHashMap<&str, usize> = FxHashMap::default();
        for func in self.edges.keys() {
            in_degree.entry(func.as_str()).or_insert(0);
        }
        for deps in self.edges.values() {
            for dep in deps {
                // function depends on target; in the "deps first" ordering,
                // function has an incoming edge from target. So function's
                // in-degree increases.
                *in_degree.entry(dep.function.as_str()).or_insert(0) += 1;
            }
        }

        // Kahn's algorithm: start with nodes that have zero in-degree
        // (i.e., no dependencies — the roots).
        let mut queue: VecDeque<String> = VecDeque::new();
        let mut zero_deg: Vec<&str> = in_degree
            .iter()
            .filter(|(_, deg)| **deg == 0)
            .map(|(name, _)| *name)
            .collect();
        zero_deg.sort(); // deterministic
        for name in zero_deg {
            queue.push_back(name.to_string());
        }

        let mut result = Vec::new();
        while let Some(func) = queue.pop_front() {
            result.push(func.clone());
            // Find all functions that depend on `func` (i.e., have `func` as target).
            for (dependent, deps) in &self.edges {
                let depends_on_func = deps.iter().any(|d| d.target == func);
                if depends_on_func
                    && let Some(deg) = in_degree.get_mut(dependent.as_str()) {
                        *deg = deg.saturating_sub(1);
                        if *deg == 0 {
                            // Insert in sorted position for determinism.
                            let pos = queue
                                .iter()
                                .position(|q| q.as_str() > dependent.as_str())
                                .unwrap_or(queue.len());
                            queue.insert(pos, dependent.clone());
                        }
                    }
            }
        }

        if result.len() != self.edges.len() {
            None // cycle detected
        } else {
            Some(result)
        }
    }

    /// Return true if the dependency graph contains a cycle.
    pub fn is_cyclic(&self) -> bool {
        self.topological_order().is_none()
    }

    /// Return all root functions: those with no proof dependencies.
    ///
    /// Root functions are the leaves of the dependency tree — they
    /// can be verified independently without assuming anything about
    /// other functions.
    pub fn roots(&self) -> Vec<String> {
        let mut result: Vec<String> = self
            .edges
            .iter()
            .filter(|(_, deps)| deps.is_empty())
            .map(|(func, _)| func.clone())
            .collect();
        result.sort();
        result
    }
}

impl Default for DependencyGraph {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // -------------------------------------------------------------------
    // Empty graph
    // -------------------------------------------------------------------

    #[test]
    fn test_empty_graph() {
        let graph = DependencyGraph::new();
        assert!(graph.roots().is_empty());
        assert!(!graph.is_cyclic());
        assert_eq!(graph.topological_order(), Some(vec![]));
        assert!(graph.direct_dependencies("anything").is_empty());
        assert!(graph.invalidated_by("anything").is_empty());
        assert!(graph.transitive_dependencies("anything").is_empty());
    }

    #[test]
    fn test_default_is_empty() {
        let graph = DependencyGraph::default();
        assert!(graph.edges.is_empty());
    }

    // -------------------------------------------------------------------
    // Adding dependencies
    // -------------------------------------------------------------------

    #[test]
    fn test_add_single_dependency() {
        let mut graph = DependencyGraph::new();
        graph.add_dependency("caller", DependencyKind::CalleeSummary, "callee");

        let deps = graph.direct_dependencies("caller");
        assert_eq!(deps.len(), 1);
        assert_eq!(deps[0].function, "caller");
        assert_eq!(deps[0].target, "callee");
        assert_eq!(deps[0].kind, DependencyKind::CalleeSummary);
    }

    #[test]
    fn test_add_multiple_dependency_kinds() {
        let mut graph = DependencyGraph::new();
        graph.add_dependency("foo", DependencyKind::CalleeSummary, "bar");
        graph.add_dependency("foo", DependencyKind::ContractAssumption, "baz");
        graph.add_dependency("foo", DependencyKind::InvariantAssumption, "bar");
        graph.add_dependency("foo", DependencyKind::TypeInvariant, "Wrapper");

        let deps = graph.direct_dependencies("foo");
        assert_eq!(deps.len(), 4);

        let kinds: FxHashSet<DependencyKind> = deps.iter().map(|d| d.kind.clone()).collect();
        assert!(kinds.contains(&DependencyKind::CalleeSummary));
        assert!(kinds.contains(&DependencyKind::ContractAssumption));
        assert!(kinds.contains(&DependencyKind::InvariantAssumption));
        assert!(kinds.contains(&DependencyKind::TypeInvariant));
    }

    #[test]
    fn test_add_dependency_registers_both_nodes() {
        let mut graph = DependencyGraph::new();
        graph.add_dependency("a", DependencyKind::CalleeSummary, "b");

        // Both "a" and "b" should exist as keys in the graph.
        assert!(graph.edges.contains_key("a"));
        assert!(graph.edges.contains_key("b"));
        // "b" has no outgoing dependencies.
        assert!(graph.direct_dependencies("b").is_empty());
    }

    // -------------------------------------------------------------------
    // Invalidation (reverse lookup)
    // -------------------------------------------------------------------

    #[test]
    fn test_invalidated_by_single() {
        let mut graph = DependencyGraph::new();
        graph.add_dependency("caller", DependencyKind::CalleeSummary, "helper");

        let invalidated = graph.invalidated_by("helper");
        assert_eq!(invalidated, vec!["caller"]);
    }

    #[test]
    fn test_invalidated_by_multiple() {
        let mut graph = DependencyGraph::new();
        graph.add_dependency("a", DependencyKind::CalleeSummary, "shared");
        graph.add_dependency("b", DependencyKind::ContractAssumption, "shared");
        graph.add_dependency("c", DependencyKind::TypeInvariant, "other");

        let invalidated = graph.invalidated_by("shared");
        assert_eq!(invalidated, vec!["a", "b"]);
    }

    #[test]
    fn test_invalidated_by_unknown_function() {
        let mut graph = DependencyGraph::new();
        graph.add_dependency("a", DependencyKind::CalleeSummary, "b");

        let invalidated = graph.invalidated_by("unknown");
        assert!(invalidated.is_empty());
    }

    // -------------------------------------------------------------------
    // Transitive dependencies
    // -------------------------------------------------------------------

    #[test]
    fn test_transitive_linear_chain() {
        let mut graph = DependencyGraph::new();
        graph.add_dependency("a", DependencyKind::CalleeSummary, "b");
        graph.add_dependency("b", DependencyKind::CalleeSummary, "c");
        graph.add_dependency("c", DependencyKind::CalleeSummary, "d");

        let trans = graph.transitive_dependencies("a");
        assert_eq!(trans, vec!["b", "c", "d"]);
    }

    #[test]
    fn test_transitive_diamond() {
        let mut graph = DependencyGraph::new();
        graph.add_dependency("top", DependencyKind::CalleeSummary, "left");
        graph.add_dependency("top", DependencyKind::CalleeSummary, "right");
        graph.add_dependency("left", DependencyKind::CalleeSummary, "bottom");
        graph.add_dependency("right", DependencyKind::CalleeSummary, "bottom");

        let trans = graph.transitive_dependencies("top");
        assert_eq!(trans, vec!["bottom", "left", "right"]);
    }

    #[test]
    fn test_transitive_of_leaf() {
        let mut graph = DependencyGraph::new();
        graph.add_dependency("a", DependencyKind::CalleeSummary, "b");

        let trans = graph.transitive_dependencies("b");
        assert!(trans.is_empty());
    }

    #[test]
    fn test_transitive_with_cycle_terminates() {
        let mut graph = DependencyGraph::new();
        graph.add_dependency("a", DependencyKind::CalleeSummary, "b");
        graph.add_dependency("b", DependencyKind::CalleeSummary, "a");

        // Should terminate despite the cycle.
        let trans = graph.transitive_dependencies("a");
        // "a" depends on "b", "b" depends on "a"; transitive deps of "a"
        // include "b" (direct) and "a" itself (via the cycle back).
        assert!(trans.contains(&"b".to_string()));
        assert!(trans.contains(&"a".to_string()));
    }

    // -------------------------------------------------------------------
    // Topological order
    // -------------------------------------------------------------------

    #[test]
    fn test_topological_order_linear() {
        let mut graph = DependencyGraph::new();
        graph.add_dependency("main", DependencyKind::CalleeSummary, "helper");
        graph.add_dependency("helper", DependencyKind::CalleeSummary, "leaf");

        let order = graph.topological_order().expect("acyclic graph should have topo order");
        let pos_leaf = order.iter().position(|x| x == "leaf").expect("leaf in order");
        let pos_helper = order.iter().position(|x| x == "helper").expect("helper in order");
        let pos_main = order.iter().position(|x| x == "main").expect("main in order");

        assert!(pos_leaf < pos_helper, "leaf before helper");
        assert!(pos_helper < pos_main, "helper before main");
    }

    #[test]
    fn test_topological_order_independent_nodes() {
        let mut graph = DependencyGraph::new();
        // Two independent subgraphs.
        graph.add_dependency("a", DependencyKind::CalleeSummary, "b");
        graph.add_dependency("c", DependencyKind::ContractAssumption, "d");

        let order = graph.topological_order().expect("acyclic graph");
        assert_eq!(order.len(), 4);

        // b before a, d before c.
        let pos_a = order.iter().position(|x| x == "a").unwrap();
        let pos_b = order.iter().position(|x| x == "b").unwrap();
        let pos_c = order.iter().position(|x| x == "c").unwrap();
        let pos_d = order.iter().position(|x| x == "d").unwrap();
        assert!(pos_b < pos_a);
        assert!(pos_d < pos_c);
    }

    // -------------------------------------------------------------------
    // Cycle detection
    // -------------------------------------------------------------------

    #[test]
    fn test_is_cyclic_false() {
        let mut graph = DependencyGraph::new();
        graph.add_dependency("a", DependencyKind::CalleeSummary, "b");
        graph.add_dependency("b", DependencyKind::CalleeSummary, "c");

        assert!(!graph.is_cyclic());
    }

    #[test]
    fn test_is_cyclic_true() {
        let mut graph = DependencyGraph::new();
        graph.add_dependency("a", DependencyKind::CalleeSummary, "b");
        graph.add_dependency("b", DependencyKind::CalleeSummary, "a");

        assert!(graph.is_cyclic());
    }

    #[test]
    fn test_is_cyclic_self_loop() {
        let mut graph = DependencyGraph::new();
        graph.add_dependency("recursive", DependencyKind::InvariantAssumption, "recursive");

        assert!(graph.is_cyclic());
    }

    #[test]
    fn test_topological_order_with_cycle_returns_none() {
        let mut graph = DependencyGraph::new();
        graph.add_dependency("x", DependencyKind::CalleeSummary, "y");
        graph.add_dependency("y", DependencyKind::CalleeSummary, "z");
        graph.add_dependency("z", DependencyKind::CalleeSummary, "x");

        assert!(graph.topological_order().is_none());
    }

    // -------------------------------------------------------------------
    // Roots
    // -------------------------------------------------------------------

    #[test]
    fn test_roots_simple() {
        let mut graph = DependencyGraph::new();
        graph.add_dependency("caller", DependencyKind::CalleeSummary, "leaf1");
        graph.add_dependency("caller", DependencyKind::ContractAssumption, "leaf2");

        let roots = graph.roots();
        assert_eq!(roots, vec!["leaf1", "leaf2"]);
    }

    #[test]
    fn test_roots_all_independent() {
        let mut graph = DependencyGraph::new();
        // Add nodes with no dependencies by making them targets.
        graph.add_dependency("a", DependencyKind::CalleeSummary, "b");
        graph.add_dependency("c", DependencyKind::CalleeSummary, "d");

        // b and d are roots (no outgoing deps).
        let roots = graph.roots();
        assert_eq!(roots, vec!["b", "d"]);
    }

    #[test]
    fn test_roots_no_roots_in_cycle() {
        let mut graph = DependencyGraph::new();
        graph.add_dependency("a", DependencyKind::CalleeSummary, "b");
        graph.add_dependency("b", DependencyKind::CalleeSummary, "a");

        // In a pure cycle, no node has zero dependencies.
        let roots = graph.roots();
        assert!(roots.is_empty());
    }
}
