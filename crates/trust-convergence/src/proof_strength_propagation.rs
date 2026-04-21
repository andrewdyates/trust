// trust-convergence proof strength propagation through composition DAG
//
// When functions are composed (f calls g), the effective proof strength of
// the composition is limited by the weakest link. A function verified at
// L2Domain that calls a function only verified at L0Safety should have its
// effective proof strength capped at L0Safety for properties that depend
// on the callee.
//
// Part of #662 (Part of #442)
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::{FxHashMap, FxHashSet};

use trust_types::ProofLevel;

/// Identifier for a function in the composition DAG.
///
/// Uses a string-based identifier consistent with the rest of the tRust
/// crate ecosystem (e.g., `DepGraph` in trust-proof-cert uses `String`).
pub(crate) type FnId = String;

/// A directed graph of function call dependencies for proof composition.
///
/// Edges go from caller to callee: if function A calls function B,
/// then `edges[A]` contains `B`. This is the same convention used
/// by `DepGraph` in trust-proof-cert.
#[derive(Debug, Clone)]
pub(crate) struct CompositionDag {
    /// Adjacency list: function -> set of callees.
    edges: FxHashMap<FnId, FxHashSet<FnId>>,
}

impl CompositionDag {
    /// Create a new empty composition DAG.
    #[must_use]
    pub fn new() -> Self {
        Self {
            edges: FxHashMap::default(),
        }
    }

    /// Add a function node to the DAG (with no callees initially).
    pub fn add_function(&mut self, function: impl Into<FnId>) {
        self.edges.entry(function.into()).or_default();
    }

    /// Add a call edge: `caller` calls `callee`.
    ///
    /// Both functions are added to the DAG if not already present.
    pub fn add_call(&mut self, caller: impl Into<FnId>, callee: impl Into<FnId>) {
        let caller = caller.into();
        let callee = callee.into();
        self.edges.entry(callee.clone()).or_default();
        self.edges.entry(caller.clone()).or_default().insert(callee);
    }

    /// Return all function IDs in the DAG.
    pub fn functions(&self) -> impl Iterator<Item = &FnId> {
        self.edges.keys()
    }

    /// Return the callees of a function, or an empty set if unknown.
    pub fn callees(&self, function: &str) -> &FxHashSet<FnId> {
        static EMPTY: std::sync::LazyLock<FxHashSet<FnId>> =
            std::sync::LazyLock::new(FxHashSet::default);
        self.edges.get(function).unwrap_or(&EMPTY)
    }

    /// Return the number of functions in the DAG.
    #[must_use]
    pub fn len(&self) -> usize {
        self.edges.len()
    }

    /// Return true if the DAG has no functions.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.edges.is_empty()
    }
}

impl Default for CompositionDag {
    fn default() -> Self {
        Self::new()
    }
}

/// Propagates proof strength through a function composition DAG.
///
/// The effective proof level of a function is the minimum of its own
/// declared proof level and the effective proof levels of all its
/// transitive callees. This captures the principle that a composition
/// is only as strong as its weakest link.
///
/// Cycles (mutual recursion) are handled by computing the minimum
/// proof level within each strongly connected component and assigning
/// that level to all functions in the cycle.
#[derive(Debug)]
pub(crate) struct ProofStrengthPropagator;

impl ProofStrengthPropagator {
    /// Propagate proof strength through the composition DAG.
    ///
    /// For each function, computes the effective proof level as:
    ///   min(own_level, min(effective_level(callee) for each callee))
    ///
    /// Functions not present in `per_fn_strength` are treated as having
    /// no proof (excluded from the result).
    ///
    /// # Algorithm
    ///
    /// 1. Compute SCCs using Tarjan's algorithm.
    /// 2. Process SCCs in reverse topological order (callees before callers).
    /// 3. For each SCC:
    ///    a. Compute the minimum declared strength within the SCC.
    ///    b. Compute the minimum effective strength of all callees outside
    ///    the SCC (already computed in step 2).
    ///    c. Effective strength = min(a, b).
    /// 4. Assign the effective strength to all functions in the SCC.
    #[must_use]
    pub fn propagate(
        dag: &CompositionDag,
        per_fn_strength: &FxHashMap<FnId, ProofLevel>,
    ) -> FxHashMap<FnId, ProofLevel> {
        let sccs = tarjan_sccs(dag);
        let mut effective: FxHashMap<FnId, ProofLevel> = FxHashMap::default();

        // SCCs are returned in reverse topological order by Tarjan's:
        // leaf SCCs (callees) come first.
        for scc in &sccs {
            // Step 3a: minimum declared strength within the SCC.
            let mut scc_min: Option<ProofLevel> = None;
            for fn_id in &scc.members {
                if let Some(&level) = per_fn_strength.get(fn_id) {
                    scc_min = Some(match scc_min {
                        Some(current) if level < current => level,
                        Some(current) => current,
                        None => level,
                    });
                }
            }

            // If no function in the SCC has a declared strength, skip.
            let Some(mut scc_level) = scc_min else {
                continue;
            };

            // Step 3b: minimum effective strength of external callees.
            for fn_id in &scc.members {
                for callee in dag.callees(fn_id) {
                    // Skip callees within the same SCC (handled by scc_min).
                    if scc.members.contains(callee) {
                        continue;
                    }
                    // Only consider callees that have an effective level.
                    if let Some(&callee_level) = effective.get(callee)
                        && callee_level < scc_level {
                            scc_level = callee_level;
                        }
                    // Callees not in per_fn_strength (and thus not in effective)
                    // are external/unknown — we don't reduce strength for them.
                    // The DAG only contains functions we know about.
                }
            }

            // Step 4: assign effective strength to all SCC members that
            // have a declared strength.
            for fn_id in &scc.members {
                if per_fn_strength.contains_key(fn_id) {
                    effective.insert(fn_id.clone(), scc_level);
                }
            }
        }

        effective
    }
}

// ---------------------------------------------------------------------------
// Tarjan's SCC algorithm (local implementation to avoid dep on trust-proof-cert)
// ---------------------------------------------------------------------------

/// A strongly connected component.
#[derive(Debug, Clone)]
struct Scc {
    members: FxHashSet<FnId>,
}

/// Compute SCCs of the composition DAG using Tarjan's algorithm.
///
/// Returns SCCs in reverse topological order: leaf SCCs first, root SCCs last.
fn tarjan_sccs(dag: &CompositionDag) -> Vec<Scc> {
    let mut state = TarjanState {
        index_counter: 0,
        index: FxHashMap::default(),
        lowlink: FxHashMap::default(),
        on_stack: FxHashSet::default(),
        stack: Vec::new(),
        sccs: Vec::new(),
    };

    for fn_id in dag.functions() {
        if !state.index.contains_key(fn_id.as_str()) {
            tarjan_visit(dag, fn_id, &mut state);
        }
    }

    state.sccs
}

struct TarjanState<'a> {
    index_counter: usize,
    index: FxHashMap<&'a str, usize>,
    lowlink: FxHashMap<&'a str, usize>,
    on_stack: FxHashSet<&'a str>,
    stack: Vec<&'a str>,
    sccs: Vec<Scc>,
}

fn tarjan_visit<'a>(dag: &'a CompositionDag, node: &'a str, state: &mut TarjanState<'a>) {
    let idx = state.index_counter;
    state.index_counter += 1;
    state.index.insert(node, idx);
    state.lowlink.insert(node, idx);
    state.stack.push(node);
    state.on_stack.insert(node);

    for callee in dag.callees(node) {
        let callee_str = callee.as_str();
        if !dag.edges.contains_key(callee_str) {
            continue; // external function, not in DAG
        }
        if !state.index.contains_key(callee_str) {
            tarjan_visit(dag, callee_str, state);
            let callee_low = state.lowlink[callee_str];
            let node_low = state.lowlink[node];
            if callee_low < node_low {
                state.lowlink.insert(node, callee_low);
            }
        } else if state.on_stack.contains(callee_str) {
            let callee_idx = state.index[callee_str];
            let node_low = state.lowlink[node];
            if callee_idx < node_low {
                state.lowlink.insert(node, callee_idx);
            }
        }
    }

    // Root of SCC
    if state.lowlink[node] == state.index[node] {
        let mut members = FxHashSet::default();
        loop {
            let w = state
                .stack
                .pop()
                .unwrap_or_else(|| unreachable!("Tarjan stack empty when popping SCC"));
            state.on_stack.remove(w);
            members.insert(w.to_string());
            if w == node {
                break;
            }
        }
        state.sccs.push(Scc { members });
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper: build a strength map from tuples.
    fn strengths(entries: &[(&str, ProofLevel)]) -> FxHashMap<FnId, ProofLevel> {
        entries
            .iter()
            .map(|(name, level)| (name.to_string(), *level))
            .collect()
    }

    // -----------------------------------------------------------------------
    // Linear chain tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_linear_chain_weakest_propagates_up() {
        // A(L2) -> B(L1) -> C(L0)
        // Effective: A=L0, B=L0, C=L0
        let mut dag = CompositionDag::new();
        dag.add_call("A", "B");
        dag.add_call("B", "C");
        dag.add_function("C");

        let strength = strengths(&[
            ("A", ProofLevel::L2Domain),
            ("B", ProofLevel::L1Functional),
            ("C", ProofLevel::L0Safety),
        ]);

        let effective = ProofStrengthPropagator::propagate(&dag, &strength);

        assert_eq!(effective["A"], ProofLevel::L0Safety);
        assert_eq!(effective["B"], ProofLevel::L0Safety);
        assert_eq!(effective["C"], ProofLevel::L0Safety);
    }

    #[test]
    fn test_linear_chain_all_same_level() {
        // A(L1) -> B(L1) -> C(L1)
        // All stay L1.
        let mut dag = CompositionDag::new();
        dag.add_call("A", "B");
        dag.add_call("B", "C");
        dag.add_function("C");

        let strength = strengths(&[
            ("A", ProofLevel::L1Functional),
            ("B", ProofLevel::L1Functional),
            ("C", ProofLevel::L1Functional),
        ]);

        let effective = ProofStrengthPropagator::propagate(&dag, &strength);

        assert_eq!(effective["A"], ProofLevel::L1Functional);
        assert_eq!(effective["B"], ProofLevel::L1Functional);
        assert_eq!(effective["C"], ProofLevel::L1Functional);
    }

    #[test]
    fn test_linear_chain_caller_weaker_than_callee() {
        // A(L0) -> B(L2)
        // A is already the weakest, effective: A=L0, B=L2
        let mut dag = CompositionDag::new();
        dag.add_call("A", "B");
        dag.add_function("B");

        let strength = strengths(&[
            ("A", ProofLevel::L0Safety),
            ("B", ProofLevel::L2Domain),
        ]);

        let effective = ProofStrengthPropagator::propagate(&dag, &strength);

        assert_eq!(effective["A"], ProofLevel::L0Safety);
        assert_eq!(effective["B"], ProofLevel::L2Domain);
    }

    // -----------------------------------------------------------------------
    // Diamond DAG tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_diamond_minimum_propagates() {
        // A -> B, A -> C, B -> D, C -> D
        // A(L2), B(L2), C(L1), D(L0)
        // Effective: D=L0, B=L0, C=L0, A=L0
        let mut dag = CompositionDag::new();
        dag.add_call("A", "B");
        dag.add_call("A", "C");
        dag.add_call("B", "D");
        dag.add_call("C", "D");
        dag.add_function("D");

        let strength = strengths(&[
            ("A", ProofLevel::L2Domain),
            ("B", ProofLevel::L2Domain),
            ("C", ProofLevel::L1Functional),
            ("D", ProofLevel::L0Safety),
        ]);

        let effective = ProofStrengthPropagator::propagate(&dag, &strength);

        assert_eq!(effective["D"], ProofLevel::L0Safety);
        assert_eq!(effective["B"], ProofLevel::L0Safety);
        assert_eq!(effective["C"], ProofLevel::L0Safety);
        assert_eq!(effective["A"], ProofLevel::L0Safety);
    }

    #[test]
    fn test_diamond_asymmetric_strengths() {
        // A -> B, A -> C, B -> D, C -> D
        // A(L2), B(L1), C(L2), D(L2)
        // D=L2, B=min(L1,L2)=L1, C=min(L2,L2)=L2, A=min(L2,L1,L2)=L1
        let mut dag = CompositionDag::new();
        dag.add_call("A", "B");
        dag.add_call("A", "C");
        dag.add_call("B", "D");
        dag.add_call("C", "D");
        dag.add_function("D");

        let strength = strengths(&[
            ("A", ProofLevel::L2Domain),
            ("B", ProofLevel::L1Functional),
            ("C", ProofLevel::L2Domain),
            ("D", ProofLevel::L2Domain),
        ]);

        let effective = ProofStrengthPropagator::propagate(&dag, &strength);

        assert_eq!(effective["D"], ProofLevel::L2Domain);
        assert_eq!(effective["B"], ProofLevel::L1Functional);
        assert_eq!(effective["C"], ProofLevel::L2Domain);
        assert_eq!(effective["A"], ProofLevel::L1Functional);
    }

    // -----------------------------------------------------------------------
    // Cycle / recursion tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_self_recursive_no_reduction() {
        // A(L1) -> A (self-call)
        // Effective: A=L1 (self-call does not reduce own level)
        let mut dag = CompositionDag::new();
        dag.add_call("A", "A");

        let strength = strengths(&[("A", ProofLevel::L1Functional)]);

        let effective = ProofStrengthPropagator::propagate(&dag, &strength);

        assert_eq!(effective["A"], ProofLevel::L1Functional);
    }

    #[test]
    fn test_mutual_recursion_min_of_cycle() {
        // A(L2) <-> B(L0) (mutual recursion)
        // Both get min(L2, L0) = L0
        let mut dag = CompositionDag::new();
        dag.add_call("A", "B");
        dag.add_call("B", "A");

        let strength = strengths(&[
            ("A", ProofLevel::L2Domain),
            ("B", ProofLevel::L0Safety),
        ]);

        let effective = ProofStrengthPropagator::propagate(&dag, &strength);

        assert_eq!(effective["A"], ProofLevel::L0Safety);
        assert_eq!(effective["B"], ProofLevel::L0Safety);
    }

    #[test]
    fn test_three_way_cycle() {
        // A(L2) -> B(L1) -> C(L2) -> A
        // All get min(L2, L1, L2) = L1
        let mut dag = CompositionDag::new();
        dag.add_call("A", "B");
        dag.add_call("B", "C");
        dag.add_call("C", "A");

        let strength = strengths(&[
            ("A", ProofLevel::L2Domain),
            ("B", ProofLevel::L1Functional),
            ("C", ProofLevel::L2Domain),
        ]);

        let effective = ProofStrengthPropagator::propagate(&dag, &strength);

        assert_eq!(effective["A"], ProofLevel::L1Functional);
        assert_eq!(effective["B"], ProofLevel::L1Functional);
        assert_eq!(effective["C"], ProofLevel::L1Functional);
    }

    #[test]
    fn test_cycle_with_external_callee() {
        // A(L2) <-> B(L2), and B -> C(L0)
        // The cycle {A,B} has min declared = L2, but B calls C(L0) outside the cycle.
        // Effective for cycle = min(L2, L0) = L0
        let mut dag = CompositionDag::new();
        dag.add_call("A", "B");
        dag.add_call("B", "A");
        dag.add_call("B", "C");
        dag.add_function("C");

        let strength = strengths(&[
            ("A", ProofLevel::L2Domain),
            ("B", ProofLevel::L2Domain),
            ("C", ProofLevel::L0Safety),
        ]);

        let effective = ProofStrengthPropagator::propagate(&dag, &strength);

        assert_eq!(effective["C"], ProofLevel::L0Safety);
        assert_eq!(effective["A"], ProofLevel::L0Safety);
        assert_eq!(effective["B"], ProofLevel::L0Safety);
    }

    // -----------------------------------------------------------------------
    // Edge cases
    // -----------------------------------------------------------------------

    #[test]
    fn test_empty_dag() {
        let dag = CompositionDag::new();
        let strength = FxHashMap::default();
        let effective = ProofStrengthPropagator::propagate(&dag, &strength);
        assert!(effective.is_empty());
    }

    #[test]
    fn test_single_function_no_calls() {
        let mut dag = CompositionDag::new();
        dag.add_function("A");

        let strength = strengths(&[("A", ProofLevel::L2Domain)]);
        let effective = ProofStrengthPropagator::propagate(&dag, &strength);

        assert_eq!(effective["A"], ProofLevel::L2Domain);
    }

    #[test]
    fn test_function_not_in_strength_map_excluded() {
        // B is in the DAG but not in the strength map => excluded from results
        let mut dag = CompositionDag::new();
        dag.add_call("A", "B");
        dag.add_function("B");

        let strength = strengths(&[("A", ProofLevel::L2Domain)]);
        let effective = ProofStrengthPropagator::propagate(&dag, &strength);

        assert_eq!(effective["A"], ProofLevel::L2Domain);
        assert!(!effective.contains_key("B"));
    }

    #[test]
    fn test_disconnected_components() {
        // Two disconnected subgraphs
        // A(L2) -> B(L0) and C(L1) -> D(L1)
        let mut dag = CompositionDag::new();
        dag.add_call("A", "B");
        dag.add_function("B");
        dag.add_call("C", "D");
        dag.add_function("D");

        let strength = strengths(&[
            ("A", ProofLevel::L2Domain),
            ("B", ProofLevel::L0Safety),
            ("C", ProofLevel::L1Functional),
            ("D", ProofLevel::L1Functional),
        ]);

        let effective = ProofStrengthPropagator::propagate(&dag, &strength);

        assert_eq!(effective["A"], ProofLevel::L0Safety);
        assert_eq!(effective["B"], ProofLevel::L0Safety);
        assert_eq!(effective["C"], ProofLevel::L1Functional);
        assert_eq!(effective["D"], ProofLevel::L1Functional);
    }

    // -----------------------------------------------------------------------
    // CompositionDag API tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_dag_default_is_empty() {
        let dag = CompositionDag::default();
        assert!(dag.is_empty());
        assert_eq!(dag.len(), 0);
    }

    #[test]
    fn test_dag_add_function_and_call() {
        let mut dag = CompositionDag::new();
        dag.add_function("A");
        assert_eq!(dag.len(), 1);

        dag.add_call("A", "B");
        assert_eq!(dag.len(), 2); // B auto-added
        assert!(dag.callees("A").contains("B"));
        assert!(dag.callees("B").is_empty());
    }

    #[test]
    fn test_dag_duplicate_calls_idempotent() {
        let mut dag = CompositionDag::new();
        dag.add_call("A", "B");
        dag.add_call("A", "B");
        assert_eq!(dag.callees("A").len(), 1);
    }
}
