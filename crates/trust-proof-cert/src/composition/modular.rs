// trust-proof-cert modular composition
//
// Cross-function modular proof composition with cycle detection.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet};

use crate::{CertificationStatus, ProofCertificate};

use super::checkers::weakest_strength;
use super::types::{ComposedProof, CompositionError, FunctionStrength};

/// Compose a caller's certificate with its callees' certificates
/// for modular cross-function verification.
///
/// The caller_cert proves properties about the caller under assumptions
/// about its callees. The callee_certs discharge those assumptions.
///
/// `call_graph` maps each function name to the list of functions it calls.
/// This is used for full DFS-based cycle detection across the entire
/// callee dependency graph, catching mutual recursion (A -> B -> A),
/// longer transitive cycles (A -> B -> C -> A), and direct self-recursion.
///
/// If `call_graph` is empty, only direct self-reference (caller in its own
/// `required_callees`) is detectable. Pass the full call graph for sound
/// cycle detection.
// tRust: BTreeMap for deterministic certificate output (#827)
pub fn modular_composition(
    caller_cert: &ProofCertificate,
    callee_certs: &[&ProofCertificate],
    required_callees: &[String],
    call_graph: &BTreeMap<String, Vec<String>>,
) -> Result<ComposedProof, CompositionError> {
    // Build callee_deps from the call_graph: for each callee (and any
    // transitively reachable function), look up its own callees in the graph.
    let mut callee_deps: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for callee_name in required_callees {
        if let Some(deps) = call_graph.get(callee_name) {
            callee_deps.insert(callee_name.clone(), deps.clone());
        }
    }
    // Propagate transitive dependencies so the DFS can walk the full graph.
    let mut frontier: Vec<String> = callee_deps.values().flatten().cloned().collect();
    let mut seen: BTreeSet<String> = callee_deps.keys().cloned().collect();
    seen.insert(caller_cert.function.clone());
    while let Some(func) = frontier.pop() {
        if seen.contains(&func) {
            continue;
        }
        seen.insert(func.clone());
        if let Some(deps) = call_graph.get(&func) {
            callee_deps.insert(func, deps.clone());
            frontier.extend(deps.iter().cloned());
        }
    }
    modular_composition_with_deps(caller_cert, callee_certs, required_callees, &callee_deps)
}

/// Compose a caller's certificate with its callees' certificates,
/// using a callee dependency graph for full DFS-based cycle detection.
///
/// `callee_deps` maps each callee function name to its own required callees.
/// This enables detection of transitive cycles (e.g., A -> B -> C -> A)
/// that cannot be caught from the caller's perspective alone.
pub fn modular_composition_with_deps(
    caller_cert: &ProofCertificate,
    callee_certs: &[&ProofCertificate],
    required_callees: &[String],
    callee_deps: &BTreeMap<String, Vec<String>>,
) -> Result<ComposedProof, CompositionError> {
    // Check that all required callees have certificates
    let proved_functions: BTreeSet<&str> =
        callee_certs.iter().map(|c| c.function.as_str()).collect();

    for callee in required_callees {
        if !proved_functions.contains(callee.as_str()) {
            return Err(CompositionError::MissingLink { function: callee.clone() });
        }
    }

    // Full DFS-based cycle detection over the dependency graph.
    // Build adjacency list: caller -> required_callees, plus any
    // callee -> callee edges from callee_deps.
    {
        let mut adj: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
        adj.insert(
            caller_cert.function.as_str(),
            required_callees.iter().map(|s| s.as_str()).collect(),
        );
        for (callee_fn, deps) in callee_deps {
            let entry = adj.entry(callee_fn.as_str()).or_default();
            for dep in deps {
                entry.push(dep.as_str());
            }
        }

        // DFS with coloring: White=0, Gray=1, Black=2.
        // A back-edge to a Gray node indicates a cycle.
        let mut color: BTreeMap<&str, u8> = BTreeMap::new();
        for key in adj.keys() {
            color.insert(*key, 0);
        }
        // Also add nodes that appear only as targets (not sources).
        for targets in adj.values() {
            for &t in targets {
                color.entry(t).or_insert(0);
            }
        }

        fn dfs_find_cycle<'a>(
            node: &'a str,
            adj: &BTreeMap<&'a str, Vec<&'a str>>,
            color: &mut BTreeMap<&'a str, u8>,
            path: &mut Vec<&'a str>,
        ) -> Option<Vec<String>> {
            color.insert(node, 1); // Gray
            path.push(node);

            if let Some(neighbors) = adj.get(node) {
                for &neighbor in neighbors {
                    match color.get(neighbor) {
                        Some(1) => {
                            // Back-edge to Gray node: cycle found.
                            let start = path.iter().position(|&p| p == neighbor).unwrap_or(0);
                            let mut cycle: Vec<String> =
                                path[start..].iter().map(|s| s.to_string()).collect();
                            cycle.push(neighbor.to_string());
                            return Some(cycle);
                        }
                        Some(0) | None => {
                            if color.get(neighbor).copied().unwrap_or(0) == 0
                                && let Some(cycle) = dfs_find_cycle(neighbor, adj, color, path)
                            {
                                return Some(cycle);
                            }
                        }
                        _ => {} // Black, already fully processed
                    }
                }
            }

            color.insert(node, 2); // Black
            path.pop();
            None
        }

        let mut path = Vec::new();
        for &node in color.clone().keys() {
            if color[node] == 0
                && let Some(cycle) = dfs_find_cycle(node, &adj, &mut color, &mut path)
            {
                return Err(CompositionError::CircularDependency { cycle: cycle.join(" -> ") });
            }
        }
    }

    // Build the composed proof
    let mut all_certs: Vec<&ProofCertificate> = vec![caller_cert];
    all_certs.extend(callee_certs.iter());

    let constituent_ids: Vec<String> = all_certs.iter().map(|c| c.id.0.clone()).collect();

    let mut functions: Vec<String> = all_certs.iter().map(|c| c.function.clone()).collect();
    functions.sort();
    functions.dedup();

    let combined_strength = weakest_strength(all_certs.iter().map(|c| &c.solver));
    let combined_status = if all_certs.iter().all(|c| c.status == CertificationStatus::Certified) {
        CertificationStatus::Certified
    } else {
        CertificationStatus::Trusted
    };

    let total_time_ms: u64 = all_certs.iter().map(|c| c.solver.time_ms).sum();

    // Build call edges
    let call_edges: Vec<(String, String)> =
        callee_certs.iter().map(|c| (caller_cert.function.clone(), c.function.clone())).collect();
    let function_strengths: Vec<FunctionStrength> = all_certs
        .iter()
        .map(|c| FunctionStrength {
            function: c.function.clone(),
            strength: c.solver.strength.clone(),
            status: c.status,
        })
        .collect();

    Ok(ComposedProof {
        constituent_ids,
        functions,
        combined_strength,
        combined_status,
        total_time_ms,
        is_consistent: true,
        call_edges,
        function_strengths,
    })
}
