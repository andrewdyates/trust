// trust-proof-cert DAG-based composition pipeline
//
// ProofComposition DAG, IncrementalComposition with change tracking,
// and composition verification.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::{FxHashMap, FxHashSet};

use serde::{Deserialize, Serialize};

use crate::ProofCertificate;

use super::checkers::compose_proofs;
use super::types::{
    ChangeKind, ComposedProof, CompositionError, CompositionNodeStatus, FunctionStrength,
};

/// A node in the proof composition DAG.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompositionNode {
    /// Function name this node represents.
    pub function: String,
    /// Certificate ID (if present).
    pub cert_id: Option<String>,
    /// Functions this node depends on (callees).
    pub dependencies: Vec<String>,
    /// Current status.
    pub status: CompositionNodeStatus,
}

/// Manages a directed acyclic graph of proof certificates for modular
/// whole-program composition.
///
/// Each node represents a function with its certificate. Edges represent
/// call dependencies (caller -> callee). The composition is sound when
/// every reachable node has a valid certificate and the DAG is acyclic.
#[derive(Debug, Clone)]
pub struct ProofComposition {
    /// Nodes indexed by function name.
    pub(crate) nodes: FxHashMap<String, CompositionNode>,
    /// Certificates indexed by function name.
    certificates: FxHashMap<String, ProofCertificate>,
}

impl ProofComposition {
    /// Create a new empty composition.
    pub fn new() -> Self {
        ProofComposition {
            nodes: FxHashMap::default(),
            certificates: FxHashMap::default(),
        }
    }

    /// Add a certificate for a function with its call dependencies.
    pub fn add_certificate(
        &mut self,
        cert: ProofCertificate,
        dependencies: Vec<String>,
    ) {
        let function = cert.function.clone();
        let cert_id = cert.id.0.clone();
        let status = if cert.chain.verify_integrity().is_ok() {
            CompositionNodeStatus::Valid
        } else {
            CompositionNodeStatus::ChainBroken
        };
        self.nodes.insert(
            function.clone(),
            CompositionNode {
                function: function.clone(),
                cert_id: Some(cert_id),
                dependencies,
                status,
            },
        );
        self.certificates.insert(function, cert);
    }

    /// Mark a function as required but without a certificate yet.
    pub fn add_missing(&mut self, function: &str, dependencies: Vec<String>) {
        self.nodes.insert(
            function.to_string(),
            CompositionNode {
                function: function.to_string(),
                cert_id: None,
                dependencies,
                status: CompositionNodeStatus::Missing,
            },
        );
    }

    /// Get a node by function name.
    pub fn get_node(&self, function: &str) -> Option<&CompositionNode> {
        self.nodes.get(function)
    }

    /// Get a certificate by function name.
    pub fn get_certificate(&self, function: &str) -> Option<&ProofCertificate> {
        self.certificates.get(function)
    }

    /// Return all function names in the composition.
    pub fn functions(&self) -> Vec<String> {
        let mut names: Vec<String> = self.nodes.keys().cloned().collect();
        names.sort();
        names
    }

    /// Return the number of nodes.
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Return true if the composition has no nodes.
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    /// Return the set of functions that have missing certificates.
    pub fn missing_functions(&self) -> Vec<String> {
        self.nodes
            .values()
            .filter(|n| n.status == CompositionNodeStatus::Missing)
            .map(|n| n.function.clone())
            .collect()
    }

    /// Detect cycles in the dependency DAG using DFS.
    ///
    /// Returns `None` if the DAG is acyclic, or `Some(cycle)` with the
    /// list of function names forming a cycle.
    pub fn detect_cycle(&self) -> Option<Vec<String>> {
        // Standard DFS cycle detection with coloring
        // White=0, Gray=1, Black=2
        let mut color: FxHashMap<&str, u8> = FxHashMap::default();
        for key in self.nodes.keys() {
            color.insert(key.as_str(), 0);
        }

        let mut path: Vec<String> = Vec::new();

        for key in self.nodes.keys() {
            if color[key.as_str()] == 0
                && let Some(cycle) = self.dfs_cycle(key, &mut color, &mut path)
            {

                    return Some(cycle);

            }
        }
        None
    }

    /// DFS helper for cycle detection.
    fn dfs_cycle<'a>(
        &'a self,
        node: &'a str,
        color: &mut FxHashMap<&'a str, u8>,
        path: &mut Vec<String>,
    ) -> Option<Vec<String>> {
        color.insert(node, 1); // Gray
        path.push(node.to_string());

        if let Some(n) = self.nodes.get(node) {
            for dep in &n.dependencies {
                match color.get(dep.as_str()) {
                    Some(1) => {
                        // Found a back edge -> cycle
                        let start = path.iter().position(|p| p == dep).unwrap_or(0);
                        let mut cycle: Vec<String> = path[start..].to_vec();
                        cycle.push(dep.clone());
                        return Some(cycle);
                    }
                    Some(0) | None => {
                        if let Some(cycle) = self.dfs_cycle(dep, color, path) {
                            return Some(cycle);
                        }
                    }
                    _ => {} // Black, already processed
                }
            }
        }

        color.insert(node, 2); // Black
        path.pop();
        None
    }

    /// Return nodes in topological order (dependencies before dependents).
    /// Returns `Err` if the graph contains a cycle.
    pub fn topological_order(&self) -> Result<Vec<String>, CompositionError> {
        if let Some(cycle) = self.detect_cycle() {
            return Err(CompositionError::CircularDependency {
                cycle: cycle.join(" -> "),
            });
        }

        let mut in_degree: FxHashMap<&str, usize> = FxHashMap::default();
        // Count in-degrees: number of within-DAG dependencies each node has
        for node in self.nodes.values() {
            let count = node
                .dependencies
                .iter()
                .filter(|d| self.nodes.contains_key(d.as_str()))
                .count();
            in_degree.insert(node.function.as_str(), count);
        }

        let mut queue: Vec<String> = in_degree
            .iter()
            .filter(|(_, deg)| **deg == 0)
            .map(|(&name, _)| name.to_string())
            .collect();
        queue.sort(); // deterministic ordering

        let mut result = Vec::new();
        while let Some(func) = queue.pop() {
            result.push(func.clone());
            // For each node that depends on `func`, decrement its in-degree
            for node in self.nodes.values() {
                if node.dependencies.contains(&func)
                    && let Some(deg) = in_degree.get_mut(node.function.as_str()) {
                        *deg = deg.saturating_sub(1);
                        if *deg == 0 {
                            queue.push(node.function.clone());
                            queue.sort();
                        }
                    }
            }
        }

        Ok(result)
    }
}

impl Default for ProofComposition {
    fn default() -> Self {
        Self::new()
    }
}

/// Incremental proof composition with change tracking.
///
/// Wraps [ProofComposition] and tracks spec/body hashes for each function
/// to enable precise invalidation when functions change. Fail-closed:
/// invalidated functions are stale until explicitly re-verified.
#[derive(Debug, Clone)]
pub struct IncrementalComposition {
    /// The underlying proof composition DAG.
    dag: ProofComposition,
    /// SHA-256 hash of each function's spec (annotations + signature).
    spec_hashes: FxHashMap<String, [u8; 32]>,
    /// SHA-256 hash of each function's MIR body.
    body_hashes: FxHashMap<String, [u8; 32]>,
    /// Functions currently marked as stale (need re-verification).
    stale: FxHashSet<String>,
}

impl IncrementalComposition {
    /// Create a new incremental composition.
    pub fn new() -> Self {
        IncrementalComposition {
            dag: ProofComposition::new(),
            spec_hashes: FxHashMap::default(),
            body_hashes: FxHashMap::default(),
            stale: FxHashSet::default(),
        }
    }

    /// Add a certificate with its hashes and dependencies.
    pub fn add_certificate(
        &mut self,
        cert: ProofCertificate,
        dependencies: Vec<String>,
        spec_hash: [u8; 32],
        body_hash: [u8; 32],
    ) {
        let function = cert.function.clone();
        self.dag.add_certificate(cert, dependencies);
        self.spec_hashes.insert(function.clone(), spec_hash);
        self.body_hashes.insert(function, body_hash);
    }

    /// Compute the set of functions needing re-verification after a change.
    ///
    /// For [`ChangeKind::BodyOnly`]: only the changed function itself.
    /// For [`ChangeKind::SpecChanged`]: the changed function plus all transitive callers.
    ///
    /// All returned functions are marked stale (fail-closed).
    pub fn invalidated_by(&mut self, changed_fn: &str, change_kind: ChangeKind) -> Vec<String> {
        let mut invalidated = vec![changed_fn.to_string()];
        self.stale.insert(changed_fn.to_string());

        if change_kind == ChangeKind::SpecChanged {
            // BFS to find all transitive callers.
            let mut queue: std::collections::VecDeque<String> = std::collections::VecDeque::new();
            queue.push_back(changed_fn.to_string());
            let mut visited: FxHashSet<String> = FxHashSet::default();
            visited.insert(changed_fn.to_string());

            while let Some(current) = queue.pop_front() {
                // Find all functions that depend on (call) current.
                for func in self.dag.functions() {
                    if let Some(node) = self.dag.get_node(&func)
                        && node.dependencies.contains(&current) && visited.insert(func.clone()) {
                            invalidated.push(func.clone());
                            self.stale.insert(func.clone());
                            queue.push_back(func);
                        }
                }
            }
        }

        invalidated.sort();
        invalidated
    }

    /// Update a single function's certificate after successful re-verification.
    ///
    /// Removes the function from the stale set and updates hashes.
    pub fn update_certificate(
        &mut self,
        cert: ProofCertificate,
        dependencies: Vec<String>,
        new_spec_hash: [u8; 32],
        new_body_hash: [u8; 32],
    ) {
        let function = cert.function.clone();
        self.dag.add_certificate(cert, dependencies);
        self.spec_hashes.insert(function.clone(), new_spec_hash);
        self.body_hashes.insert(function.clone(), new_body_hash);
        self.stale.remove(&function);
    }

    /// Return the set of functions currently marked as stale.
    pub fn stale_functions(&self) -> Vec<String> {
        let mut stale: Vec<String> = self.stale.iter().cloned().collect();
        stale.sort();
        stale
    }

    /// Check if a function is currently stale.
    pub fn is_stale(&self, function: &str) -> bool {
        self.stale.contains(function)
    }

    /// Get the underlying DAG.
    pub fn dag(&self) -> &ProofComposition {
        &self.dag
    }

    /// Get the spec hash for a function.
    pub fn spec_hash(&self, function: &str) -> Option<&[u8; 32]> {
        self.spec_hashes.get(function)
    }

    /// Get the body hash for a function.
    pub fn body_hash(&self, function: &str) -> Option<&[u8; 32]> {
        self.body_hashes.get(function)
    }

    /// Build per-function strengths from the current DAG state.
    pub fn function_strengths(&self) -> Vec<FunctionStrength> {
        let mut strengths = Vec::new();
        for func in self.dag.functions() {
            if let Some(cert) = self.dag.get_certificate(&func) {
                strengths.push(FunctionStrength {
                    function: func,
                    strength: cert.solver.strength.clone(),
                    status: cert.status,
                });
            }
        }
        strengths
    }
}

impl Default for IncrementalComposition {
    fn default() -> Self {
        Self::new()
    }
}

/// Result of verifying a proof composition.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompositionVerification {
    /// Whether the entire composition is sound.
    pub sound: bool,
    /// Functions with valid certificates.
    pub valid_functions: Vec<String>,
    /// Functions with missing certificates.
    pub missing_functions: Vec<String>,
    /// Functions with broken chains.
    pub broken_chains: Vec<String>,
    /// Cycle detected (if any).
    pub cycle: Option<Vec<String>>,
    /// The composed proof (if composition is sound).
    pub composed: Option<ComposedProof>,
}

/// Verify that a proof composition is sound.
///
/// A composition is sound when:
/// 1. The dependency DAG is acyclic
/// 2. Every node has a valid certificate (no missing, no broken chains)
/// 3. All pairwise composability checks pass
/// 4. The transitive closure covers all dependencies
pub fn verify_composition(composition: &ProofComposition) -> CompositionVerification {
    let mut valid_functions = Vec::new();
    let mut missing_functions = Vec::new();
    let mut broken_chains = Vec::new();

    for node in composition.nodes.values() {
        match node.status {
            CompositionNodeStatus::Valid => valid_functions.push(node.function.clone()),
            CompositionNodeStatus::Missing => missing_functions.push(node.function.clone()),
            CompositionNodeStatus::ChainBroken => broken_chains.push(node.function.clone()),
            CompositionNodeStatus::Stale => broken_chains.push(node.function.clone()),
        }
    }

    valid_functions.sort();
    missing_functions.sort();
    broken_chains.sort();

    // Check for cycles
    let cycle = composition.detect_cycle();

    // Composition is sound if no missing, no broken, no cycles
    let sound = missing_functions.is_empty() && broken_chains.is_empty() && cycle.is_none();

    // Build composed proof if sound
    let composed = if sound && !valid_functions.is_empty() {
        let certs: Vec<&ProofCertificate> = valid_functions
            .iter()
            .filter_map(|f| composition.get_certificate(f))
            .collect();
        compose_proofs(&certs).ok()
    } else {
        None
    };

    CompositionVerification {
        sound,
        valid_functions,
        missing_functions,
        broken_chains,
        cycle,
        composed,
    }
}
