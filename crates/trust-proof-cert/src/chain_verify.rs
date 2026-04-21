// trust-proof-cert/chain_verify.rs: Proof chain verification (#353)
//
// Verification of proof certificate chains ensuring dependent proofs
// maintain consistency. Checks dependency completeness, verdict consistency,
// cycle freedom, and orphan detection.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::VecDeque;
use trust_types::fx::{FxHashMap, FxHashSet};

use thiserror::Error;

// ---------------------------------------------------------------------------
// Error type
// ---------------------------------------------------------------------------

/// Errors detected during chain verification.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
#[non_exhaustive]
pub(crate) enum ChainError {
    #[error("certificate `{cert_id}` depends on missing certificate `{missing}`")]
    MissingDependency { cert_id: String, missing: String },

    #[error(
        "certificate `{cert_id}` has inconsistent verdict: expected `{expected}`, found `{found}`"
    )]
    InconsistentVerdict { cert_id: String, expected: String, found: String },

    #[error("cycle detected in proof chain: {0:?}")]
    CycleDetected(Vec<String>),

    #[error("orphan link with no dependents or dependencies: `{0}`")]
    OrphanLink(String),
}

// ---------------------------------------------------------------------------
// Data types
// ---------------------------------------------------------------------------

/// A single link in a proof chain representing one function's proof certificate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ChainLink {
    /// Unique certificate identifier.
    pub cert_id: String,
    /// Name of the function this certificate proves.
    pub function_name: String,
    /// Certificate IDs this link depends on (callees whose contracts are assumed).
    pub depends_on: Vec<String>,
    /// Verdict of this certificate (e.g., "proven", "unproven", "timeout").
    pub verdict: String,
}

/// A chain of proof certificates with a designated root.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ProofChain {
    /// All links in the chain.
    pub links: Vec<ChainLink>,
    /// The root certificate ID (entry point of the proof chain).
    pub root_cert: String,
}

/// Result of verifying a proof chain.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ChainVerifyResult {
    /// Whether the entire chain is valid.
    pub is_valid: bool,
    /// Number of links that were successfully verified.
    pub verified_links: usize,
    /// Certificate IDs of links that failed verification.
    pub broken_links: Vec<String>,
    /// Detailed errors found during verification.
    pub errors: Vec<ChainError>,
}

/// Configuration for chain verification behavior.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct ChainConfig {
    /// In strict mode, any error makes the chain invalid.
    /// In non-strict mode, partial chains may still be considered valid.
    pub strict_mode: bool,
    /// Maximum allowed chain depth (prevents runaway recursion).
    pub max_chain_depth: usize,
    /// Whether to allow partial chains (chains with missing dependencies).
    pub allow_partial: bool,
    /// Minimum fraction of links that must verify for partial mode (0.0 to 1.0).
    /// Default is 0.5 (at least half must verify).
    pub min_verified_ratio: f64,
}

impl Default for ChainConfig {
    fn default() -> Self {
        Self {
            strict_mode: true,
            max_chain_depth: 256,
            allow_partial: false,
            min_verified_ratio: 0.5,
        }
    }
}

// ---------------------------------------------------------------------------
// ChainVerifier
// ---------------------------------------------------------------------------

/// Verifies proof certificate chains for consistency and completeness.
pub(crate) struct ChainVerifier {
    config: ChainConfig,
}

impl ChainVerifier {
    /// Create a new verifier with the given configuration.
    #[must_use]
    pub fn new(config: ChainConfig) -> Self {
        Self { config }
    }

    /// Verify an entire proof chain for consistency, completeness, and acyclicity.
    #[must_use]
    pub fn verify_chain(&self, chain: &ProofChain) -> ChainVerifyResult {
        let mut errors = Vec::new();
        let mut broken = FxHashSet::default();

        let id_set: FxHashSet<&str> = chain.links.iter().map(|l| l.cert_id.as_str()).collect();

        // 1. Check each link for missing dependencies and consistency.
        for link in &chain.links {
            if let Err(e) = self.check_link_consistency(link, chain) {
                broken.insert(link.cert_id.clone());
                errors.push(e);
            }
        }

        // 2. Detect cycles.
        if let Some(cycle) = self.detect_cycle(chain) {
            for id in &cycle {
                broken.insert(id.clone());
            }
            errors.push(ChainError::CycleDetected(cycle));
        }

        // 3. Detect orphans (links that are not root, have no dependents,
        //    and have no dependencies).
        if self.config.strict_mode {
            let depended_upon: FxHashSet<&str> =
                chain.links.iter().flat_map(|l| l.depends_on.iter().map(String::as_str)).collect();

            for link in &chain.links {
                if link.cert_id != chain.root_cert
                    && link.depends_on.is_empty()
                    && !depended_upon.contains(link.cert_id.as_str())
                {
                    broken.insert(link.cert_id.clone());
                    errors.push(ChainError::OrphanLink(link.cert_id.clone()));
                }
            }
        }

        // 4. Check max depth.
        let depth = self.chain_depth(chain);
        if depth > self.config.max_chain_depth {
            // Depth exceeded is treated as broken root.
            broken.insert(chain.root_cert.clone());
        }

        let broken_links: Vec<String> = {
            let mut v: Vec<String> = broken.into_iter().collect();
            v.sort();
            v
        };

        let verified_links = chain.links.len().saturating_sub(broken_links.len());
        let is_valid = if self.config.strict_mode {
            errors.is_empty() && id_set.contains(chain.root_cert.as_str())
        } else if self.config.allow_partial {
            let ratio = if chain.links.is_empty() {
                0.0
            } else {
                verified_links as f64 / chain.links.len() as f64
            };
            ratio >= self.config.min_verified_ratio
        } else {
            broken_links.is_empty() && id_set.contains(chain.root_cert.as_str())
        };

        ChainVerifyResult { is_valid, verified_links, broken_links, errors }
    }

    /// Check a single link for consistency against the chain.
    ///
    /// Verifies that all dependencies exist and that dependency verdicts
    /// are "proven" (non-proven dependencies make the link inconsistent
    /// in strict mode).
    pub fn check_link_consistency(
        &self,
        link: &ChainLink,
        chain: &ProofChain,
    ) -> Result<(), ChainError> {
        let id_map: FxHashMap<&str, &ChainLink> =
            chain.links.iter().map(|l| (l.cert_id.as_str(), l)).collect();

        for dep_id in &link.depends_on {
            match id_map.get(dep_id.as_str()) {
                None => {
                    return Err(ChainError::MissingDependency {
                        cert_id: link.cert_id.clone(),
                        missing: dep_id.clone(),
                    });
                }
                Some(dep_link) => {
                    if self.config.strict_mode && dep_link.verdict != "proven" {
                        return Err(ChainError::InconsistentVerdict {
                            cert_id: link.cert_id.clone(),
                            expected: "proven".to_string(),
                            found: dep_link.verdict.clone(),
                        });
                    }
                }
            }
        }

        Ok(())
    }

    /// Find all broken link IDs in the chain (links with errors).
    #[must_use]
    pub fn find_broken_links(&self, chain: &ProofChain) -> Vec<String> {
        let mut broken = Vec::new();
        for link in &chain.links {
            if self.check_link_consistency(link, chain).is_err() {
                broken.push(link.cert_id.clone());
            }
        }
        broken.sort();
        broken
    }

    /// Compute the maximum depth of the dependency chain starting from the root.
    ///
    /// Returns 0 for an empty chain, 1 for a single root with no dependencies.
    #[must_use]
    pub fn chain_depth(&self, chain: &ProofChain) -> usize {
        if chain.links.is_empty() {
            return 0;
        }

        let id_map: FxHashMap<&str, &ChainLink> =
            chain.links.iter().map(|l| (l.cert_id.as_str(), l)).collect();

        // BFS from root, tracking depth.
        let mut visited = FxHashSet::default();
        let mut queue = VecDeque::new();
        queue.push_back((chain.root_cert.as_str(), 1usize));
        visited.insert(chain.root_cert.as_str());
        let mut max_depth = 0;

        while let Some((current, depth)) = queue.pop_front() {
            max_depth = max_depth.max(depth);

            if let Some(link) = id_map.get(current) {
                for dep in &link.depends_on {
                    if visited.insert(dep.as_str()) {
                        queue.push_back((dep.as_str(), depth + 1));
                    }
                }
            }
        }

        max_depth
    }

    /// Compute a topological ordering of the chain links.
    ///
    /// Returns `None` if the chain contains a cycle.
    #[must_use]
    pub fn topological_order(&self, chain: &ProofChain) -> Option<Vec<String>> {
        let id_map: FxHashMap<&str, &ChainLink> =
            chain.links.iter().map(|l| (l.cert_id.as_str(), l)).collect();

        // Compute in-degree for each node present in the chain.
        let mut in_degree: FxHashMap<&str, usize> = FxHashMap::default();
        for link in &chain.links {
            in_degree.entry(link.cert_id.as_str()).or_insert(0);
            for dep in &link.depends_on {
                if id_map.contains_key(dep.as_str()) {
                    *in_degree.entry(dep.as_str()).or_insert(0) += 1;
                }
            }
        }

        // Note: in this dependency graph, edges go from dependent -> dependency.
        // "In-degree" here counts how many other nodes depend on this node.
        // Nodes with in-degree 0 are leaves (depended on by nobody else).
        // We want the reverse: topological order where dependencies come first.
        //
        // Recompute using standard Kahn's on reverse edges:
        // edge from A -> B means "A depends on B", so B must come before A.
        let mut reverse_in_degree: FxHashMap<&str, usize> = FxHashMap::default();
        for link in &chain.links {
            reverse_in_degree.entry(link.cert_id.as_str()).or_insert(0);
        }
        for link in &chain.links {
            for dep in &link.depends_on {
                if id_map.contains_key(dep.as_str()) {
                    *reverse_in_degree.entry(link.cert_id.as_str()).or_insert(0) += 1;
                }
            }
        }

        let mut queue: VecDeque<&str> =
            reverse_in_degree.iter().filter(|(_, deg)| **deg == 0).map(|(id, _)| *id).collect();

        // Sort for deterministic output.
        let mut sorted_queue: Vec<&str> = queue.drain(..).collect();
        sorted_queue.sort();
        for item in sorted_queue {
            queue.push_back(item);
        }

        let mut order = Vec::new();

        while let Some(node) = queue.pop_front() {
            order.push(node.to_string());

            // Find all nodes that depend on `node` and decrement their
            // reverse in-degree.
            let mut next_candidates = Vec::new();
            for link in &chain.links {
                if link.depends_on.iter().any(|d| d.as_str() == node)
                    && let Some(deg) = reverse_in_degree.get_mut(link.cert_id.as_str())
                {
                    *deg = deg.saturating_sub(1);
                    if *deg == 0 {
                        next_candidates.push(link.cert_id.as_str());
                    }
                }
            }
            next_candidates.sort();
            for c in next_candidates {
                queue.push_back(c);
            }
        }

        if order.len() == chain.links.len() {
            Some(order)
        } else {
            None // Cycle detected
        }
    }

    /// Find root certificates (links that no other link depends on).
    #[must_use]
    pub fn find_roots(&self, chain: &ProofChain) -> Vec<String> {
        let depended_upon: FxHashSet<&str> =
            chain.links.iter().flat_map(|l| l.depends_on.iter().map(String::as_str)).collect();

        let mut roots: Vec<String> = chain
            .links
            .iter()
            .filter(|l| !depended_upon.contains(l.cert_id.as_str()))
            .map(|l| l.cert_id.clone())
            .collect();

        roots.sort();
        roots
    }

    // -----------------------------------------------------------------------
    // Internal helpers
    // -----------------------------------------------------------------------

    /// Detect a cycle using DFS coloring.
    fn detect_cycle(&self, chain: &ProofChain) -> Option<Vec<String>> {
        let id_map: FxHashMap<&str, &ChainLink> =
            chain.links.iter().map(|l| (l.cert_id.as_str(), l)).collect();

        // 0 = white (unvisited), 1 = gray (in stack), 2 = black (done)
        let mut color: FxHashMap<&str, u8> = FxHashMap::default();
        let mut parent: FxHashMap<&str, &str> = FxHashMap::default();

        for link in &chain.links {
            color.insert(link.cert_id.as_str(), 0);
        }

        for link in &chain.links {
            if color[link.cert_id.as_str()] == 0
                && let Some(cycle) =
                    self.dfs_cycle(link.cert_id.as_str(), &id_map, &mut color, &mut parent)
            {
                return Some(cycle);
            }
        }

        None
    }

    fn dfs_cycle<'a>(
        &self,
        node: &'a str,
        id_map: &FxHashMap<&'a str, &'a ChainLink>,
        color: &mut FxHashMap<&'a str, u8>,
        parent: &mut FxHashMap<&'a str, &'a str>,
    ) -> Option<Vec<String>> {
        color.insert(node, 1); // gray

        if let Some(link) = id_map.get(node) {
            for dep in &link.depends_on {
                let dep_str = dep.as_str();
                if !color.contains_key(dep_str) {
                    // Dependency not in chain — skip (handled by missing dep check).
                    continue;
                }
                match color[dep_str] {
                    0 => {
                        parent.insert(dep_str, node);
                        if let Some(cycle) = self.dfs_cycle(dep_str, id_map, color, parent) {
                            return Some(cycle);
                        }
                    }
                    1 => {
                        // Back edge — cycle found. Reconstruct.
                        let mut cycle = vec![dep.clone()];
                        let mut cur = node;
                        while cur != dep_str {
                            cycle.push(cur.to_string());
                            cur = match parent.get(cur) {
                                Some(p) => p,
                                None => break,
                            };
                        }
                        cycle.push(dep.clone());
                        cycle.reverse();
                        return Some(cycle);
                    }
                    _ => {} // black — already processed, no cycle through here
                }
            }
        }

        color.insert(node, 2); // black
        None
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn make_link(id: &str, function: &str, deps: &[&str], verdict: &str) -> ChainLink {
        ChainLink {
            cert_id: id.to_string(),
            function_name: function.to_string(),
            depends_on: deps.iter().map(|s| s.to_string()).collect(),
            verdict: verdict.to_string(),
        }
    }

    fn simple_chain() -> ProofChain {
        // root -> mid -> leaf
        ProofChain {
            links: vec![
                make_link("root", "main", &["mid"], "proven"),
                make_link("mid", "helper", &["leaf"], "proven"),
                make_link("leaf", "utility", &[], "proven"),
            ],
            root_cert: "root".to_string(),
        }
    }

    fn default_verifier() -> ChainVerifier {
        ChainVerifier::new(ChainConfig::default())
    }

    // -----------------------------------------------------------------------
    // Basic valid chain
    // -----------------------------------------------------------------------

    #[test]
    fn test_verify_chain_valid_simple() {
        let verifier = default_verifier();
        let chain = simple_chain();
        let result = verifier.verify_chain(&chain);

        assert!(result.is_valid, "simple chain should be valid: {:?}", result.errors);
        assert_eq!(result.verified_links, 3);
        assert!(result.broken_links.is_empty());
        assert!(result.errors.is_empty());
    }

    #[test]
    fn test_verify_chain_single_root() {
        let verifier = default_verifier();
        let chain = ProofChain {
            links: vec![make_link("only", "main", &[], "proven")],
            root_cert: "only".to_string(),
        };
        let result = verifier.verify_chain(&chain);

        assert!(result.is_valid);
        assert_eq!(result.verified_links, 1);
    }

    // -----------------------------------------------------------------------
    // Missing dependency
    // -----------------------------------------------------------------------

    #[test]
    fn test_verify_chain_missing_dependency() {
        let verifier = default_verifier();
        let chain = ProofChain {
            links: vec![make_link("root", "main", &["missing_dep"], "proven")],
            root_cert: "root".to_string(),
        };
        let result = verifier.verify_chain(&chain);

        assert!(!result.is_valid);
        assert!(result.broken_links.contains(&"root".to_string()));
        assert!(result.errors.iter().any(|e| matches!(
            e,
            ChainError::MissingDependency { cert_id, missing }
            if cert_id == "root" && missing == "missing_dep"
        )));
    }

    #[test]
    fn test_verify_chain_allow_partial_missing_dep() {
        let verifier = ChainVerifier::new(ChainConfig {
            strict_mode: false,
            max_chain_depth: 256,
            allow_partial: true,
            min_verified_ratio: 0.5,
        });
        let chain = ProofChain {
            links: vec![make_link("root", "main", &["missing_dep"], "proven")],
            root_cert: "root".to_string(),
        };
        let result = verifier.verify_chain(&chain);

        assert!(!result.is_valid);
        assert_eq!(result.verified_links, 0);
        assert!(result.broken_links.contains(&"root".to_string()));
    }

    #[test]
    fn test_verify_chain_allow_partial_mostly_broken_fails() {
        let verifier = ChainVerifier::new(ChainConfig {
            strict_mode: false,
            max_chain_depth: 256,
            allow_partial: true,
            min_verified_ratio: 0.5,
        });
        // 10 links, 9 depend on missing certs, only 1 has no deps
        let mut links = vec![make_link("good", "fn_good", &[], "proven")];
        for i in 0..9 {
            links.push(make_link(
                &format!("bad{i}"),
                &format!("fn_bad{i}"),
                &["nonexistent"],
                "proven",
            ));
        }
        let chain = ProofChain { links, root_cert: "good".to_string() };
        let result = verifier.verify_chain(&chain);

        // Only 1/10 = 0.1 verified, below 0.5 threshold
        assert!(!result.is_valid, "mostly-broken chain should fail with min_verified_ratio=0.5");
        assert_eq!(result.verified_links, 1);
    }

    // -----------------------------------------------------------------------
    // Inconsistent verdict
    // -----------------------------------------------------------------------

    #[test]
    fn test_verify_chain_inconsistent_verdict() {
        let verifier = default_verifier();
        let chain = ProofChain {
            links: vec![
                make_link("root", "main", &["dep"], "proven"),
                make_link("dep", "helper", &[], "timeout"),
            ],
            root_cert: "root".to_string(),
        };
        let result = verifier.verify_chain(&chain);

        assert!(!result.is_valid);
        assert!(result.errors.iter().any(|e| matches!(
            e,
            ChainError::InconsistentVerdict { cert_id, expected, found }
            if cert_id == "root" && expected == "proven" && found == "timeout"
        )));
    }

    #[test]
    fn test_verify_chain_non_strict_allows_unproven_deps() {
        let verifier = ChainVerifier::new(ChainConfig {
            strict_mode: false,
            max_chain_depth: 256,
            allow_partial: false,
            min_verified_ratio: 0.5,
        });
        let chain = ProofChain {
            links: vec![
                make_link("root", "main", &["dep"], "proven"),
                make_link("dep", "helper", &[], "timeout"),
            ],
            root_cert: "root".to_string(),
        };
        let result = verifier.verify_chain(&chain);

        assert!(result.is_valid);
        assert_eq!(result.verified_links, 2);
    }

    // -----------------------------------------------------------------------
    // Cycle detection
    // -----------------------------------------------------------------------

    #[test]
    fn test_verify_chain_cycle_detected() {
        let verifier = default_verifier();
        let chain = ProofChain {
            links: vec![
                make_link("a", "fn_a", &["b"], "proven"),
                make_link("b", "fn_b", &["a"], "proven"),
            ],
            root_cert: "a".to_string(),
        };
        let result = verifier.verify_chain(&chain);

        assert!(!result.is_valid);
        assert!(result.errors.iter().any(|e| matches!(e, ChainError::CycleDetected(_))));
    }

    #[test]
    fn test_verify_chain_three_node_cycle() {
        let verifier = default_verifier();
        let chain = ProofChain {
            links: vec![
                make_link("a", "fn_a", &["b"], "proven"),
                make_link("b", "fn_b", &["c"], "proven"),
                make_link("c", "fn_c", &["a"], "proven"),
            ],
            root_cert: "a".to_string(),
        };
        let result = verifier.verify_chain(&chain);

        assert!(!result.is_valid);
        assert!(result.errors.iter().any(|e| matches!(e, ChainError::CycleDetected(_))));
    }

    // -----------------------------------------------------------------------
    // Orphan detection
    // -----------------------------------------------------------------------

    #[test]
    fn test_verify_chain_orphan_link() {
        let verifier = default_verifier();
        let chain = ProofChain {
            links: vec![
                make_link("root", "main", &[], "proven"),
                make_link("orphan", "stray", &[], "proven"),
            ],
            root_cert: "root".to_string(),
        };
        let result = verifier.verify_chain(&chain);

        assert!(!result.is_valid);
        assert!(result.errors.iter().any(|e| matches!(
            e,
            ChainError::OrphanLink(id) if id == "orphan"
        )));
    }

    // -----------------------------------------------------------------------
    // check_link_consistency
    // -----------------------------------------------------------------------

    #[test]
    fn test_check_link_consistency_ok() {
        let verifier = default_verifier();
        let chain = simple_chain();
        let root = &chain.links[0];
        let result = verifier.check_link_consistency(root, &chain);

        assert!(result.is_ok());
    }

    #[test]
    fn test_check_link_consistency_missing_dep() {
        let verifier = default_verifier();
        let chain = ProofChain {
            links: vec![make_link("a", "fn_a", &["nonexistent"], "proven")],
            root_cert: "a".to_string(),
        };
        let link = &chain.links[0];
        let result = verifier.check_link_consistency(link, &chain);

        assert!(result.is_err());
        assert!(matches!(result.unwrap_err(), ChainError::MissingDependency { .. }));
    }

    // -----------------------------------------------------------------------
    // find_broken_links
    // -----------------------------------------------------------------------

    #[test]
    fn test_find_broken_links_none() {
        let verifier = default_verifier();
        let chain = simple_chain();
        let broken = verifier.find_broken_links(&chain);

        assert!(broken.is_empty());
    }

    #[test]
    fn test_find_broken_links_some() {
        let verifier = default_verifier();
        let chain = ProofChain {
            links: vec![
                make_link("good", "fn_good", &[], "proven"),
                make_link("bad", "fn_bad", &["nonexistent"], "proven"),
            ],
            root_cert: "good".to_string(),
        };
        let broken = verifier.find_broken_links(&chain);

        assert_eq!(broken, vec!["bad".to_string()]);
    }

    // -----------------------------------------------------------------------
    // chain_depth
    // -----------------------------------------------------------------------

    #[test]
    fn test_chain_depth_simple() {
        let verifier = default_verifier();
        let chain = simple_chain();
        let depth = verifier.chain_depth(&chain);

        assert_eq!(depth, 3); // root -> mid -> leaf
    }

    #[test]
    fn test_chain_depth_empty() {
        let verifier = default_verifier();
        let chain = ProofChain { links: vec![], root_cert: "none".to_string() };
        let depth = verifier.chain_depth(&chain);

        assert_eq!(depth, 0);
    }

    #[test]
    fn test_chain_depth_single() {
        let verifier = default_verifier();
        let chain = ProofChain {
            links: vec![make_link("only", "main", &[], "proven")],
            root_cert: "only".to_string(),
        };
        let depth = verifier.chain_depth(&chain);

        assert_eq!(depth, 1);
    }

    // -----------------------------------------------------------------------
    // topological_order
    // -----------------------------------------------------------------------

    #[test]
    fn test_topological_order_simple() {
        let verifier = default_verifier();
        let chain = simple_chain();
        let order = verifier.topological_order(&chain);

        assert!(order.is_some());
        let order = order.unwrap();
        assert_eq!(order.len(), 3);

        // leaf must come before mid, mid before root.
        let pos = |id: &str| order.iter().position(|s| s == id).unwrap();
        assert!(pos("leaf") < pos("mid"));
        assert!(pos("mid") < pos("root"));
    }

    #[test]
    fn test_topological_order_cycle_returns_none() {
        let verifier = default_verifier();
        let chain = ProofChain {
            links: vec![
                make_link("a", "fn_a", &["b"], "proven"),
                make_link("b", "fn_b", &["a"], "proven"),
            ],
            root_cert: "a".to_string(),
        };
        let order = verifier.topological_order(&chain);

        assert!(order.is_none());
    }

    // -----------------------------------------------------------------------
    // find_roots
    // -----------------------------------------------------------------------

    #[test]
    fn test_find_roots_simple() {
        let verifier = default_verifier();
        let chain = simple_chain();
        let roots = verifier.find_roots(&chain);

        assert_eq!(roots, vec!["root".to_string()]);
    }

    #[test]
    fn test_find_roots_multiple() {
        let verifier = default_verifier();
        let chain = ProofChain {
            links: vec![
                make_link("r1", "main1", &["shared"], "proven"),
                make_link("r2", "main2", &["shared"], "proven"),
                make_link("shared", "lib", &[], "proven"),
            ],
            root_cert: "r1".to_string(),
        };
        let roots = verifier.find_roots(&chain);

        assert_eq!(roots, vec!["r1".to_string(), "r2".to_string()]);
    }

    // -----------------------------------------------------------------------
    // Config variations
    // -----------------------------------------------------------------------

    #[test]
    fn test_config_default() {
        let config = ChainConfig::default();

        assert!(config.strict_mode);
        assert_eq!(config.max_chain_depth, 256);
        assert!(!config.allow_partial);
        assert_eq!(config.min_verified_ratio, 0.5);
    }

    #[test]
    fn test_verify_missing_root_cert_invalid() {
        let verifier = default_verifier();
        let chain = ProofChain {
            links: vec![make_link("a", "fn_a", &[], "proven")],
            root_cert: "nonexistent".to_string(),
        };
        let result = verifier.verify_chain(&chain);

        // Root cert not in chain => invalid in strict mode.
        assert!(!result.is_valid);
    }
}
