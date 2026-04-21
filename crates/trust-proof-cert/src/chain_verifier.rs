// trust-proof-cert chain verifier
//
// Verifies that a ProofChain is sound: each certificate's assumptions
// are discharged by other certificates in the chain. Reports gaps
// (unproven assumptions) and coverage.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::{FxHashMap, FxHashSet};

use serde::{Deserialize, Serialize};

use crate::dep_graph::DepGraph;
use crate::ProofCertificate;

/// A chain of proof certificates forming a whole-program verification.
///
/// Each certificate proves properties about a single function. The chain
/// verifier checks that every certificate's assumptions (callee contracts)
/// are discharged by other certificates in the chain.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProofChain {
    /// Certificates in this chain, keyed by function name.
    pub certificates: FxHashMap<String, ProofCertificate>,
    /// Call graph edges: caller -> list of callees.
    pub call_graph: FxHashMap<String, Vec<String>>,
    /// Name of this proof chain (e.g., crate name).
    pub name: String,
    /// Format version for serialization compatibility.
    pub version: u32,
}

/// Current proof chain format version.
pub const PROOF_CHAIN_VERSION: u32 = 1;

impl ProofChain {
    /// Create a new empty proof chain.
    pub fn new(name: &str) -> Self {
        ProofChain {
            certificates: FxHashMap::default(),
            call_graph: FxHashMap::default(),
            name: name.to_string(),
            version: PROOF_CHAIN_VERSION,
        }
    }

    /// Add a certificate with its callee dependencies.
    pub fn add_certificate(&mut self, cert: ProofCertificate, callees: Vec<String>) {
        let function = cert.function.clone();
        self.call_graph.insert(function.clone(), callees);
        self.certificates.insert(function, cert);
    }

    /// Get a certificate by function name.
    pub fn get_certificate(&self, function: &str) -> Option<&ProofCertificate> {
        self.certificates.get(function)
    }

    /// Return all function names that have certificates.
    pub fn proven_functions(&self) -> Vec<String> {
        let mut names: Vec<String> = self.certificates.keys().cloned().collect();
        names.sort();
        names
    }

    /// Return the number of certificates in the chain.
    pub fn len(&self) -> usize {
        self.certificates.len()
    }

    /// Return true if the chain has no certificates.
    pub fn is_empty(&self) -> bool {
        self.certificates.is_empty()
    }

    /// Build a dependency graph from this chain's call graph.
    pub fn to_dep_graph(&self) -> DepGraph {
        let mut graph = DepGraph::new();
        // Add all functions from the call graph
        let all_functions: FxHashSet<&str> = self
            .call_graph
            .keys()
            .map(|s| s.as_str())
            .chain(
                self.call_graph
                    .values()
                    .flat_map(|v| v.iter().map(|s| s.as_str())),
            )
            .collect();

        for func in all_functions {
            let callees = self
                .call_graph
                .get(func)
                .cloned()
                .unwrap_or_default();
            let has_proof = self.certificates.contains_key(func);
            graph.add_function(func, callees, has_proof);
        }

        graph
    }
}

/// Result of verifying a proof chain.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ChainVerificationResult {
    /// Whether the chain is sound (all assumptions discharged, no gaps).
    pub sound: bool,
    /// Functions with valid proofs whose assumptions are all discharged.
    pub discharged: Vec<String>,
    /// Gaps: functions referenced as callees but without proof certificates.
    pub gaps: Vec<ChainGap>,
    /// Functions with proof certificates that failed individual verification.
    pub invalid_certs: Vec<String>,
    /// Circular dependencies detected (if any).
    pub cycles: Vec<Vec<String>>,
    /// Coverage: fraction of functions with valid proofs (0.0 - 1.0).
    pub coverage: f64,
    /// Total number of functions in the call graph.
    pub total_functions: usize,
    /// Number of functions with valid certificates.
    pub proven_count: usize,
}

/// A gap in the proof chain: an unproven assumption.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ChainGap {
    /// The function that is missing a proof.
    pub function: String,
    /// Functions that depend on this unproven function.
    pub depended_on_by: Vec<String>,
}

/// Verifies a proof chain for soundness.
///
/// A chain is sound when:
/// 1. Every certificate passes standalone verification (VC hash, chain integrity)
/// 2. Every function's callee assumptions are discharged by certificates in the chain
/// 3. The dependency graph is acyclic (or cycles are explicitly handled)
/// 4. No gaps exist (all referenced functions have certificates)
pub fn verify_proof_chain(chain: &ProofChain) -> ChainVerificationResult {
    let dep_graph = chain.to_dep_graph();
    let analysis = dep_graph.analyze();

    // Check each certificate individually
    let mut invalid_certs = Vec::new();
    for (function, cert) in &chain.certificates {
        if !cert.verify_vc_hash() {
            invalid_certs.push(function.clone());
        }
    }
    invalid_certs.sort();

    // Find gaps: functions in the call graph without certificates
    let mut gaps: Vec<ChainGap> = Vec::new();
    let mut gap_set: FxHashSet<String> = FxHashSet::default();
    for (caller, callees) in &chain.call_graph {
        for callee in callees {
            if !chain.certificates.contains_key(callee) && !gap_set.contains(callee) {
                gap_set.insert(callee.clone());
                gaps.push(ChainGap {
                    function: callee.clone(),
                    depended_on_by: vec![caller.clone()],
                });
            } else if !chain.certificates.contains_key(callee) {
                // Already in gaps, add this caller to depended_on_by
                if let Some(gap) = gaps.iter_mut().find(|g| g.function == *callee)
                    && !gap.depended_on_by.contains(caller)
                {

                        gap.depended_on_by.push(caller.clone());

                }
            }
        }
    }
    for gap in &mut gaps {
        gap.depended_on_by.sort();
    }
    gaps.sort_by(|a, b| a.function.cmp(&b.function));

    // Extract cycles from SCCs
    let cycles: Vec<Vec<String>> = analysis
        .sccs
        .iter()
        .filter(|scc| scc.is_recursive())
        .map(|scc| scc.functions.clone())
        .collect();

    // Compute discharged functions: have proof and all callees are proven
    let discharged = analysis.fully_discharged;

    // Total functions includes both proven and gap functions
    let all_functions: FxHashSet<&str> = chain
        .call_graph
        .keys()
        .map(|s| s.as_str())
        .chain(
            chain
                .call_graph
                .values()
                .flat_map(|v| v.iter().map(|s| s.as_str())),
        )
        .collect();
    let total_functions = all_functions.len();
    let proven_count = chain.certificates.len() - invalid_certs.len();

    let coverage = if total_functions == 0 {
        0.0
    } else {
        proven_count as f64 / total_functions as f64
    };

    // Sound if: no gaps, no invalid certs, no cycles
    let sound = gaps.is_empty() && invalid_certs.is_empty() && cycles.is_empty();

    ChainVerificationResult {
        sound,
        discharged,
        gaps,
        invalid_certs,
        cycles,
        coverage,
        total_functions,
        proven_count,
    }
}

/// Quick check: is this proof chain complete (all assumptions discharged)?
pub fn is_chain_complete(chain: &ProofChain) -> bool {
    let result = verify_proof_chain(chain);
    result.sound
}

#[cfg(test)]
mod tests {
    use trust_types::{Formula, ProofStrength, SourceSpan, VcKind, VerificationCondition};

    use super::*;
    use crate::{FunctionHash, SolverInfo, VcSnapshot};

    fn sample_solver() -> SolverInfo {
        SolverInfo {
            name: "z4".to_string(),
            version: "1.0.0".to_string(),
            time_ms: 10,
            strength: ProofStrength::smt_unsat(),
            evidence: None,
        }
    }

    fn sample_vc(function: &str) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::Assertion {
                message: "test".to_string(),
            },
            function: function.to_string(),
            location: SourceSpan {
                file: "src/lib.rs".to_string(),
                line_start: 1,
                col_start: 1,
                line_end: 1,
                col_end: 10,
            },
            formula: Formula::Bool(true),
            contract_metadata: None,
        }
    }

    fn make_cert(function: &str) -> ProofCertificate {
        let vc = sample_vc(function);
        let snapshot = VcSnapshot::from_vc(&vc).expect("snapshot");
        ProofCertificate::new_trusted(
            function.to_string(),
            FunctionHash::from_bytes(format!("{function}-body").as_bytes()),
            snapshot,
            sample_solver(),
            vec![1, 2, 3],
            "2026-03-29T00:00:00Z".to_string(),
        )
    }

    #[test]
    fn test_proof_chain_new() {
        let chain = ProofChain::new("my-crate");
        assert!(chain.is_empty());
        assert_eq!(chain.len(), 0);
        assert_eq!(chain.name, "my-crate");
        assert_eq!(chain.version, PROOF_CHAIN_VERSION);
    }

    #[test]
    fn test_proof_chain_add_certificate() {
        let mut chain = ProofChain::new("test");
        let cert = make_cert("foo");
        chain.add_certificate(cert.clone(), vec!["bar".to_string()]);

        assert_eq!(chain.len(), 1);
        assert!(!chain.is_empty());
        assert_eq!(chain.proven_functions(), vec!["foo"]);
        assert_eq!(chain.get_certificate("foo"), Some(&cert));
    }

    #[test]
    fn test_verify_complete_chain() {
        let mut chain = ProofChain::new("test");
        chain.add_certificate(make_cert("foo"), vec!["bar".to_string()]);
        chain.add_certificate(make_cert("bar"), vec![]);

        let result = verify_proof_chain(&chain);
        assert!(result.sound, "complete chain should be sound: {:?}", result);
        assert!(result.gaps.is_empty());
        assert!(result.invalid_certs.is_empty());
        assert!(result.cycles.is_empty());
        assert_eq!(result.total_functions, 2);
        assert_eq!(result.proven_count, 2);
        assert!((result.coverage - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_verify_chain_with_gap() {
        let mut chain = ProofChain::new("test");
        chain.add_certificate(make_cert("foo"), vec!["bar".to_string()]);
        // bar is missing

        let result = verify_proof_chain(&chain);
        assert!(!result.sound, "chain with gap should not be sound");
        assert_eq!(result.gaps.len(), 1);
        assert_eq!(result.gaps[0].function, "bar");
        assert_eq!(result.gaps[0].depended_on_by, vec!["foo"]);
    }

    #[test]
    fn test_verify_chain_with_cycle() {
        let mut chain = ProofChain::new("test");
        chain.add_certificate(make_cert("foo"), vec!["bar".to_string()]);
        chain.add_certificate(make_cert("bar"), vec!["foo".to_string()]);

        let result = verify_proof_chain(&chain);
        assert!(!result.sound, "chain with cycle should not be sound");
        assert!(!result.cycles.is_empty());
    }

    #[test]
    fn test_verify_chain_with_invalid_cert() {
        let mut chain = ProofChain::new("test");
        let mut bad_cert = make_cert("foo");
        bad_cert.vc_hash[0] ^= 0xFF; // corrupt
        chain.add_certificate(bad_cert, vec![]);

        let result = verify_proof_chain(&chain);
        assert!(!result.sound);
        assert_eq!(result.invalid_certs, vec!["foo"]);
    }

    #[test]
    fn test_verify_empty_chain() {
        let chain = ProofChain::new("test");
        let result = verify_proof_chain(&chain);
        // Empty chain is vacuously sound
        assert!(result.sound);
        assert_eq!(result.total_functions, 0);
        assert!((result.coverage - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_is_chain_complete() {
        let mut complete = ProofChain::new("test");
        complete.add_certificate(make_cert("foo"), vec!["bar".to_string()]);
        complete.add_certificate(make_cert("bar"), vec![]);
        assert!(is_chain_complete(&complete));

        let mut incomplete = ProofChain::new("test");
        incomplete.add_certificate(make_cert("foo"), vec!["bar".to_string()]);
        assert!(!is_chain_complete(&incomplete));
    }

    #[test]
    fn test_proof_chain_to_dep_graph() {
        let mut chain = ProofChain::new("test");
        chain.add_certificate(make_cert("a"), vec!["b".to_string(), "c".to_string()]);
        chain.add_certificate(make_cert("b"), vec!["c".to_string()]);
        chain.add_certificate(make_cert("c"), vec![]);

        let graph = chain.to_dep_graph();
        assert_eq!(graph.len(), 3);

        let a = graph.get_node("a").expect("a should exist");
        assert!(a.has_proof);
        assert_eq!(a.callees.len(), 2);
    }

    #[test]
    fn test_verify_chain_multiple_gaps() {
        let mut chain = ProofChain::new("test");
        chain.add_certificate(
            make_cert("main"),
            vec!["helper_a".to_string(), "helper_b".to_string()],
        );

        let result = verify_proof_chain(&chain);
        assert!(!result.sound);
        assert_eq!(result.gaps.len(), 2);
        let gap_names: Vec<&str> = result.gaps.iter().map(|g| g.function.as_str()).collect();
        assert!(gap_names.contains(&"helper_a"));
        assert!(gap_names.contains(&"helper_b"));
    }

    #[test]
    fn test_verify_chain_discharged_functions() {
        let mut chain = ProofChain::new("test");
        chain.add_certificate(make_cert("foo"), vec!["bar".to_string()]);
        chain.add_certificate(make_cert("bar"), vec![]);

        let result = verify_proof_chain(&chain);
        // Both are fully discharged: bar has no callees, foo's callee (bar) is proven
        assert!(result.discharged.contains(&"bar".to_string()));
        assert!(result.discharged.contains(&"foo".to_string()));
    }

    #[test]
    fn test_verify_chain_partial_discharge() {
        let mut chain = ProofChain::new("test");
        chain.add_certificate(
            make_cert("foo"),
            vec!["bar".to_string(), "baz".to_string()],
        );
        chain.add_certificate(make_cert("bar"), vec![]);
        // baz is missing

        let result = verify_proof_chain(&chain);
        // bar is fully discharged (no deps), foo is NOT (baz missing)
        assert!(result.discharged.contains(&"bar".to_string()));
        assert!(!result.discharged.contains(&"foo".to_string()));
    }

    #[test]
    fn test_gap_depended_on_by_multiple() {
        let mut chain = ProofChain::new("test");
        chain.add_certificate(make_cert("caller_a"), vec!["shared".to_string()]);
        chain.add_certificate(make_cert("caller_b"), vec!["shared".to_string()]);

        let result = verify_proof_chain(&chain);
        assert_eq!(result.gaps.len(), 1);
        let gap = &result.gaps[0];
        assert_eq!(gap.function, "shared");
        assert!(gap.depended_on_by.contains(&"caller_a".to_string()));
        assert!(gap.depended_on_by.contains(&"caller_b".to_string()));
    }
}
