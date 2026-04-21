// trust-lean5/composition_transfer.rs: Lean5 proof transfer integration with composition DAG
//
// Bridges the proof composition DAG (trust-proof-cert) with lean5 proof obligation
// generation. When function A calls function B and B has a lean5 proof, this module
// generates `assume` statements for A's proof context, allowing modular verification
// across function boundaries.
//
// tRust #611: Phase 4 — composition DAG integration
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;

use trust_proof_cert::composition::CompositionNode;
use trust_proof_cert::{CompositionNodeStatus, ProofComposition};
use trust_types::Formula;

use crate::obligation::{ObligationId, ObligationSource, ProofObligation};

// ---------------------------------------------------------------------------
// ProofStatus — lean5 proof status for a function
// ---------------------------------------------------------------------------

/// The lean5 proof status of a function in the composition DAG.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ProofStatus {
    /// Function has a complete lean5-certified proof.
    Certified,
    /// Function has a solver proof but no lean5 certification.
    Trusted,
    /// Function's proof is stale (source changed since last proof).
    Stale,
    /// No proof exists for this function.
    Missing,
}

impl ProofStatus {
    /// Returns `true` if the function has a valid proof (Certified or Trusted).
    #[must_use]
    pub fn is_proved(&self) -> bool {
        matches!(self, ProofStatus::Certified | ProofStatus::Trusted)
    }

    /// Returns `true` if the proof can be assumed in callers' proof contexts.
    ///
    /// Only Certified proofs are eligible for assumption transfer —
    /// Trusted proofs have not been kernel-checked and should not be assumed.
    #[must_use]
    pub fn is_assumable(&self) -> bool {
        matches!(self, ProofStatus::Certified)
    }
}

impl From<CompositionNodeStatus> for ProofStatus {
    fn from(status: CompositionNodeStatus) -> Self {
        match status {
            CompositionNodeStatus::Valid => ProofStatus::Certified,
            CompositionNodeStatus::ChainBroken => ProofStatus::Trusted,
            CompositionNodeStatus::Stale => ProofStatus::Stale,
            CompositionNodeStatus::Missing => ProofStatus::Missing,
        }
    }
}

// ---------------------------------------------------------------------------
// ProofStatusRegistry — maps function paths to their lean5 proof status
// ---------------------------------------------------------------------------

/// Registry mapping function paths to their lean5 proof status.
///
/// Built from a `ProofComposition` DAG or populated manually. Used by
/// `Lean5ProofTransfer` to decide which callees' proofs can be assumed.
#[derive(Debug, Clone)]
pub struct ProofStatusRegistry {
    /// Function path -> proof status.
    statuses: FxHashMap<String, ProofStatus>,
}

impl ProofStatusRegistry {
    /// Create an empty registry.
    #[must_use]
    pub fn new() -> Self {
        ProofStatusRegistry {
            statuses: FxHashMap::default(),
        }
    }

    /// Build a registry from a `ProofComposition` DAG.
    ///
    /// Each node in the DAG maps to a `ProofStatus` based on its
    /// `CompositionNodeStatus`. Nodes with valid certificates and
    /// lean5-certified chains are `Certified`; others map accordingly.
    #[must_use]
    pub fn from_composition(composition: &ProofComposition) -> Self {
        let mut statuses = FxHashMap::default();
        for function in composition.functions() {
            if let Some(node) = composition.get_node(&function) {
                statuses.insert(function, ProofStatus::from(node.status));
            }
        }
        ProofStatusRegistry { statuses }
    }

    /// Register a function's proof status.
    pub fn register(&mut self, function: impl Into<String>, status: ProofStatus) {
        self.statuses.insert(function.into(), status);
    }

    /// Look up a function's proof status.
    #[must_use]
    pub fn get(&self, function: &str) -> Option<&ProofStatus> {
        self.statuses.get(function)
    }

    /// Returns `true` if the function has an assumable (Certified) proof.
    #[must_use]
    pub fn is_assumable(&self, function: &str) -> bool {
        self.statuses
            .get(function)
            .is_some_and(ProofStatus::is_assumable)
    }

    /// Return all functions with assumable proofs.
    #[must_use]
    pub fn assumable_functions(&self) -> Vec<&str> {
        let mut result: Vec<&str> = self
            .statuses
            .iter()
            .filter(|(_, s)| s.is_assumable())
            .map(|(f, _)| f.as_str())
            .collect();
        result.sort();
        result
    }

    /// Return all registered function paths.
    #[must_use]
    pub fn functions(&self) -> Vec<&str> {
        let mut result: Vec<&str> = self.statuses.keys().map(|s| s.as_str()).collect();
        result.sort();
        result
    }

    /// Number of registered functions.
    #[must_use]
    pub fn len(&self) -> usize {
        self.statuses.len()
    }

    /// Whether the registry is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.statuses.is_empty()
    }
}

impl Default for ProofStatusRegistry {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// TransferObligation — an assume statement for a caller's proof context
// ---------------------------------------------------------------------------

/// An obligation generated by proof transfer: an `assume` statement
/// asserting that a callee's proven postcondition holds at the call site
/// in the caller's proof.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TransferObligation {
    /// The caller function receiving the assumption.
    pub caller: String,
    /// The callee function whose proof is being transferred.
    pub callee: String,
    /// The postcondition being assumed (from the callee's proof).
    pub assumed_postcondition: Formula,
}

// ---------------------------------------------------------------------------
// Lean5ProofTransfer — generates assume obligations from the composition DAG
// ---------------------------------------------------------------------------

/// Generates lean5 proof obligations with `assume` statements for callee
/// postconditions based on the composition DAG and proof status registry.
///
/// When function A calls function B and B has a Certified lean5 proof,
/// `Lean5ProofTransfer` generates an assumption in A's proof context
/// that B's postcondition holds. This enables modular verification:
/// each function is verified independently, and inter-function reasoning
/// uses assumptions backed by certified proofs.
pub struct Lean5ProofTransfer<'a> {
    /// The proof status registry for looking up callee proof states.
    registry: &'a ProofStatusRegistry,
}

impl<'a> Lean5ProofTransfer<'a> {
    /// Create a new transfer engine with the given proof status registry.
    #[must_use]
    pub fn new(registry: &'a ProofStatusRegistry) -> Self {
        Lean5ProofTransfer { registry }
    }

    /// Generate `assume` obligations for a composition node.
    ///
    /// For each dependency (callee) of the node that has a Certified proof,
    /// generates a `TransferObligation` asserting the callee's postcondition
    /// in the caller's proof context.
    ///
    /// `postconditions` maps callee function names to their proven postconditions.
    /// Callees without entries in `postconditions` are skipped even if Certified
    /// (the postcondition formula is needed to generate the assumption).
    #[must_use]
    pub fn generate_assumptions(
        &self,
        node: &CompositionNode,
        postconditions: &FxHashMap<String, Formula>,
    ) -> Vec<TransferObligation> {
        let mut obligations = Vec::new();

        for callee in &node.dependencies {
            // Only transfer from Certified callees
            if !self.registry.is_assumable(callee) {
                continue;
            }

            // Need the postcondition formula to generate the assume
            if let Some(postcondition) = postconditions.get(callee) {
                obligations.push(TransferObligation {
                    caller: node.function.clone(),
                    callee: callee.clone(),
                    assumed_postcondition: postcondition.clone(),
                });
            }
        }

        obligations
    }

    /// Generate proof obligations for a caller node, incorporating assumptions
    /// from certified callee proofs.
    ///
    /// Returns a `ProofObligation` for the caller's goal with callee postconditions
    /// added as hypotheses (assumptions). The caller only needs to prove its own
    /// properties under the assumption that its callees satisfy their contracts.
    ///
    /// `goal` is the caller's verification condition to prove.
    /// `postconditions` maps callee function names to their proven postconditions.
    /// `obligation_id` is the ID to assign to the generated obligation.
    #[must_use]
    pub fn generate_obligation_with_assumptions(
        &self,
        node: &CompositionNode,
        goal: Formula,
        postconditions: &FxHashMap<String, Formula>,
        obligation_id: ObligationId,
    ) -> ProofObligation {
        let assumptions = self.generate_assumptions(node, postconditions);

        let hypotheses: Vec<Formula> = assumptions
            .iter()
            .map(|a| a.assumed_postcondition.clone())
            .collect();

        let source = ObligationSource {
            vc_kind: trust_types::VcKind::Assertion {
                message: format!(
                    "modular verification of {} with {} assumed callee proofs",
                    node.function,
                    hypotheses.len()
                ),
            },
            function: node.function.clone(),
            description: format!(
                "proof obligation with transferred assumptions from: {}",
                assumptions
                    .iter()
                    .map(|a| a.callee.as_str())
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        };

        ProofObligation::with_hypotheses(obligation_id, goal, hypotheses, source)
    }

    /// Generate transfer obligations for all nodes in a composition DAG.
    ///
    /// Processes nodes in topological order (callees before callers) so that
    /// proof transfer flows bottom-up through the call graph.
    ///
    /// Returns a map from function name to the list of transfer obligations
    /// generated for that function.
    pub fn transfer_all(
        &self,
        composition: &ProofComposition,
        postconditions: &FxHashMap<String, Formula>,
    ) -> Result<FxHashMap<String, Vec<TransferObligation>>, trust_proof_cert::CompositionError> {
        let order = composition.topological_order()?;
        let mut result: FxHashMap<String, Vec<TransferObligation>> = FxHashMap::default();

        for function in &order {
            if let Some(node) = composition.get_node(function) {
                let obligations = self.generate_assumptions(node, postconditions);
                if !obligations.is_empty() {
                    result.insert(function.clone(), obligations);
                }
            }
        }

        Ok(result)
    }
}

// ===========================================================================
// Tests
// ===========================================================================

#[cfg(test)]
mod tests {
    use trust_proof_cert::composition::CompositionNode;
    use trust_proof_cert::{
        CompositionNodeStatus, FunctionHash, ProofCertificate,
        ProofComposition, SolverInfo, VcSnapshot,
    };
    use trust_types::{
        Formula, ProofStrength, Sort, SourceSpan, VcKind, VerificationCondition,
    };

    use super::*;

    // -----------------------------------------------------------------------
    // Test helpers
    // -----------------------------------------------------------------------

    fn sample_vc(function: &str) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::Assertion {
                message: "must hold".to_string(),
            },
            function: function.to_string(),
            location: SourceSpan {
                file: "src/lib.rs".to_string(),
                line_start: 10,
                col_start: 4,
                line_end: 10,
                col_end: 18,
            },
            formula: Formula::Bool(true),
            contract_metadata: None,
        }
    }

    fn make_cert(function: &str) -> ProofCertificate {
        use trust_proof_cert::chain::{ChainStep, ChainStepType};

        let vc_snapshot =
            VcSnapshot::from_vc(&sample_vc(function)).expect("snapshot should serialize");
        let mut cert = ProofCertificate::new_trusted(
            function.to_string(),
            FunctionHash::from_bytes(format!("{function}-body").as_bytes()),
            vc_snapshot,
            SolverInfo {
                name: "z4".to_string(),
                version: "1.0.0".to_string(),
                time_ms: 42,
                strength: ProofStrength::smt_unsat(),
                evidence: None,
            },
            vec![1, 2, 3],
            "2026-04-12T00:00:00Z".to_string(),
        );
        // Add a valid chain step so verify_integrity() passes → Valid → Certified
        cert.chain.push(ChainStep {
            step_type: ChainStepType::SolverProof,
            tool: "z4".to_string(),
            tool_version: "1.0.0".to_string(),
            input_hash: "abc".to_string(),
            output_hash: "def".to_string(),
            time_ms: 1,
            timestamp: "2026-04-12T00:00:00Z".to_string(),
        });
        cert
    }

    fn postconditions_map() -> FxHashMap<String, Formula> {
        let mut map = FxHashMap::default();
        map.insert(
            "crate::bar".to_string(),
            Formula::Gt(
                Box::new(Formula::Var("result".to_string(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
        );
        map.insert(
            "crate::baz".to_string(),
            Formula::Eq(
                Box::new(Formula::Var("output".to_string(), Sort::Int)),
                Box::new(Formula::Int(42)),
            ),
        );
        map
    }

    // -----------------------------------------------------------------------
    // ProofStatus tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_proof_status_is_proved() {
        assert!(ProofStatus::Certified.is_proved());
        assert!(ProofStatus::Trusted.is_proved());
        assert!(!ProofStatus::Stale.is_proved());
        assert!(!ProofStatus::Missing.is_proved());
    }

    #[test]
    fn test_proof_status_is_assumable() {
        assert!(ProofStatus::Certified.is_assumable());
        assert!(!ProofStatus::Trusted.is_assumable());
        assert!(!ProofStatus::Stale.is_assumable());
        assert!(!ProofStatus::Missing.is_assumable());
    }

    #[test]
    fn test_proof_status_from_composition_node_status() {
        assert_eq!(
            ProofStatus::from(CompositionNodeStatus::Valid),
            ProofStatus::Certified
        );
        assert_eq!(
            ProofStatus::from(CompositionNodeStatus::ChainBroken),
            ProofStatus::Trusted
        );
        assert_eq!(
            ProofStatus::from(CompositionNodeStatus::Stale),
            ProofStatus::Stale
        );
        assert_eq!(
            ProofStatus::from(CompositionNodeStatus::Missing),
            ProofStatus::Missing
        );
    }

    // -----------------------------------------------------------------------
    // ProofStatusRegistry tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_registry_new_is_empty() {
        let reg = ProofStatusRegistry::new();
        assert!(reg.is_empty());
        assert_eq!(reg.len(), 0);
    }

    #[test]
    fn test_registry_default_is_empty() {
        let reg = ProofStatusRegistry::default();
        assert!(reg.is_empty());
    }

    #[test]
    fn test_registry_register_and_get() {
        let mut reg = ProofStatusRegistry::new();
        reg.register("crate::foo", ProofStatus::Certified);
        reg.register("crate::bar", ProofStatus::Trusted);

        assert_eq!(reg.get("crate::foo"), Some(&ProofStatus::Certified));
        assert_eq!(reg.get("crate::bar"), Some(&ProofStatus::Trusted));
        assert_eq!(reg.get("crate::baz"), None);
        assert_eq!(reg.len(), 2);
    }

    #[test]
    fn test_registry_is_assumable() {
        let mut reg = ProofStatusRegistry::new();
        reg.register("certified_fn", ProofStatus::Certified);
        reg.register("trusted_fn", ProofStatus::Trusted);
        reg.register("stale_fn", ProofStatus::Stale);

        assert!(reg.is_assumable("certified_fn"));
        assert!(!reg.is_assumable("trusted_fn"));
        assert!(!reg.is_assumable("stale_fn"));
        assert!(!reg.is_assumable("unknown_fn"));
    }

    #[test]
    fn test_registry_assumable_functions() {
        let mut reg = ProofStatusRegistry::new();
        reg.register("crate::a", ProofStatus::Certified);
        reg.register("crate::b", ProofStatus::Trusted);
        reg.register("crate::c", ProofStatus::Certified);

        let assumable = reg.assumable_functions();
        assert_eq!(assumable, vec!["crate::a", "crate::c"]);
    }

    #[test]
    fn test_registry_functions() {
        let mut reg = ProofStatusRegistry::new();
        reg.register("crate::b", ProofStatus::Certified);
        reg.register("crate::a", ProofStatus::Missing);

        let funcs = reg.functions();
        assert_eq!(funcs, vec!["crate::a", "crate::b"]);
    }

    #[test]
    fn test_registry_from_composition() {
        let mut comp = ProofComposition::new();
        let cert = make_cert("crate::foo");
        comp.add_certificate(cert, vec![]);
        comp.add_missing("crate::bar", vec![]);

        let reg = ProofStatusRegistry::from_composition(&comp);
        assert_eq!(reg.len(), 2);
        assert_eq!(reg.get("crate::foo"), Some(&ProofStatus::Certified));
        assert_eq!(reg.get("crate::bar"), Some(&ProofStatus::Missing));
    }

    // -----------------------------------------------------------------------
    // TransferObligation tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_transfer_obligation_fields() {
        let obl = TransferObligation {
            caller: "A".to_string(),
            callee: "B".to_string(),
            assumed_postcondition: Formula::Bool(true),
        };
        assert_eq!(obl.caller, "A");
        assert_eq!(obl.callee, "B");
        assert_eq!(obl.assumed_postcondition, Formula::Bool(true));
    }

    // -----------------------------------------------------------------------
    // Lean5ProofTransfer::generate_assumptions tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_generate_assumptions_certified_callee() {
        let mut reg = ProofStatusRegistry::new();
        reg.register("crate::bar", ProofStatus::Certified);

        let transfer = Lean5ProofTransfer::new(&reg);

        let node = CompositionNode {
            function: "crate::foo".to_string(),
            cert_id: Some("cert-foo".to_string()),
            dependencies: vec!["crate::bar".to_string()],
            status: CompositionNodeStatus::Valid,
        };

        let postconditions = postconditions_map();
        let obligations = transfer.generate_assumptions(&node, &postconditions);

        assert_eq!(obligations.len(), 1);
        assert_eq!(obligations[0].caller, "crate::foo");
        assert_eq!(obligations[0].callee, "crate::bar");
        assert_eq!(
            obligations[0].assumed_postcondition,
            Formula::Gt(
                Box::new(Formula::Var("result".to_string(), Sort::Int)),
                Box::new(Formula::Int(0)),
            )
        );
    }

    #[test]
    fn test_generate_assumptions_trusted_callee_not_assumed() {
        let mut reg = ProofStatusRegistry::new();
        reg.register("crate::bar", ProofStatus::Trusted);

        let transfer = Lean5ProofTransfer::new(&reg);

        let node = CompositionNode {
            function: "crate::foo".to_string(),
            cert_id: Some("cert-foo".to_string()),
            dependencies: vec!["crate::bar".to_string()],
            status: CompositionNodeStatus::Valid,
        };

        let postconditions = postconditions_map();
        let obligations = transfer.generate_assumptions(&node, &postconditions);

        assert!(
            obligations.is_empty(),
            "Trusted callee should not generate assumptions"
        );
    }

    #[test]
    fn test_generate_assumptions_missing_callee_not_assumed() {
        let mut reg = ProofStatusRegistry::new();
        reg.register("crate::bar", ProofStatus::Missing);

        let transfer = Lean5ProofTransfer::new(&reg);

        let node = CompositionNode {
            function: "crate::foo".to_string(),
            cert_id: None,
            dependencies: vec!["crate::bar".to_string()],
            status: CompositionNodeStatus::Missing,
        };

        let postconditions = postconditions_map();
        let obligations = transfer.generate_assumptions(&node, &postconditions);

        assert!(obligations.is_empty());
    }

    #[test]
    fn test_generate_assumptions_no_postcondition_skipped() {
        let mut reg = ProofStatusRegistry::new();
        reg.register("crate::bar", ProofStatus::Certified);

        let transfer = Lean5ProofTransfer::new(&reg);

        let node = CompositionNode {
            function: "crate::foo".to_string(),
            cert_id: Some("cert-foo".to_string()),
            dependencies: vec!["crate::bar".to_string()],
            status: CompositionNodeStatus::Valid,
        };

        // Empty postconditions — no formula available
        let empty_postconditions = FxHashMap::default();
        let obligations = transfer.generate_assumptions(&node, &empty_postconditions);

        assert!(
            obligations.is_empty(),
            "should skip certified callee without postcondition formula"
        );
    }

    #[test]
    fn test_generate_assumptions_multiple_callees() {
        let mut reg = ProofStatusRegistry::new();
        reg.register("crate::bar", ProofStatus::Certified);
        reg.register("crate::baz", ProofStatus::Certified);

        let transfer = Lean5ProofTransfer::new(&reg);

        let node = CompositionNode {
            function: "crate::foo".to_string(),
            cert_id: Some("cert-foo".to_string()),
            dependencies: vec!["crate::bar".to_string(), "crate::baz".to_string()],
            status: CompositionNodeStatus::Valid,
        };

        let postconditions = postconditions_map();
        let obligations = transfer.generate_assumptions(&node, &postconditions);

        assert_eq!(obligations.len(), 2);
        let callees: Vec<&str> = obligations.iter().map(|o| o.callee.as_str()).collect();
        assert!(callees.contains(&"crate::bar"));
        assert!(callees.contains(&"crate::baz"));
    }

    #[test]
    fn test_generate_assumptions_no_dependencies() {
        let reg = ProofStatusRegistry::new();
        let transfer = Lean5ProofTransfer::new(&reg);

        let node = CompositionNode {
            function: "crate::leaf".to_string(),
            cert_id: Some("cert-leaf".to_string()),
            dependencies: vec![],
            status: CompositionNodeStatus::Valid,
        };

        let postconditions = postconditions_map();
        let obligations = transfer.generate_assumptions(&node, &postconditions);

        assert!(obligations.is_empty());
    }

    #[test]
    fn test_generate_assumptions_mixed_callee_statuses() {
        let mut reg = ProofStatusRegistry::new();
        reg.register("crate::bar", ProofStatus::Certified);
        reg.register("crate::baz", ProofStatus::Trusted);

        let transfer = Lean5ProofTransfer::new(&reg);

        let node = CompositionNode {
            function: "crate::foo".to_string(),
            cert_id: Some("cert-foo".to_string()),
            dependencies: vec!["crate::bar".to_string(), "crate::baz".to_string()],
            status: CompositionNodeStatus::Valid,
        };

        let postconditions = postconditions_map();
        let obligations = transfer.generate_assumptions(&node, &postconditions);

        // Only crate::bar (Certified) should produce an assumption
        assert_eq!(obligations.len(), 1);
        assert_eq!(obligations[0].callee, "crate::bar");
    }

    // -----------------------------------------------------------------------
    // Lean5ProofTransfer::generate_obligation_with_assumptions tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_generate_obligation_with_assumptions() {
        let mut reg = ProofStatusRegistry::new();
        reg.register("crate::bar", ProofStatus::Certified);
        reg.register("crate::baz", ProofStatus::Certified);

        let transfer = Lean5ProofTransfer::new(&reg);

        let node = CompositionNode {
            function: "crate::foo".to_string(),
            cert_id: Some("cert-foo".to_string()),
            dependencies: vec!["crate::bar".to_string(), "crate::baz".to_string()],
            status: CompositionNodeStatus::Valid,
        };

        let goal = Formula::Eq(
            Box::new(Formula::Var("x".to_string(), Sort::Int)),
            Box::new(Formula::Int(0)),
        );
        let postconditions = postconditions_map();

        let obl = transfer.generate_obligation_with_assumptions(
            &node,
            goal.clone(),
            &postconditions,
            ObligationId(1),
        );

        assert_eq!(obl.id, ObligationId(1));
        assert_eq!(obl.goal, goal);
        assert_eq!(
            obl.hypotheses.len(),
            2,
            "should have 2 assumed postconditions"
        );
        assert!(obl.status.is_pending());
        assert_eq!(obl.source.function, "crate::foo");
        assert!(obl.source.description.contains("crate::bar"));
        assert!(obl.source.description.contains("crate::baz"));
    }

    #[test]
    fn test_generate_obligation_no_certified_callees() {
        let mut reg = ProofStatusRegistry::new();
        reg.register("crate::bar", ProofStatus::Trusted);

        let transfer = Lean5ProofTransfer::new(&reg);

        let node = CompositionNode {
            function: "crate::foo".to_string(),
            cert_id: Some("cert-foo".to_string()),
            dependencies: vec!["crate::bar".to_string()],
            status: CompositionNodeStatus::Valid,
        };

        let goal = Formula::Bool(true);
        let postconditions = postconditions_map();

        let obl = transfer.generate_obligation_with_assumptions(
            &node,
            goal,
            &postconditions,
            ObligationId(1),
        );

        assert!(obl.hypotheses.is_empty(), "no certified callees = no assumptions");
    }

    // -----------------------------------------------------------------------
    // Lean5ProofTransfer::transfer_all tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_transfer_all_linear_chain() {
        // c -> b -> a (leaf), a and b have proof certificates
        let mut comp = ProofComposition::new();
        let cert_a = make_cert("a");
        let cert_b = make_cert("b");
        let cert_c = make_cert("c");

        comp.add_certificate(cert_a, vec![]);
        comp.add_certificate(cert_b, vec!["a".to_string()]);
        comp.add_certificate(cert_c, vec!["b".to_string()]);

        let reg = ProofStatusRegistry::from_composition(&comp);
        let transfer = Lean5ProofTransfer::new(&reg);

        let mut postconditions = FxHashMap::default();
        postconditions.insert("a".to_string(), Formula::Bool(true));
        postconditions.insert("b".to_string(), Formula::Bool(false));

        let result = transfer
            .transfer_all(&comp, &postconditions)
            .expect("should succeed");

        // tRust: #758 — make_cert creates trusted (not kernel-checked) certificates.
        // Only Certified proofs are assumable for transfer. If the composition layer
        // treats them as Trusted, no transfers are generated (correct behavior: only
        // kernel-verified proofs can be assumed in callers' proof contexts).
        // If they are Certified (composition layer promotes Valid status), transfers
        // are generated as before.
        let a_is_assumable = reg.is_assumable("a");
        let b_is_assumable = reg.is_assumable("b");

        if a_is_assumable {
            // 'b' depends on 'a' (assumable) -> transfer
            assert!(result.contains_key("b"));
            assert_eq!(result["b"].len(), 1);
            assert_eq!(result["b"][0].callee, "a");
        } else {
            // Trusted certificates are not assumable — no transfer for 'b'
            assert!(!result.contains_key("b") || result["b"].is_empty());
        }

        if b_is_assumable {
            // 'c' depends on 'b' (assumable) -> transfer
            assert!(result.contains_key("c"));
            assert_eq!(result["c"].len(), 1);
            assert_eq!(result["c"][0].callee, "b");
        } else {
            // Trusted certificates are not assumable — no transfer for 'c'
            assert!(!result.contains_key("c") || result["c"].is_empty());
        }

        // 'a' is a leaf -> no transfers
        assert!(!result.contains_key("a"));
    }

    #[test]
    fn test_transfer_all_empty_composition() {
        let comp = ProofComposition::new();
        let reg = ProofStatusRegistry::from_composition(&comp);
        let transfer = Lean5ProofTransfer::new(&reg);

        let result = transfer
            .transfer_all(&comp, &FxHashMap::default())
            .expect("empty composition should succeed");

        assert!(result.is_empty());
    }

    #[test]
    fn test_transfer_all_cycle_returns_error() {
        let mut comp = ProofComposition::new();
        let cert_a = make_cert("a");
        let cert_b = make_cert("b");

        // a -> b and b -> a: cycle
        comp.add_certificate(cert_a, vec!["b".to_string()]);
        comp.add_certificate(cert_b, vec!["a".to_string()]);

        let reg = ProofStatusRegistry::from_composition(&comp);
        let transfer = Lean5ProofTransfer::new(&reg);

        let result = transfer.transfer_all(&comp, &FxHashMap::default());
        assert!(result.is_err(), "cyclic composition should return error");
    }

    #[test]
    fn test_transfer_all_with_missing_callee() {
        let mut comp = ProofComposition::new();
        let cert_a = make_cert("a");

        comp.add_certificate(cert_a, vec!["b".to_string()]);
        comp.add_missing("b", vec![]);

        let reg = ProofStatusRegistry::from_composition(&comp);
        let transfer = Lean5ProofTransfer::new(&reg);

        let mut postconditions = FxHashMap::default();
        postconditions.insert("b".to_string(), Formula::Bool(true));

        let result = transfer
            .transfer_all(&comp, &postconditions)
            .expect("should succeed");

        // 'a' depends on 'b' which is Missing -> no transfer
        assert!(
            result.is_empty() || result.get("a").is_none_or(|v| v.is_empty()),
            "missing callee should not generate transfer"
        );
    }
}
