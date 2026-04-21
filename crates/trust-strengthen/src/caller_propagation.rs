// trust-strengthen/caller_propagation.rs: Caller propagation for pub API precondition strengthening
//
// When a precondition is inferred for a function F, propagate it to all callers
// so they know what to assert before calling F. Handles visibility-aware logic:
// - Private/pub(crate) functions: add inline VC at each call site
// - Pub functions: propagate precondition AND add #[requires] to F's signature
//
// Uses the CallGraph from trust-types to discover caller-callee relationships.
//
// Part of #144
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;

use trust_types::call_graph::{CallGraph, CallGraphEdge};

use crate::proposer::{Proposal, ProposalKind};
use trust_types::fx::FxHashSet;

/// The visibility of a function for purposes of precondition propagation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FnVisibility {
    /// Private to the module -- may add spec directly without caller propagation.
    Private,
    /// Visible within the crate -- propagate precondition as VC at call sites.
    PubCrate,
    /// Fully public API -- propagate to callers AND add `#[requires]` to signature.
    Public,
}

/// A call site where a precondition needs to be asserted before a function call.
#[derive(Debug, Clone)]
pub struct CallerObligation {
    /// Def path of the calling function.
    pub caller_path: String,
    /// Human-readable caller name.
    pub caller_name: String,
    /// Def path of the callee whose precondition must be satisfied.
    pub callee_path: String,
    /// The precondition spec body that must hold at the call site.
    pub precondition: String,
    /// The proposal generated for this caller.
    pub proposal: Proposal,
}

/// Result of propagating preconditions to callers.
#[derive(Debug, Clone)]
pub struct PropagationResult {
    /// New proposals generated for caller functions.
    pub caller_proposals: Vec<Proposal>,
    /// Obligations at each call site (for reporting).
    pub obligations: Vec<CallerObligation>,
    /// Functions that need re-verification after propagation.
    pub reverify_functions: Vec<String>,
    /// Signature-level additions for pub functions (function_path -> spec body).
    pub signature_specs: Vec<SignatureSpec>,
    /// Number of callers affected.
    pub callers_affected: usize,
}

/// A spec that should be added to a function's signature (for pub APIs).
#[derive(Debug, Clone, PartialEq)]
pub struct SignatureSpec {
    /// Def path of the function getting the signature spec.
    pub function_path: String,
    /// The spec body to add as `#[requires("...")]`.
    pub spec_body: String,
    /// Rationale for adding this spec.
    pub rationale: String,
}

/// Propagates inferred preconditions from callees to their callers.
///
/// Given a call graph and a set of precondition proposals, generates new
/// proposals at each call site to ensure the precondition is satisfied.
pub struct CallerPropagator<'a> {
    /// The call graph for the crate.
    graph: &'a CallGraph,
    /// Reverse index: callee def_path -> list of (caller def_path, edge).
    reverse_edges: FxHashMap<String, Vec<CallerInfo>>,
}

/// Information about a caller of a function.
#[derive(Debug, Clone)]
struct CallerInfo {
    /// Def path of the calling function.
    caller_path: String,
    /// Human-readable caller name (derived from def_path).
    caller_name: String,
    /// The original call edge.
    _edge: CallGraphEdge,
}

impl<'a> CallerPropagator<'a> {
    /// Create a new propagator from a call graph.
    ///
    /// Builds a reverse index from callee -> callers for efficient lookup.
    #[must_use]
    pub fn new(graph: &'a CallGraph) -> Self {
        let mut reverse_edges: FxHashMap<String, Vec<CallerInfo>> = FxHashMap::default();

        for edge in &graph.edges {
            // Resolve callee to a full def_path if possible
            let resolved_callee = resolve_callee(&graph.nodes, &edge.callee);
            let caller_name = extract_name(&edge.caller);

            reverse_edges
                .entry(resolved_callee)
                .or_default()
                .push(CallerInfo {
                    caller_path: edge.caller.clone(),
                    caller_name,
                    _edge: edge.clone(),
                });
        }

        Self {
            graph,
            reverse_edges,
        }
    }

    /// Find all callers of a given function by its def_path.
    ///
    /// Returns a list of (caller_def_path, caller_name) pairs.
    #[must_use]
    pub fn find_callers(&self, callee_path: &str) -> Vec<(String, String)> {
        // Try exact match first
        if let Some(callers) = self.reverse_edges.get(callee_path) {
            return callers
                .iter()
                .map(|c| (c.caller_path.clone(), c.caller_name.clone()))
                .collect();
        }

        // Try suffix match: look for keys that end with the callee_path
        let mut result = Vec::new();
        for (key, callers) in &self.reverse_edges {
            if key.ends_with(callee_path) || callee_path.ends_with(key.as_str()) {
                for caller in callers {
                    result.push((caller.caller_path.clone(), caller.caller_name.clone()));
                }
            }
        }
        result
    }

    /// Propagate precondition proposals to all callers.
    ///
    /// For each precondition proposal on a function:
    /// 1. Find all callers of that function
    /// 2. Generate a caller-side assertion proposal at each call site
    /// 3. If the function is public, also generate a signature-level `#[requires]` spec
    /// 4. Track which functions need re-verification
    #[must_use]
    pub fn propagate(&self, proposals: &[Proposal], visibility: &dyn Fn(&str) -> FnVisibility) -> PropagationResult {
        let mut caller_proposals = Vec::new();
        let mut obligations = Vec::new();
        let mut reverify_functions = Vec::new();
        let mut signature_specs = Vec::new();
        let mut seen_callers = FxHashSet::default();

        for proposal in proposals {
            // Only propagate preconditions
            let spec_body = match &proposal.kind {
                ProposalKind::AddPrecondition { spec_body } => spec_body.clone(),
                _ => continue,
            };

            let vis = visibility(&proposal.function_path);
            let callers = self.find_callers(&proposal.function_path);

            // For pub functions: add signature-level requires spec
            if vis == FnVisibility::Public {
                signature_specs.push(SignatureSpec {
                    function_path: proposal.function_path.clone(),
                    spec_body: spec_body.clone(),
                    rationale: format!(
                        "Pub API precondition: callers must ensure {} before calling {}",
                        spec_body, proposal.function_name,
                    ),
                });
            }

            // For pub and pub(crate): propagate to callers
            if vis == FnVisibility::Public || vis == FnVisibility::PubCrate {
                for (caller_path, caller_name) in &callers {
                    let caller_proposal = Proposal {
                        function_path: caller_path.clone(),
                        function_name: caller_name.clone(),
                        kind: ProposalKind::AddPrecondition {
                            spec_body: format!(
                                "caller must ensure: {} (required by {})",
                                spec_body, proposal.function_name,
                            ),
                        },
                        confidence: proposal.confidence * 0.9, // slightly lower confidence for propagated specs
                        rationale: format!(
                            "Propagated from {}: callee requires {}",
                            proposal.function_name, spec_body,
                        ),
                    };

                    let obligation = CallerObligation {
                        caller_path: caller_path.clone(),
                        caller_name: caller_name.clone(),
                        callee_path: proposal.function_path.clone(),
                        precondition: spec_body.clone(),
                        proposal: caller_proposal.clone(),
                    };

                    caller_proposals.push(caller_proposal);
                    obligations.push(obligation);

                    if seen_callers.insert(caller_path.clone()) {
                        reverify_functions.push(caller_path.clone());
                    }
                }
            }

            // Private functions: no propagation needed (spec added directly)
        }

        let callers_affected = seen_callers.len();

        PropagationResult {
            caller_proposals,
            obligations,
            reverify_functions,
            signature_specs,
            callers_affected,
        }
    }

    /// Propagate preconditions transitively through the call graph.
    ///
    /// After propagating preconditions from callees to callers, if any of those
    /// callers are themselves called by other functions, propagate further up.
    /// Stops at the given depth limit to prevent infinite loops.
    #[must_use]
    pub fn propagate_transitive(
        &self,
        proposals: &[Proposal],
        visibility: &dyn Fn(&str) -> FnVisibility,
        max_depth: usize,
    ) -> PropagationResult {
        let mut all_caller_proposals = Vec::new();
        let mut all_obligations = Vec::new();
        let mut all_reverify = Vec::new();
        let mut all_signature_specs = Vec::new();
        let mut seen_callers = FxHashSet::default();

        let mut current_proposals: Vec<Proposal> = proposals.to_vec();

        for _depth in 0..max_depth {
            let result = self.propagate(&current_proposals, visibility);
            if result.caller_proposals.is_empty() {
                break;
            }

            // Collect new caller proposals for the next depth level
            let mut next_proposals = Vec::new();
            for proposal in &result.caller_proposals {
                if seen_callers.insert(format!("{}:{}", proposal.function_path, proposal.rationale)) {
                    next_proposals.push(proposal.clone());
                }
            }

            all_caller_proposals.extend(result.caller_proposals);
            all_obligations.extend(result.obligations);
            all_signature_specs.extend(result.signature_specs);
            for func in &result.reverify_functions {
                if !all_reverify.contains(func) {
                    all_reverify.push(func.clone());
                }
            }

            if next_proposals.is_empty() {
                break;
            }
            current_proposals = next_proposals;
        }

        PropagationResult {
            callers_affected: all_reverify.len(),
            caller_proposals: all_caller_proposals,
            obligations: all_obligations,
            reverify_functions: all_reverify,
            signature_specs: all_signature_specs,
        }
    }

    /// Get the number of functions in the call graph.
    #[must_use]
    pub fn function_count(&self) -> usize {
        self.graph.nodes.len()
    }

    /// Get the number of call edges in the graph.
    #[must_use]
    pub fn edge_count(&self) -> usize {
        self.graph.edges.len()
    }
}

/// Resolve a callee name to a full def_path using the graph's nodes.
/// Falls back to the callee string itself if no match is found.
fn resolve_callee(nodes: &[trust_types::call_graph::CallGraphNode], callee: &str) -> String {
    // Exact match
    if nodes.iter().any(|n| n.def_path == callee) {
        return callee.to_string();
    }

    // Suffix match: find a node whose def_path ends with "::callee"
    let suffix = format!("::{callee}");
    for node in nodes {
        if node.def_path.ends_with(&suffix) {
            return node.def_path.clone();
        }
    }

    // No match -- use as-is
    callee.to_string()
}

/// Extract a short function name from a def_path.
/// "crate::module::function" -> "function"
fn extract_name(def_path: &str) -> String {
    def_path
        .rsplit("::")
        .next()
        .unwrap_or(def_path)
        .to_string()
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_types::call_graph::{CallGraph, CallGraphEdge, CallGraphNode};
    use trust_types::SourceSpan;

    fn span() -> SourceSpan {
        SourceSpan::default()
    }

    fn node(def_path: &str, is_public: bool) -> CallGraphNode {
        CallGraphNode {
            def_path: def_path.to_string(),
            name: extract_name(def_path),
            is_public,
            is_entry_point: false,
            span: span(),
        }
    }

    fn edge(caller: &str, callee: &str) -> CallGraphEdge {
        CallGraphEdge {
            caller: caller.to_string(),
            callee: callee.to_string(),
            call_site: span(),
        }
    }

    fn precondition_proposal(function_path: &str, spec: &str) -> Proposal {
        Proposal {
            function_path: function_path.to_string(),
            function_name: extract_name(function_path),
            kind: ProposalKind::AddPrecondition {
                spec_body: spec.to_string(),
            },
            confidence: 0.9,
            rationale: "test".to_string(),
        }
    }

    fn simple_graph() -> CallGraph {
        // main -> handler -> helper
        CallGraph {
            nodes: vec![
                node("crate::main", false),
                node("crate::handler", true),
                node("crate::helper", false),
            ],
            edges: vec![
                edge("crate::main", "crate::handler"),
                edge("crate::handler", "crate::helper"),
            ],
        }
    }

    fn visibility_for_simple(path: &str) -> FnVisibility {
        match path {
            "crate::handler" => FnVisibility::Public,
            "crate::helper" => FnVisibility::PubCrate,
            _ => FnVisibility::Private,
        }
    }

    // --- CallerPropagator construction ---

    #[test]
    fn test_new_builds_reverse_index() {
        let graph = simple_graph();
        let prop = CallerPropagator::new(&graph);
        assert_eq!(prop.function_count(), 3);
        assert_eq!(prop.edge_count(), 2);
    }

    #[test]
    fn test_new_empty_graph() {
        let graph = CallGraph::new();
        let prop = CallerPropagator::new(&graph);
        assert_eq!(prop.function_count(), 0);
        assert_eq!(prop.edge_count(), 0);
    }

    // --- find_callers ---

    #[test]
    fn test_find_callers_exact_match() {
        let graph = simple_graph();
        let prop = CallerPropagator::new(&graph);

        let callers = prop.find_callers("crate::handler");
        assert_eq!(callers.len(), 1);
        assert_eq!(callers[0].0, "crate::main");
    }

    #[test]
    fn test_find_callers_of_helper() {
        let graph = simple_graph();
        let prop = CallerPropagator::new(&graph);

        let callers = prop.find_callers("crate::helper");
        assert_eq!(callers.len(), 1);
        assert_eq!(callers[0].0, "crate::handler");
    }

    #[test]
    fn test_find_callers_no_callers() {
        let graph = simple_graph();
        let prop = CallerPropagator::new(&graph);

        let callers = prop.find_callers("crate::main");
        assert!(callers.is_empty(), "main has no callers");
    }

    #[test]
    fn test_find_callers_nonexistent() {
        let graph = simple_graph();
        let prop = CallerPropagator::new(&graph);

        let callers = prop.find_callers("crate::nonexistent");
        assert!(callers.is_empty());
    }

    #[test]
    fn test_find_callers_multiple_callers() {
        let graph = CallGraph {
            nodes: vec![
                node("crate::a", false),
                node("crate::b", false),
                node("crate::target", true),
            ],
            edges: vec![
                edge("crate::a", "crate::target"),
                edge("crate::b", "crate::target"),
            ],
        };
        let prop = CallerPropagator::new(&graph);

        let callers = prop.find_callers("crate::target");
        assert_eq!(callers.len(), 2);
        let caller_paths: Vec<&str> = callers.iter().map(|(p, _)| p.as_str()).collect();
        assert!(caller_paths.contains(&"crate::a"));
        assert!(caller_paths.contains(&"crate::b"));
    }

    // --- propagate ---

    #[test]
    fn test_propagate_precondition_to_caller() {
        let graph = simple_graph();
        let prop = CallerPropagator::new(&graph);

        let proposals = vec![precondition_proposal("crate::helper", "x != 0")];
        let result = prop.propagate(&proposals, &visibility_for_simple);

        assert_eq!(result.callers_affected, 1);
        assert_eq!(result.caller_proposals.len(), 1);
        assert_eq!(result.caller_proposals[0].function_path, "crate::handler");
        assert!(result.reverify_functions.contains(&"crate::handler".to_string()));
    }

    #[test]
    fn test_propagate_pub_function_gets_signature_spec() {
        let graph = simple_graph();
        let prop = CallerPropagator::new(&graph);

        let proposals = vec![precondition_proposal("crate::handler", "y > 0")];
        let result = prop.propagate(&proposals, &visibility_for_simple);

        // handler is public -- should get a signature spec
        assert_eq!(result.signature_specs.len(), 1);
        assert_eq!(result.signature_specs[0].function_path, "crate::handler");
        assert_eq!(result.signature_specs[0].spec_body, "y > 0");

        // Its caller (main) should get a caller proposal
        assert_eq!(result.caller_proposals.len(), 1);
        assert_eq!(result.caller_proposals[0].function_path, "crate::main");
    }

    #[test]
    fn test_propagate_pubcrate_no_signature_spec() {
        let graph = simple_graph();
        let prop = CallerPropagator::new(&graph);

        let proposals = vec![precondition_proposal("crate::helper", "z < 10")];
        let result = prop.propagate(&proposals, &visibility_for_simple);

        // helper is pub(crate) -- no signature spec, but caller gets proposal
        assert!(result.signature_specs.is_empty());
        assert_eq!(result.caller_proposals.len(), 1);
    }

    #[test]
    fn test_propagate_private_no_propagation() {
        let graph = simple_graph();
        let prop = CallerPropagator::new(&graph);

        let proposals = vec![precondition_proposal("crate::main", "n > 0")];
        let result = prop.propagate(&proposals, &visibility_for_simple);

        // main is private -- no propagation at all
        assert!(result.caller_proposals.is_empty());
        assert!(result.signature_specs.is_empty());
        assert_eq!(result.callers_affected, 0);
    }

    #[test]
    fn test_propagate_skips_non_precondition_proposals() {
        let graph = simple_graph();
        let prop = CallerPropagator::new(&graph);

        let proposals = vec![Proposal {
            function_path: "crate::handler".to_string(),
            function_name: "handler".to_string(),
            kind: ProposalKind::AddPostcondition {
                spec_body: "result > 0".to_string(),
            },
            confidence: 0.8,
            rationale: "test".to_string(),
        }];

        let result = prop.propagate(&proposals, &visibility_for_simple);
        assert!(result.caller_proposals.is_empty(), "only preconditions should be propagated");
    }

    #[test]
    fn test_propagate_confidence_reduction() {
        let graph = simple_graph();
        let prop = CallerPropagator::new(&graph);

        let proposals = vec![precondition_proposal("crate::handler", "y > 0")];
        let result = prop.propagate(&proposals, &visibility_for_simple);

        // Propagated proposals should have slightly lower confidence
        assert!(!result.caller_proposals.is_empty());
        let original_confidence = 0.9;
        let propagated_confidence = result.caller_proposals[0].confidence;
        assert!(
            propagated_confidence < original_confidence,
            "propagated confidence ({propagated_confidence}) should be less than original ({original_confidence})"
        );
        assert!(
            (propagated_confidence - original_confidence * 0.9).abs() < f64::EPSILON,
            "propagated confidence should be 90% of original"
        );
    }

    #[test]
    fn test_propagate_multiple_proposals() {
        let graph = CallGraph {
            nodes: vec![
                node("crate::caller_a", false),
                node("crate::caller_b", false),
                node("crate::target", true),
            ],
            edges: vec![
                edge("crate::caller_a", "crate::target"),
                edge("crate::caller_b", "crate::target"),
            ],
        };
        let prop = CallerPropagator::new(&graph);

        let vis = |path: &str| -> FnVisibility {
            if path == "crate::target" { FnVisibility::Public } else { FnVisibility::Private }
        };

        let proposals = vec![precondition_proposal("crate::target", "x >= 0")];
        let result = prop.propagate(&proposals, &vis);

        // Both callers should get proposals
        assert_eq!(result.caller_proposals.len(), 2);
        assert_eq!(result.callers_affected, 2);
        assert_eq!(result.reverify_functions.len(), 2);
    }

    #[test]
    fn test_propagate_empty_proposals() {
        let graph = simple_graph();
        let prop = CallerPropagator::new(&graph);

        let result = prop.propagate(&[], &visibility_for_simple);
        assert!(result.caller_proposals.is_empty());
        assert_eq!(result.callers_affected, 0);
    }

    #[test]
    fn test_propagate_empty_graph() {
        let graph = CallGraph::new();
        let prop = CallerPropagator::new(&graph);

        let proposals = vec![precondition_proposal("crate::func", "x > 0")];
        let vis = |_: &str| FnVisibility::Public;
        let result = prop.propagate(&proposals, &vis);

        // Public function with no callers: still gets signature spec
        assert_eq!(result.signature_specs.len(), 1);
        assert!(result.caller_proposals.is_empty());
    }

    // --- propagate_transitive ---

    #[test]
    fn test_propagate_transitive_two_levels() {
        // a -> b -> c, precondition on c should reach a via b
        let graph = CallGraph {
            nodes: vec![
                node("crate::a", false),
                node("crate::b", false),
                node("crate::c", false),
            ],
            edges: vec![
                edge("crate::a", "crate::b"),
                edge("crate::b", "crate::c"),
            ],
        };
        let prop = CallerPropagator::new(&graph);

        let vis = |_: &str| FnVisibility::PubCrate;
        let proposals = vec![precondition_proposal("crate::c", "n > 0")];
        let result = prop.propagate_transitive(&proposals, &vis, 3);

        // Both b (direct caller) and a (transitive caller) should be affected
        assert!(result.reverify_functions.contains(&"crate::b".to_string()));
        assert!(result.reverify_functions.contains(&"crate::a".to_string()));
        assert_eq!(result.callers_affected, 2);
    }

    #[test]
    fn test_propagate_transitive_respects_depth_limit() {
        // a -> b -> c -> d, with depth limit 1 starting from d
        let graph = CallGraph {
            nodes: vec![
                node("crate::a", false),
                node("crate::b", false),
                node("crate::c", false),
                node("crate::d", false),
            ],
            edges: vec![
                edge("crate::a", "crate::b"),
                edge("crate::b", "crate::c"),
                edge("crate::c", "crate::d"),
            ],
        };
        let prop = CallerPropagator::new(&graph);

        let vis = |_: &str| FnVisibility::PubCrate;
        let proposals = vec![precondition_proposal("crate::d", "x != 0")];
        let result = prop.propagate_transitive(&proposals, &vis, 1);

        // Only c (direct caller) should be affected with depth 1
        assert!(result.reverify_functions.contains(&"crate::c".to_string()));
        assert_eq!(result.callers_affected, 1);
    }

    #[test]
    fn test_propagate_transitive_handles_cycles() {
        // a -> b -> a (cycle)
        let graph = CallGraph {
            nodes: vec![
                node("crate::a", false),
                node("crate::b", false),
            ],
            edges: vec![
                edge("crate::a", "crate::b"),
                edge("crate::b", "crate::a"),
            ],
        };
        let prop = CallerPropagator::new(&graph);

        let vis = |_: &str| FnVisibility::PubCrate;
        let proposals = vec![precondition_proposal("crate::b", "x > 0")];
        // Should terminate and not loop infinitely
        let result = prop.propagate_transitive(&proposals, &vis, 10);

        assert!(result.reverify_functions.contains(&"crate::a".to_string()));
        // cycle detection stops further propagation
    }

    #[test]
    fn test_propagate_transitive_zero_depth() {
        let graph = simple_graph();
        let prop = CallerPropagator::new(&graph);

        let proposals = vec![precondition_proposal("crate::helper", "x != 0")];
        let result = prop.propagate_transitive(&proposals, &visibility_for_simple, 0);

        assert!(result.caller_proposals.is_empty(), "depth 0 should produce no propagation");
    }

    // --- CallerObligation ---

    #[test]
    fn test_obligation_contains_correct_info() {
        let graph = simple_graph();
        let prop = CallerPropagator::new(&graph);

        let proposals = vec![precondition_proposal("crate::helper", "divisor != 0")];
        let result = prop.propagate(&proposals, &visibility_for_simple);

        assert_eq!(result.obligations.len(), 1);
        let obligation = &result.obligations[0];
        assert_eq!(obligation.caller_path, "crate::handler");
        assert_eq!(obligation.callee_path, "crate::helper");
        assert_eq!(obligation.precondition, "divisor != 0");
    }

    // --- extract_name ---

    #[test]
    fn test_extract_name_qualified() {
        assert_eq!(extract_name("crate::module::function"), "function");
    }

    #[test]
    fn test_extract_name_simple() {
        assert_eq!(extract_name("function"), "function");
    }

    #[test]
    fn test_extract_name_nested() {
        assert_eq!(extract_name("crate::a::b::c::deep"), "deep");
    }

    // --- FnVisibility ---

    #[test]
    fn test_visibility_enum_equality() {
        assert_eq!(FnVisibility::Public, FnVisibility::Public);
        assert_ne!(FnVisibility::Public, FnVisibility::Private);
        assert_ne!(FnVisibility::PubCrate, FnVisibility::Private);
    }

    // --- Integration: full workflow ---

    #[test]
    fn test_full_propagation_workflow() {
        // Build a realistic call graph:
        // main (entry) -> api::handler (pub) -> util::validate (pub(crate)) -> util::check (private)
        let graph = CallGraph {
            nodes: vec![
                {
                    let mut n = node("crate::main", false);
                    n.is_entry_point = true;
                    n
                },
                node("crate::api::handler", true),
                node("crate::util::validate", false),
                node("crate::util::check", false),
            ],
            edges: vec![
                edge("crate::main", "crate::api::handler"),
                edge("crate::api::handler", "crate::util::validate"),
                edge("crate::util::validate", "crate::util::check"),
            ],
        };
        let prop = CallerPropagator::new(&graph);

        let vis = |path: &str| -> FnVisibility {
            match path {
                "crate::api::handler" => FnVisibility::Public,
                "crate::util::validate" => FnVisibility::PubCrate,
                _ => FnVisibility::Private,
            }
        };

        // Infer a precondition on validate
        let proposals = vec![precondition_proposal("crate::util::validate", "input.len() > 0")];
        let result = prop.propagate(&proposals, &vis);

        // validate is pub(crate): no signature spec, but its caller (handler) gets a proposal
        assert!(result.signature_specs.is_empty());
        assert_eq!(result.caller_proposals.len(), 1);
        assert_eq!(result.caller_proposals[0].function_path, "crate::api::handler");
        assert_eq!(result.reverify_functions.len(), 1);
        assert_eq!(result.reverify_functions[0], "crate::api::handler");
    }

    #[test]
    fn test_full_transitive_propagation_workflow() {
        // Same graph as above, but with transitive propagation
        let graph = CallGraph {
            nodes: vec![
                {
                    let mut n = node("crate::main", false);
                    n.is_entry_point = true;
                    n
                },
                node("crate::api::handler", true),
                node("crate::util::validate", false),
            ],
            edges: vec![
                edge("crate::main", "crate::api::handler"),
                edge("crate::api::handler", "crate::util::validate"),
            ],
        };
        let prop = CallerPropagator::new(&graph);

        let vis = |path: &str| -> FnVisibility {
            match path {
                "crate::api::handler" => FnVisibility::Public,
                "crate::util::validate" => FnVisibility::PubCrate,
                _ => FnVisibility::Private,
            }
        };

        // Infer precondition on validate, propagate transitively
        let proposals = vec![precondition_proposal("crate::util::validate", "data.is_valid()")];
        let result = prop.propagate_transitive(&proposals, &vis, 5);

        // validate -> handler (pub, gets signature spec too) -> main
        // handler should be in reverify
        assert!(result.reverify_functions.contains(&"crate::api::handler".to_string()));
        // With transitive, main should also be reached since handler is pub
        assert!(result.reverify_functions.contains(&"crate::main".to_string()));
    }
}
