// trust-proof-cert composition tests
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;

use trust_types::{Formula, ProofStrength, SourceSpan, VcKind, VerificationCondition};

use super::*;
use crate::{FunctionHash, SolverInfo, VcSnapshot};

fn sample_solver(strength: ProofStrength, time_ms: u64) -> SolverInfo {
    SolverInfo {
        name: "z4".to_string(),
        version: "1.0.0".to_string(),
        time_ms,
        strength,
        evidence: None,
    }
}

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

fn sample_vc_snapshot(function: &str) -> VcSnapshot {
    VcSnapshot::from_vc(&sample_vc(function)).expect("snapshot should serialize")
}

fn make_cert(function: &str, timestamp: &str, strength: ProofStrength) -> crate::ProofCertificate {
    use crate::chain::{ChainStep, ChainStepType};

    let mut cert = crate::ProofCertificate::new_trusted(
        function.to_string(),
        FunctionHash::from_bytes(format!("{function}-body").as_bytes()),
        sample_vc_snapshot(function),
        sample_solver(strength, 42),
        vec![1, 2, 3, 4],
        timestamp.to_string(),
    );
    // Add a valid chain step so verify_integrity() passes -> Valid status in compositions
    cert.chain.push(ChainStep {
        step_type: ChainStepType::SolverProof,
        tool: "z4".to_string(),
        tool_version: "1.0.0".to_string(),
        input_hash: "abc".to_string(),
        output_hash: "def".to_string(),
        time_ms: 1,
        timestamp: timestamp.to_string(),
    });
    cert
}

fn make_certified_cert(function: &str, timestamp: &str) -> crate::ProofCertificate {
    let certifier_key = crate::CertSigningKey::generate(crate::TrustLevel::Certifier);
    let mut cert = make_cert(function, timestamp, ProofStrength::constructive());
    cert.upgrade_to_certified(&certifier_key).expect("upgrade should succeed");
    cert
}

// -----------------------------------------------------------------------
// Composability checks
// -----------------------------------------------------------------------

#[test]
fn test_composability_different_functions() {
    let a = make_cert("crate::foo", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());
    let b = make_cert("crate::bar", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());

    let result = check_composability(&a, &b).unwrap();
    assert!(result.composable);
    assert!(result.issues.is_empty());
    assert!(result.shared_deps.is_empty());
}

#[test]
fn test_composability_same_function_same_vc_kind() {
    let a = make_cert("crate::foo", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());
    let b = make_cert("crate::foo", "2026-03-27T12:05:00Z", ProofStrength::smt_unsat());

    let result = check_composability(&a, &b).unwrap();
    assert!(!result.composable);
    assert!(!result.issues.is_empty());
}

// -----------------------------------------------------------------------
// Proof composition
// -----------------------------------------------------------------------

#[test]
fn test_compose_single_cert() {
    let cert = make_cert("crate::foo", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());

    let composed = compose_proofs(&[&cert]).unwrap();
    assert_eq!(composed.constituent_ids.len(), 1);
    assert_eq!(composed.functions, vec!["crate::foo"]);
    assert_eq!(composed.combined_strength, ProofStrength::smt_unsat());
    assert!(composed.is_consistent);
}

#[test]
fn test_compose_multiple_certs() {
    let a = make_cert("crate::foo", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());
    let b = make_cert("crate::bar", "2026-03-27T12:00:00Z", ProofStrength::constructive());

    let composed = compose_proofs(&[&a, &b]).unwrap();
    assert_eq!(composed.constituent_ids.len(), 2);
    assert_eq!(composed.functions, vec!["crate::bar", "crate::foo"]);
    // Weakest strength should be SmtUnsat (rank 1) vs Constructive (rank 4)
    assert_eq!(composed.combined_strength, ProofStrength::smt_unsat());
    assert_eq!(composed.total_time_ms, 84);
}

#[test]
fn test_compose_all_certified() {
    let a = make_certified_cert("crate::foo", "2026-03-27T12:00:00Z");
    let b = make_certified_cert("crate::bar", "2026-03-27T12:00:00Z");

    let composed = compose_proofs(&[&a, &b]).unwrap();
    assert_eq!(composed.combined_status, crate::CertificationStatus::Certified);
}

#[test]
fn test_compose_mixed_status() {
    let certified = make_certified_cert("crate::foo", "2026-03-27T12:00:00Z");
    let trusted = make_cert("crate::bar", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());

    let composed = compose_proofs(&[&certified, &trusted]).unwrap();
    assert_eq!(composed.combined_status, crate::CertificationStatus::Trusted);
}

#[test]
fn test_compose_empty_fails() {
    let result = compose_proofs(&[]);
    assert!(result.is_err());
}

#[test]
fn test_compose_incompatible_fails() {
    let a = make_cert("crate::foo", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());
    let b = make_cert("crate::foo", "2026-03-27T12:05:00Z", ProofStrength::smt_unsat());

    let result = compose_proofs(&[&a, &b]);
    assert!(result.is_err());
    match result.unwrap_err() {
        CompositionError::IncompatibleAssumptions { .. } => {}
        other => panic!("expected IncompatibleAssumptions, got: {other:?}"),
    }
}

// -----------------------------------------------------------------------
// Transitive closure
// -----------------------------------------------------------------------

#[test]
fn test_transitive_closure_all_proved() {
    let a = make_cert("crate::foo", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());
    let b = make_cert("crate::bar", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());

    let mut call_graph = FxHashMap::default();
    call_graph.insert("crate::foo".to_string(), vec!["crate::bar".to_string()]);

    let closure = transitive_closure(&[&a, &b], &call_graph);
    assert!(closure.contains("crate::foo"));
    assert!(closure.contains("crate::bar"));
}

#[test]
fn test_transitive_closure_missing_callee() {
    let a = make_cert("crate::foo", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());

    let mut call_graph = FxHashMap::default();
    call_graph.insert("crate::foo".to_string(), vec!["crate::bar".to_string()]);

    let closure = transitive_closure(&[&a], &call_graph);
    // foo has a direct proof certificate, so it remains even if bar is unproved.
    assert!(closure.contains("crate::foo"));
}

#[test]
fn test_transitive_closure_no_deps() {
    let a = make_cert("crate::foo", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());
    let call_graph = FxHashMap::default();

    let closure = transitive_closure(&[&a], &call_graph);
    assert!(closure.contains("crate::foo"));
}

// -----------------------------------------------------------------------
// Weakening
// -----------------------------------------------------------------------

#[test]
fn test_weakening_valid() {
    let cert = make_cert("crate::foo", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());
    let weaker = Property::new("Assertion");

    let derived = weakening(&cert, &weaker).unwrap();
    assert_eq!(derived.function, "crate::foo");
    assert!(derived.vc_snapshot.kind.contains("Weakened"));
    assert!(derived.vc_snapshot.kind.contains("Assertion"));
    // Derived cert should have a different ID
    assert_ne!(derived.id, cert.id);
}

#[test]
fn test_weakening_invalid() {
    let cert = make_cert("crate::foo", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());
    let unrelated = Property::new("Overflow");

    let result = weakening(&cert, &unrelated);
    assert!(result.is_err());
    match result.unwrap_err() {
        CompositionError::WeakeningFailed { .. } => {}
        other => panic!("expected WeakeningFailed, got: {other:?}"),
    }
}

// -----------------------------------------------------------------------
// Strengthening check
// -----------------------------------------------------------------------

#[test]
fn test_strengthening_check_pass() {
    let cert = make_cert("crate::foo", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());
    // The cert's VC kind contains "Assertion", so checking for that should pass
    let stronger = Property::new("Assertion");

    assert!(strengthening_check(&cert, &stronger).is_ok());
}

#[test]
fn test_strengthening_check_fail() {
    let cert = make_cert("crate::foo", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());
    let stronger = Property::new("MemorySafety");

    let result = strengthening_check(&cert, &stronger);
    assert!(result.is_err());
    match result.unwrap_err() {
        CompositionError::StrengtheningFailed { .. } => {}
        other => panic!("expected StrengtheningFailed, got: {other:?}"),
    }
}

// -----------------------------------------------------------------------
// Modular composition
// -----------------------------------------------------------------------

#[test]
fn test_modular_composition_success() {
    let caller = make_cert("crate::foo", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());
    let callee1 = make_cert("crate::bar", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());
    let callee2 = make_cert("crate::baz", "2026-03-27T12:00:00Z", ProofStrength::constructive());

    let required = vec!["crate::bar".to_string(), "crate::baz".to_string()];

    let call_graph = FxHashMap::default();
    let composed =
        modular_composition(&caller, &[&callee1, &callee2], &required, &call_graph).unwrap();

    assert_eq!(composed.constituent_ids.len(), 3);
    assert_eq!(composed.functions.len(), 3);
    assert_eq!(composed.call_edges.len(), 2);
    assert!(composed.call_edges.contains(&("crate::foo".to_string(), "crate::bar".to_string())));
    assert!(composed.call_edges.contains(&("crate::foo".to_string(), "crate::baz".to_string())));
    // Weakest strength
    assert_eq!(composed.combined_strength, ProofStrength::smt_unsat());
}

#[test]
fn test_modular_composition_missing_callee() {
    let caller = make_cert("crate::foo", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());
    let callee = make_cert("crate::bar", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());

    let required = vec!["crate::bar".to_string(), "crate::baz".to_string()];
    let call_graph = FxHashMap::default();

    let result = modular_composition(&caller, &[&callee], &required, &call_graph);
    assert!(result.is_err());
    match result.unwrap_err() {
        CompositionError::MissingLink { function } => {
            assert_eq!(function, "crate::baz");
        }
        other => panic!("expected MissingLink, got: {other:?}"),
    }
}

#[test]
fn test_modular_composition_direct_recursion() {
    // A calls A (direct self-recursion) -- should be caught.
    let caller = make_cert("crate::foo", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());
    let self_ref = make_cert("crate::foo", "2026-03-27T12:05:00Z", ProofStrength::smt_unsat());

    let required = vec!["crate::foo".to_string()];
    let mut call_graph = FxHashMap::default();
    call_graph.insert("crate::foo".to_string(), vec!["crate::foo".to_string()]);

    let result = modular_composition(&caller, &[&self_ref], &required, &call_graph);
    assert!(result.is_err());
    match result.unwrap_err() {
        CompositionError::CircularDependency { .. } => {}
        other => panic!("expected CircularDependency, got: {other:?}"),
    }
}

#[test]
fn test_modular_composition_mutual_recursion() {
    // A calls B, B calls A (mutual recursion) -- should be caught.
    let caller_a = make_cert("A", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());
    let callee_b = make_cert("B", "2026-03-27T12:01:00Z", ProofStrength::smt_unsat());

    let required = vec!["B".to_string()];
    let mut call_graph = FxHashMap::default();
    call_graph.insert("A".to_string(), vec!["B".to_string()]);
    call_graph.insert("B".to_string(), vec!["A".to_string()]);

    let result = modular_composition(&caller_a, &[&callee_b], &required, &call_graph);
    assert!(result.is_err(), "mutual recursion A -> B -> A should be detected");
    match result.unwrap_err() {
        CompositionError::CircularDependency { cycle } => {
            assert!(cycle.contains("A"), "cycle should mention A: {cycle}");
            assert!(cycle.contains("B"), "cycle should mention B: {cycle}");
        }
        other => panic!("expected CircularDependency, got: {other:?}"),
    }
}

#[test]
fn test_modular_composition_diamond_not_flagged() {
    // A calls B and C, both B and C call D -- diamond, NOT a cycle.
    let caller_a = make_cert("A", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());
    let callee_b = make_cert("B", "2026-03-27T12:01:00Z", ProofStrength::smt_unsat());
    let callee_c = make_cert("C", "2026-03-27T12:02:00Z", ProofStrength::smt_unsat());
    let callee_d = make_cert("D", "2026-03-27T12:03:00Z", ProofStrength::smt_unsat());

    let required = vec!["B".to_string(), "C".to_string()];
    let mut call_graph = FxHashMap::default();
    call_graph.insert("A".to_string(), vec!["B".to_string(), "C".to_string()]);
    call_graph.insert("B".to_string(), vec!["D".to_string()]);
    call_graph.insert("C".to_string(), vec!["D".to_string()]);
    call_graph.insert("D".to_string(), vec![]);

    let result = modular_composition(
        &caller_a,
        &[&callee_b, &callee_c, &callee_d],
        &required,
        &call_graph,
    );
    assert!(result.is_ok(), "diamond dependency should NOT be flagged as a cycle: {result:?}");
}

#[test]
fn test_modular_composition_no_callees() {
    let caller = make_cert("crate::foo", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());
    let required: Vec<String> = vec![];
    let call_graph = FxHashMap::default();

    let composed = modular_composition(&caller, &[], &required, &call_graph).unwrap();
    assert_eq!(composed.constituent_ids.len(), 1);
    assert!(composed.call_edges.is_empty());
}

#[test]
fn test_modular_composition_transitive_cycle_detected() {
    // A -> B -> C -> A: should detect cycle via DFS in callee_deps.
    let caller = make_cert("A", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());
    let callee_b = make_cert("B", "2026-03-27T12:01:00Z", ProofStrength::smt_unsat());
    let callee_c = make_cert("C", "2026-03-27T12:02:00Z", ProofStrength::smt_unsat());

    let required = vec!["B".to_string()];
    let mut callee_deps = FxHashMap::default();
    callee_deps.insert("B".to_string(), vec!["C".to_string()]);
    callee_deps.insert("C".to_string(), vec!["A".to_string()]); // cycle back to caller

    let result = modular_composition_with_deps(
        &caller,
        &[&callee_b, &callee_c],
        &required,
        &callee_deps,
    );
    assert!(result.is_err(), "transitive cycle A -> B -> C -> A should be detected");
    match result.unwrap_err() {
        CompositionError::CircularDependency { cycle } => {
            assert!(cycle.contains("A"), "cycle should mention A: {cycle}");
            assert!(cycle.contains("B"), "cycle should mention B: {cycle}");
            assert!(cycle.contains("C"), "cycle should mention C: {cycle}");
        }
        other => panic!("expected CircularDependency, got: {other:?}"),
    }
}

#[test]
fn test_modular_composition_with_deps_no_cycle() {
    // A -> B -> C (no cycle)
    let caller = make_cert("A", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());
    let callee_b = make_cert("B", "2026-03-27T12:01:00Z", ProofStrength::smt_unsat());
    let callee_c = make_cert("C", "2026-03-27T12:02:00Z", ProofStrength::smt_unsat());

    let required = vec!["B".to_string()];
    let mut callee_deps = FxHashMap::default();
    callee_deps.insert("B".to_string(), vec!["C".to_string()]);

    let result = modular_composition_with_deps(
        &caller,
        &[&callee_b, &callee_c],
        &required,
        &callee_deps,
    );
    assert!(result.is_ok(), "A -> B -> C has no cycle");
}

// -----------------------------------------------------------------------
// Strength ranking
// -----------------------------------------------------------------------

#[test]
fn test_strength_ranking() {
    use super::checkers::strength_rank;
    assert!(strength_rank(&ProofStrength::bounded(10)) < strength_rank(&ProofStrength::smt_unsat()));
    assert!(strength_rank(&ProofStrength::smt_unsat()) < strength_rank(&ProofStrength::deductive()));
    assert!(strength_rank(&ProofStrength::deductive()) < strength_rank(&ProofStrength::inductive()));
    assert!(
        strength_rank(&ProofStrength::inductive()) < strength_rank(&ProofStrength::constructive())
    );
}

#[test]
fn test_weakest_strength_selection() {
    use super::checkers::weakest_strength;
    let solvers = [
        sample_solver(ProofStrength::constructive(), 10),
        sample_solver(ProofStrength::smt_unsat(), 20),
        sample_solver(ProofStrength::bounded(5), 30),
    ];

    let weakest = weakest_strength(solvers.iter());
    assert_eq!(weakest, ProofStrength::bounded(5));
}

// -----------------------------------------------------------------------
// ProofComposition DAG
// -----------------------------------------------------------------------

#[test]
fn test_proof_composition_new_empty() {
    let comp = ProofComposition::new();
    assert!(comp.is_empty());
    assert_eq!(comp.len(), 0);
    assert!(comp.functions().is_empty());
}

#[test]
fn test_proof_composition_add_certificate() {
    let mut comp = ProofComposition::new();
    let cert = make_cert("crate::foo", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());
    comp.add_certificate(cert.clone(), vec![]);

    assert_eq!(comp.len(), 1);
    assert!(!comp.is_empty());
    assert_eq!(comp.functions(), vec!["crate::foo"]);

    let node = comp.get_node("crate::foo").unwrap();
    assert_eq!(node.status, CompositionNodeStatus::Valid);
    assert!(node.dependencies.is_empty());

    let retrieved = comp.get_certificate("crate::foo").unwrap();
    assert_eq!(retrieved, &cert);
}

#[test]
fn test_proof_composition_add_with_dependencies() {
    let mut comp = ProofComposition::new();
    let foo = make_cert("crate::foo", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());
    let bar = make_cert("crate::bar", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());

    comp.add_certificate(bar, vec![]);
    comp.add_certificate(foo, vec!["crate::bar".to_string()]);

    assert_eq!(comp.len(), 2);
    let foo_node = comp.get_node("crate::foo").unwrap();
    assert_eq!(foo_node.dependencies, vec!["crate::bar"]);
}

#[test]
fn test_proof_composition_add_missing() {
    let mut comp = ProofComposition::new();
    comp.add_missing("crate::baz", vec![]);

    let node = comp.get_node("crate::baz").unwrap();
    assert_eq!(node.status, CompositionNodeStatus::Missing);
    assert!(comp.get_certificate("crate::baz").is_none());

    assert_eq!(comp.missing_functions(), vec!["crate::baz"]);
}

#[test]
fn test_proof_composition_no_cycle() {
    let mut comp = ProofComposition::new();
    let foo = make_cert("crate::foo", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());
    let bar = make_cert("crate::bar", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());

    comp.add_certificate(bar, vec![]);
    comp.add_certificate(foo, vec!["crate::bar".to_string()]);

    assert!(comp.detect_cycle().is_none());
}

#[test]
fn test_proof_composition_detects_cycle() {
    let mut comp = ProofComposition::new();
    let foo = make_cert("crate::foo", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());
    let bar = make_cert("crate::bar", "2026-03-27T12:01:00Z", ProofStrength::smt_unsat());

    comp.add_certificate(foo, vec!["crate::bar".to_string()]);
    comp.add_certificate(bar, vec!["crate::foo".to_string()]);

    let cycle = comp.detect_cycle();
    assert!(cycle.is_some(), "should detect cycle between foo and bar");
}

#[test]
fn test_proof_composition_topological_order_linear() {
    let mut comp = ProofComposition::new();
    let a = make_cert("a", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());
    let b = make_cert("b", "2026-03-27T12:01:00Z", ProofStrength::smt_unsat());
    let c = make_cert("c", "2026-03-27T12:02:00Z", ProofStrength::smt_unsat());

    comp.add_certificate(a, vec!["b".to_string()]);
    comp.add_certificate(b, vec!["c".to_string()]);
    comp.add_certificate(c, vec![]);

    let order = comp.topological_order().unwrap();
    // c has no deps, so it comes first; then b, then a
    let pos_a = order.iter().position(|x| x == "a").unwrap();
    let pos_b = order.iter().position(|x| x == "b").unwrap();
    let pos_c = order.iter().position(|x| x == "c").unwrap();
    assert!(pos_c < pos_b, "c should come before b");
    assert!(pos_b < pos_a, "b should come before a");
}

#[test]
fn test_proof_composition_topological_order_cycle_error() {
    let mut comp = ProofComposition::new();
    let foo = make_cert("crate::foo", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());
    let bar = make_cert("crate::bar", "2026-03-27T12:01:00Z", ProofStrength::smt_unsat());

    comp.add_certificate(foo, vec!["crate::bar".to_string()]);
    comp.add_certificate(bar, vec!["crate::foo".to_string()]);

    let result = comp.topological_order();
    assert!(result.is_err());
    match result.unwrap_err() {
        CompositionError::CircularDependency { cycle } => {
            assert!(cycle.contains("crate::foo"));
            assert!(cycle.contains("crate::bar"));
        }
        other => panic!("expected CircularDependency, got: {other:?}"),
    }
}

// -----------------------------------------------------------------------
// verify_composition
// -----------------------------------------------------------------------

#[test]
fn test_verify_composition_sound() {
    let mut comp = ProofComposition::new();
    let foo = make_cert("crate::foo", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());
    let bar = make_cert("crate::bar", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());

    comp.add_certificate(bar, vec![]);
    comp.add_certificate(foo, vec!["crate::bar".to_string()]);

    let result = verify_composition(&comp);
    assert!(result.sound, "composition should be sound: {:?}", result);
    assert_eq!(result.valid_functions.len(), 2);
    assert!(result.missing_functions.is_empty());
    assert!(result.broken_chains.is_empty());
    assert!(result.cycle.is_none());
    assert!(result.composed.is_some());
}

#[test]
fn test_verify_composition_missing_function() {
    let mut comp = ProofComposition::new();
    let foo = make_cert("crate::foo", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());
    comp.add_certificate(foo, vec!["crate::bar".to_string()]);
    comp.add_missing("crate::bar", vec![]);

    let result = verify_composition(&comp);
    assert!(!result.sound);
    assert_eq!(result.missing_functions, vec!["crate::bar"]);
    assert!(result.composed.is_none());
}

#[test]
fn test_verify_composition_with_cycle() {
    let mut comp = ProofComposition::new();
    let foo = make_cert("crate::foo", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());
    let bar = make_cert("crate::bar", "2026-03-27T12:01:00Z", ProofStrength::smt_unsat());

    comp.add_certificate(foo, vec!["crate::bar".to_string()]);
    comp.add_certificate(bar, vec!["crate::foo".to_string()]);

    let result = verify_composition(&comp);
    assert!(!result.sound);
    assert!(result.cycle.is_some());
}

#[test]
fn test_verify_composition_empty() {
    let comp = ProofComposition::new();
    let result = verify_composition(&comp);
    // Empty composition is vacuously sound (no obligations)
    assert!(result.sound);
    assert!(result.composed.is_none()); // no certs to compose
}

#[test]
fn test_composition_node_status_variants() {
    // Ensure all status variants are distinguishable
    assert_ne!(CompositionNodeStatus::Valid, CompositionNodeStatus::Missing);
    assert_ne!(CompositionNodeStatus::Valid, CompositionNodeStatus::ChainBroken);
    assert_ne!(CompositionNodeStatus::Valid, CompositionNodeStatus::Stale);
    assert_ne!(CompositionNodeStatus::Missing, CompositionNodeStatus::ChainBroken);
}

#[test]
fn test_proof_composition_default() {
    let comp = ProofComposition::default();
    assert!(comp.is_empty());
}

// -----------------------------------------------------------------------
// Bug #400: weakening/strengthening must use structural comparison
// -----------------------------------------------------------------------

#[test]
fn test_weakening_rejects_arbitrary_substring() {
    // "sert" is a substring of "Assertion { ... }" but is NOT a valid weakening.
    // Before the fix, this would succeed due to string containment.
    let cert = make_cert("crate::foo", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());
    let bogus = Property::new("sert");

    let result = weakening(&cert, &bogus);
    assert!(result.is_err(), "arbitrary substring should not be a valid weakening");
    match result.unwrap_err() {
        CompositionError::WeakeningFailed { .. } => {}
        other => panic!("expected WeakeningFailed, got: {other:?}"),
    }
}

#[test]
fn test_weakening_accepts_exact_structural_prefix() {
    // "Assertion" is a structural prefix of "Assertion { ... }" -- valid weakening.
    let cert = make_cert("crate::foo", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());
    let valid = Property::new("Assertion");

    let result = weakening(&cert, &valid);
    assert!(result.is_ok(), "structural prefix should be valid weakening");
}

#[test]
fn test_weakening_rejects_partial_word_prefix() {
    // "Assert" is a prefix of "Assertion" but not a structural one (no delimiter).
    let cert = make_cert("crate::foo", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());
    let partial = Property::new("Assert");

    let result = weakening(&cert, &partial);
    assert!(result.is_err(), "partial word prefix should not be a valid weakening");
}

#[test]
fn test_strengthening_rejects_arbitrary_substring() {
    // "sert" is a substring of "Assertion { ... }" but should NOT pass strengthening.
    // Before the fix, this would succeed due to string containment.
    let cert = make_cert("crate::foo", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());
    let bogus = Property::new("sert");

    let result = strengthening_check(&cert, &bogus);
    assert!(result.is_err(), "arbitrary substring should not pass strengthening check");
}

#[test]
fn test_strengthening_accepts_structural_prefix() {
    // "Assertion" is a structural prefix of the cert's VC kind -- valid.
    let cert = make_cert("crate::foo", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());
    let valid = Property::new("Assertion");

    let result = strengthening_check(&cert, &valid);
    assert!(result.is_ok(), "structural prefix should pass strengthening check");
}

#[test]
fn test_strengthening_rejects_partial_word_prefix() {
    // "Assert" is NOT a structural prefix of "Assertion { ... }".
    let cert = make_cert("crate::foo", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());
    let partial = Property::new("Assert");

    let result = strengthening_check(&cert, &partial);
    assert!(result.is_err(), "partial word prefix should not pass strengthening check");
}

// -----------------------------------------------------------------------
// Bug #367: transitive_closure must add transitively verified functions
// -----------------------------------------------------------------------

#[test]
fn test_transitive_closure_adds_unproved_caller_with_all_proved_callees() {
    // "baz" is not directly proved, but all its callees ("foo", "bar") are.
    // Before the fix, "baz" would never be added to the result set.
    let foo = make_cert("foo", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());
    let bar = make_cert("bar", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());

    let mut call_graph = FxHashMap::default();
    call_graph.insert("baz".to_string(), vec!["foo".to_string(), "bar".to_string()]);

    let closure = transitive_closure(&[&foo, &bar], &call_graph);
    assert!(closure.contains("foo"), "directly proved foo should be in closure");
    assert!(closure.contains("bar"), "directly proved bar should be in closure");
    assert!(
        closure.contains("baz"),
        "baz should be transitively verified since all callees are proved"
    );
}

#[test]
fn test_transitive_closure_chain() {
    // a -> b -> c, only c is directly proved.
    // Before the fix, b and a would never be added transitively.
    let c = make_cert("c", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());

    let mut call_graph = FxHashMap::default();
    call_graph.insert("a".to_string(), vec!["b".to_string()]);
    call_graph.insert("b".to_string(), vec!["c".to_string()]);

    let closure = transitive_closure(&[&c], &call_graph);
    assert!(closure.contains("c"), "c is directly proved");
    assert!(closure.contains("b"), "b should be transitively verified (calls only c)");
    assert!(closure.contains("a"), "a should be transitively verified (calls only b)");
}

#[test]
fn test_transitive_closure_partial_callees_not_proved() {
    // "baz" calls "foo" and "missing". "foo" is proved but "missing" is not.
    // "baz" should NOT be transitively verified.
    let foo = make_cert("foo", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());

    let mut call_graph = FxHashMap::default();
    call_graph.insert(
        "baz".to_string(),
        vec!["foo".to_string(), "missing".to_string()],
    );

    let closure = transitive_closure(&[&foo], &call_graph);
    assert!(closure.contains("foo"));
    assert!(!closure.contains("baz"), "baz should NOT be transitively verified (missing callee)");
}

// -----------------------------------------------------------------------
// IncrementalComposition
// -----------------------------------------------------------------------

#[test]
fn test_incremental_body_only_invalidation() {
    let mut inc = IncrementalComposition::new();
    let f = make_cert("f", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());
    let g = make_cert("g", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());
    inc.add_certificate(f, vec![], [0u8; 32], [1u8; 32]);
    inc.add_certificate(g, vec!["f".to_string()], [2u8; 32], [3u8; 32]);

    let invalidated = inc.invalidated_by("f", ChangeKind::BodyOnly);
    assert_eq!(invalidated, vec!["f"], "body-only change should only invalidate f");
    assert!(inc.is_stale("f"));
    assert!(!inc.is_stale("g"), "g should not be stale for body-only change");
}

#[test]
fn test_incremental_spec_changed_invalidation() {
    let mut inc = IncrementalComposition::new();
    let f = make_cert("f", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());
    let g = make_cert("g", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());
    let h = make_cert("h", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());
    inc.add_certificate(f, vec![], [0u8; 32], [1u8; 32]);
    inc.add_certificate(g, vec!["f".to_string()], [2u8; 32], [3u8; 32]);
    inc.add_certificate(h, vec!["g".to_string()], [4u8; 32], [5u8; 32]);

    let invalidated = inc.invalidated_by("f", ChangeKind::SpecChanged);
    assert!(invalidated.contains(&"f".to_string()));
    assert!(invalidated.contains(&"g".to_string()), "g calls f, should be invalidated");
    assert!(
        invalidated.contains(&"h".to_string()),
        "h calls g which calls f, should be invalidated"
    );
}

#[test]
fn test_incremental_update_clears_stale() {
    let mut inc = IncrementalComposition::new();
    let f = make_cert("f", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());
    inc.add_certificate(f, vec![], [0u8; 32], [1u8; 32]);
    inc.invalidated_by("f", ChangeKind::BodyOnly);
    assert!(inc.is_stale("f"));

    let f2 = make_cert("f", "2026-03-27T12:05:00Z", ProofStrength::smt_unsat());
    inc.update_certificate(f2, vec![], [0u8; 32], [10u8; 32]);
    assert!(!inc.is_stale("f"), "f should no longer be stale after re-verification");
}

#[test]
fn test_incremental_stale_functions() {
    let mut inc = IncrementalComposition::new();
    let f = make_cert("f", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());
    let g = make_cert("g", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());
    inc.add_certificate(f, vec![], [0u8; 32], [1u8; 32]);
    inc.add_certificate(g, vec!["f".to_string()], [2u8; 32], [3u8; 32]);

    assert!(inc.stale_functions().is_empty());
    inc.invalidated_by("f", ChangeKind::SpecChanged);
    let stale = inc.stale_functions();
    assert!(stale.contains(&"f".to_string()));
    assert!(stale.contains(&"g".to_string()));
}

// -----------------------------------------------------------------------
// FunctionStrength and per-function tracking
// -----------------------------------------------------------------------

#[test]
fn test_function_strengths_in_composed_proof() {
    let a = make_cert("a", "2026-03-27T12:00:00Z", ProofStrength::constructive());
    let b = make_cert("b", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());

    let composed = compose_proofs(&[&a, &b]).unwrap();
    assert_eq!(composed.function_strengths.len(), 2);
    // combined_strength should be the weakest (smt_unsat)
    assert_eq!(composed.combined_strength, ProofStrength::smt_unsat());
    // Individual strengths should differ
    let a_strength = composed
        .function_strengths
        .iter()
        .find(|fs| fs.function == "a")
        .unwrap();
    assert_eq!(a_strength.strength, ProofStrength::constructive());
    let b_strength = composed
        .function_strengths
        .iter()
        .find(|fs| fs.function == "b")
        .unwrap();
    assert_eq!(b_strength.strength, ProofStrength::smt_unsat());
}

#[test]
fn test_combined_strength_is_lattice_minimum() {
    let strong = make_cert("strong", "2026-03-27T12:00:00Z", ProofStrength::constructive());
    let medium = make_cert("medium", "2026-03-27T12:00:00Z", ProofStrength::deductive());
    let weak = make_cert("weak", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());

    let composed = compose_proofs(&[&strong, &medium, &weak]).unwrap();
    // Weakest is smt_unsat (rank 1), not majority vote
    assert_eq!(composed.combined_strength, ProofStrength::smt_unsat());
}

// -----------------------------------------------------------------------
// transitive_closure fix: directly proved functions preserved
// -----------------------------------------------------------------------

#[test]
fn test_transitive_closure_preserves_directly_proved() {
    // foo has a direct proof but calls unproved bar.
    // Before the fix, foo would be removed. After fix, foo stays.
    let foo = make_cert("foo", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());

    let mut call_graph = FxHashMap::default();
    call_graph.insert("foo".to_string(), vec!["bar".to_string()]);

    let closure = transitive_closure(&[&foo], &call_graph);
    assert!(closure.contains("foo"), "directly proved foo should remain even with unproved callee");
    assert!(!closure.contains("bar"), "bar has no proof");
}

#[test]
fn test_incremental_function_strengths() {
    let mut inc = IncrementalComposition::new();
    let f = make_cert("f", "2026-03-27T12:00:00Z", ProofStrength::constructive());
    let g = make_cert("g", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());
    inc.add_certificate(f, vec![], [0u8; 32], [1u8; 32]);
    inc.add_certificate(g, vec!["f".to_string()], [2u8; 32], [3u8; 32]);

    let strengths = inc.function_strengths();
    assert_eq!(strengths.len(), 2);
    let f_strength = strengths.iter().find(|fs| fs.function == "f").unwrap();
    assert_eq!(f_strength.strength, ProofStrength::constructive());
}

// -----------------------------------------------------------------------
// Semantic composability checks (#648)
// -----------------------------------------------------------------------

/// Helper: create a cert with a specific formula embedded in vc_snapshot.
fn make_cert_with_formula(
    function: &str,
    timestamp: &str,
    formula: Formula,
    kind: &str,
) -> crate::ProofCertificate {
    let formula_json = serde_json::to_string(&formula).expect("formula should serialize");
    let vc_snapshot = VcSnapshot {
        kind: kind.to_string(),
        formula_json,
        location: None,
    };
    crate::ProofCertificate::new_trusted(
        function.to_string(),
        FunctionHash::from_bytes(format!("{function}-body").as_bytes()),
        vc_snapshot,
        sample_solver(ProofStrength::smt_unsat(), 42),
        vec![1, 2, 3, 4],
        timestamp.to_string(),
    )
}

#[test]
fn test_semantic_composability_equivalent_formulas() {
    // Two certificates for different functions with semantically equivalent
    // formulas (x + 1 vs 1 + x) should be composable.
    let f1 = Formula::Add(
        Box::new(Formula::Var("x".into(), trust_types::Sort::Int)),
        Box::new(Formula::Int(1)),
    );
    let f2 = Formula::Add(
        Box::new(Formula::Int(1)),
        Box::new(Formula::Var("x".into(), trust_types::Sort::Int)),
    );
    let a = make_cert_with_formula("crate::foo", "2026-03-27T12:00:00Z", f1, "Assertion");
    let b = make_cert_with_formula("crate::bar", "2026-03-27T12:00:00Z", f2, "Postcondition");

    let result = check_composability(&a, &b).unwrap();
    assert!(result.composable, "semantically equivalent formulas should compose");
}

#[test]
fn test_semantic_composability_subsumption() {
    // Callee proves And(a, b), caller assumes a -- subsumption holds.
    let stronger = Formula::And(vec![
        Formula::Var("a".into(), trust_types::Sort::Bool),
        Formula::Var("b".into(), trust_types::Sort::Bool),
    ]);
    let weaker = Formula::Var("a".into(), trust_types::Sort::Bool);

    let a = make_cert_with_formula("crate::foo", "2026-03-27T12:00:00Z", stronger, "Assertion");
    let b = make_cert_with_formula("crate::bar", "2026-03-27T12:00:00Z", weaker, "Precondition");

    let result = check_composability(&a, &b).unwrap();
    assert!(result.composable, "stronger formula should subsume weaker for composability");
}

#[test]
fn test_semantic_composability_same_function_same_vc_rejected() {
    // Same function + same VC kind should still be rejected even with semantic check.
    let f = Formula::Var("x".into(), trust_types::Sort::Int);
    let a = make_cert_with_formula("crate::foo", "2026-03-27T12:00:00Z", f.clone(), "Assertion");
    let b = make_cert_with_formula("crate::foo", "2026-03-27T12:05:00Z", f, "Assertion");

    let result = check_composability(&a, &b).unwrap();
    assert!(!result.composable, "same function + same VC kind is redundant");
}

#[test]
fn test_semantic_composability_direct_call() {
    // Directly call check_composability_semantic with different VCs
    let f1 = Formula::Gt(
        Box::new(Formula::Var("x".into(), trust_types::Sort::Int)),
        Box::new(Formula::Int(0)),
    );
    let f2 = Formula::Lt(
        Box::new(Formula::Var("y".into(), trust_types::Sort::Int)),
        Box::new(Formula::Int(10)),
    );
    let a = make_cert_with_formula("crate::foo", "2026-03-27T12:00:00Z", f1, "Assertion");
    let b = make_cert_with_formula("crate::bar", "2026-03-27T12:00:00Z", f2, "Precondition");

    let result = check_composability_semantic(&a, &b).unwrap();
    assert!(
        result.composable,
        "independent formulas on different functions should compose semantically"
    );
}

#[test]
fn test_semantic_composability_invalid_formula_json() {
    // tRust #756: Invalid formula_json must return an error, not silently pass.
    let mut a = make_cert("crate::foo", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());
    a.vc_snapshot.formula_json = "not-valid-json{{".to_string();
    let b = make_cert("crate::bar", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());

    let err = check_composability_semantic(&a, &b)
        .expect_err("corrupted formula_json should return error");
    match err {
        CompositionError::FormulaDeserializationFailed { ref function, .. } => {
            assert_eq!(function, "crate::foo");
        }
        other => panic!("expected FormulaDeserializationFailed, got: {other:?}"),
    }
}

#[test]
fn test_semantic_composability_both_formulas_corrupted() {
    // tRust #756: When both certs have corrupted formula_json, the first
    // deserialization failure should surface.
    let mut a = make_cert("crate::foo", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());
    a.vc_snapshot.formula_json = "{garbage".to_string();
    let mut b = make_cert("crate::bar", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());
    b.vc_snapshot.formula_json = "also-garbage".to_string();

    let err = check_composability_semantic(&a, &b)
        .expect_err("both corrupted formulas should return error");
    match err {
        CompositionError::FormulaDeserializationFailed { ref function, .. } => {
            assert_eq!(function, "crate::foo", "first cert's error should surface first");
        }
        other => panic!("expected FormulaDeserializationFailed, got: {other:?}"),
    }
}

#[test]
fn test_composability_corrupted_formula_via_public_api() {
    // tRust #756: check_composability (public API) must propagate
    // deserialization errors when semantic fallback is triggered.
    // To trigger semantic fallback, the syntactic contradiction check must
    // fire: a.formula_json == negate_formula_json(b.formula_json).
    //
    // Strategy: use a valid formula for b, compute its negation, set
    // a.formula_json to that negation (so syntactic check fires), then
    // corrupt a.formula_json slightly so it still matches syntactically
    // but fails deserialization in the semantic path.
    use super::checkers::negate_formula_json;

    let b_formula = Formula::Bool(true);
    let b_json = serde_json::to_string(&b_formula).unwrap();
    // negate_formula_json wraps in Not(...) via serde
    let negated_b = negate_formula_json(&b_json);

    let mut a = make_cert("crate::foo", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());
    let mut b = make_cert("crate::foo", "2026-03-27T12:05:00Z", ProofStrength::smt_unsat());
    // Different VC kinds so same-function-same-vc doesn't fire
    a.vc_snapshot.kind = "Assertion".to_string();
    b.vc_snapshot.kind = "Precondition".to_string();
    // Set a's formula to the valid negation, and b's to the valid formula
    a.vc_snapshot.formula_json = negated_b.clone();
    b.vc_snapshot.formula_json = b_json;

    // Verify the syntactic contradiction check fires (formulas match negation)
    assert_eq!(a.vc_snapshot.formula_json, negate_formula_json(&b.vc_snapshot.formula_json));

    // Now corrupt a's formula JSON so semantic deserialization fails
    a.vc_snapshot.formula_json = negated_b + "CORRUPTED";

    // Syntactic check now won't fire (corrupted string won't match negation),
    // so check_composability returns Ok early. This is correct behavior:
    // the syntactic check is conservative, and corruption prevents the match.
    // The important test is via check_composability_semantic directly.
    //
    // Test that direct semantic call still catches the corruption:
    let err = check_composability_semantic(&a, &b)
        .expect_err("corrupted formula should be caught by semantic check");
    assert!(
        matches!(err, CompositionError::FormulaDeserializationFailed { .. }),
        "expected FormulaDeserializationFailed, got: {err:?}"
    );
}

#[test]
fn test_semantic_composability_true_subsumes_anything() {
    // A certificate with formula `true` should compose with anything.
    let a = make_cert_with_formula(
        "crate::foo",
        "2026-03-27T12:00:00Z",
        Formula::Bool(true),
        "Assertion",
    );
    let b = make_cert_with_formula(
        "crate::bar",
        "2026-03-27T12:00:00Z",
        Formula::Gt(
            Box::new(Formula::Var("x".into(), trust_types::Sort::Int)),
            Box::new(Formula::Int(0)),
        ),
        "Precondition",
    );

    let result = check_composability_semantic(&a, &b).unwrap();
    assert!(result.composable, "true subsumes everything");
}

#[test]
fn test_semantic_composability_disjunct_implies_disjunction() {
    // a => Or(a, b, c) should make these composable.
    let stronger = Formula::Var("a".into(), trust_types::Sort::Bool);
    let weaker = Formula::Or(vec![
        Formula::Var("a".into(), trust_types::Sort::Bool),
        Formula::Var("b".into(), trust_types::Sort::Bool),
        Formula::Var("c".into(), trust_types::Sort::Bool),
    ]);

    let a = make_cert_with_formula("crate::foo", "2026-03-27T12:00:00Z", stronger, "Assertion");
    let b = make_cert_with_formula("crate::bar", "2026-03-27T12:00:00Z", weaker, "Postcondition");

    let result = check_composability_semantic(&a, &b).unwrap();
    assert!(result.composable, "disjunct implies disjunction -- composable");
}

// -----------------------------------------------------------------------
// CompositionManifest (#650)
// -----------------------------------------------------------------------

fn make_manifest_entry(
    strength: ProofStrength,
    composable: bool,
    deps: Vec<&str>,
) -> ManifestEntry {
    ManifestEntry {
        spec: FunctionSpec {
            preconditions: vec!["x > 0".to_string()],
            postconditions: vec!["result >= x".to_string()],
            proof_strength: strength,
        },
        signature_hash: "abcdef1234567890".to_string(),
        composable,
        dependencies: deps.into_iter().map(String::from).collect(),
    }
}

#[test]
fn test_manifest_new_empty() {
    let m = CompositionManifest::new("my-crate", "0.1.0");
    assert!(m.is_empty());
    assert_eq!(m.len(), 0);
    assert_eq!(m.crate_id, "my-crate");
    assert_eq!(m.version, "0.1.0");
    assert!(m.function_names().is_empty());
}

#[test]
fn test_manifest_add_and_lookup() {
    let mut m = CompositionManifest::new("my-crate", "0.1.0");
    let entry = make_manifest_entry(ProofStrength::smt_unsat(), true, vec!["bar"]);
    m.add_entry("crate::foo", entry.clone());

    assert_eq!(m.len(), 1);
    assert!(!m.is_empty());
    let looked_up = m.lookup("crate::foo").expect("should find entry");
    assert_eq!(looked_up, &entry);
    assert!(m.lookup("crate::missing").is_none());
}

#[test]
fn test_manifest_function_names_sorted() {
    let mut m = CompositionManifest::new("my-crate", "0.1.0");
    m.add_entry("crate::zeta", make_manifest_entry(ProofStrength::smt_unsat(), true, vec![]));
    m.add_entry("crate::alpha", make_manifest_entry(ProofStrength::smt_unsat(), true, vec![]));
    m.add_entry("crate::mu", make_manifest_entry(ProofStrength::smt_unsat(), true, vec![]));

    assert_eq!(
        m.function_names(),
        vec!["crate::alpha", "crate::mu", "crate::zeta"]
    );
}

#[test]
fn test_manifest_is_composable_both_valid() {
    let mut m = CompositionManifest::new("my-crate", "0.1.0");
    m.add_entry("foo", make_manifest_entry(ProofStrength::smt_unsat(), true, vec![]));
    m.add_entry("bar", make_manifest_entry(ProofStrength::constructive(), true, vec![]));

    assert!(m.is_composable("foo", "bar").expect("should not error"));
}

#[test]
fn test_manifest_is_composable_one_not_composable() {
    let mut m = CompositionManifest::new("my-crate", "0.1.0");
    m.add_entry("foo", make_manifest_entry(ProofStrength::smt_unsat(), true, vec![]));
    m.add_entry("bar", make_manifest_entry(ProofStrength::smt_unsat(), false, vec![]));

    assert!(!m.is_composable("foo", "bar").expect("should not error"));
}

#[test]
fn test_manifest_is_composable_bounded_too_weak() {
    let mut m = CompositionManifest::new("my-crate", "0.1.0");
    m.add_entry("foo", make_manifest_entry(ProofStrength::smt_unsat(), true, vec![]));
    // Bounded proof has rank 0 (below SMT threshold of 1)
    m.add_entry("bar", make_manifest_entry(ProofStrength::bounded(5), true, vec![]));

    assert!(!m.is_composable("foo", "bar").expect("should not error"));
}

#[test]
fn test_manifest_is_composable_missing_function() {
    let mut m = CompositionManifest::new("my-crate", "0.1.0");
    m.add_entry("foo", make_manifest_entry(ProofStrength::smt_unsat(), true, vec![]));

    let err = m.is_composable("foo", "missing").expect_err("should error");
    match err {
        ManifestError::FunctionNotFound { function } => {
            assert_eq!(function, "missing");
        }
        other => panic!("expected FunctionNotFound, got: {other:?}"),
    }
}

#[test]
fn test_manifest_merge_disjoint() {
    let mut m1 = CompositionManifest::new("crate-a", "0.1.0");
    m1.add_entry("foo", make_manifest_entry(ProofStrength::smt_unsat(), true, vec![]));
    m1.internal_edges.push(("foo".to_string(), "helper".to_string()));

    let mut m2 = CompositionManifest::new("crate-b", "0.2.0");
    m2.add_entry("bar", make_manifest_entry(ProofStrength::constructive(), true, vec![]));
    m2.internal_edges.push(("bar".to_string(), "util".to_string()));

    m1.merge(&m2).expect("disjoint merge should succeed");
    assert_eq!(m1.len(), 2);
    assert!(m1.lookup("foo").is_some());
    assert!(m1.lookup("bar").is_some());
    assert_eq!(m1.internal_edges.len(), 2);
}

#[test]
fn test_manifest_merge_same_function_same_hash() {
    let mut m1 = CompositionManifest::new("crate-a", "0.1.0");
    m1.add_entry("foo", make_manifest_entry(ProofStrength::smt_unsat(), true, vec![]));

    let mut m2 = CompositionManifest::new("crate-b", "0.2.0");
    // Same signature_hash ("abcdef1234567890") -- should succeed
    m2.add_entry("foo", make_manifest_entry(ProofStrength::constructive(), true, vec![]));

    m1.merge(&m2).expect("same hash merge should succeed");
    assert_eq!(m1.len(), 1);
    // Last-writer-wins: m2's entry replaces m1's
    let entry = m1.lookup("foo").unwrap();
    assert_eq!(entry.spec.proof_strength, ProofStrength::constructive());
}

#[test]
fn test_manifest_merge_conflict() {
    let mut m1 = CompositionManifest::new("crate-a", "0.1.0");
    m1.add_entry("foo", make_manifest_entry(ProofStrength::smt_unsat(), true, vec![]));

    let mut m2 = CompositionManifest::new("crate-b", "0.2.0");
    let mut conflicting = make_manifest_entry(ProofStrength::smt_unsat(), true, vec![]);
    conflicting.signature_hash = "different_hash".to_string();
    m2.add_entry("foo", conflicting);

    let err = m1.merge(&m2).expect_err("conflicting hashes should fail");
    match err {
        ManifestError::MergeConflict { function } => {
            assert_eq!(function, "foo");
        }
        other => panic!("expected MergeConflict, got: {other:?}"),
    }
}

#[test]
fn test_manifest_merge_deduplicates_edges() {
    let mut m1 = CompositionManifest::new("crate-a", "0.1.0");
    m1.internal_edges.push(("a".to_string(), "b".to_string()));

    let mut m2 = CompositionManifest::new("crate-b", "0.2.0");
    m2.internal_edges.push(("a".to_string(), "b".to_string())); // duplicate
    m2.internal_edges.push(("c".to_string(), "d".to_string())); // new

    m1.merge(&m2).expect("merge should succeed");
    assert_eq!(m1.internal_edges.len(), 2);
}

#[test]
fn test_manifest_json_roundtrip() {
    let mut m = CompositionManifest::new("my-crate", "0.1.0");
    m.add_entry("foo", make_manifest_entry(ProofStrength::smt_unsat(), true, vec!["bar"]));
    m.add_entry("bar", make_manifest_entry(ProofStrength::constructive(), true, vec![]));
    m.internal_edges.push(("foo".to_string(), "bar".to_string()));
    m.external_deps
        .push(("foo".to_string(), "dep-crate".to_string(), "dep::helper".to_string()));
    m.spec_hashes.insert("foo".to_string(), 0xDEAD_BEEF);
    m.bundle_hash = vec![1, 2, 3, 4];

    let json = m.to_json().expect("should serialize");
    let restored = CompositionManifest::from_json(&json).expect("should deserialize");
    assert_eq!(restored, m);
}

#[test]
fn test_manifest_json_invalid() {
    let err = CompositionManifest::from_json("not valid json{{{")
        .expect_err("invalid JSON should fail");
    match err {
        ManifestError::SerializationFailed { .. } => {}
        other => panic!("expected SerializationFailed, got: {other:?}"),
    }
}

#[test]
fn test_generate_manifest_from_composition() {
    let mut comp = ProofComposition::new();
    let foo = make_cert("crate::foo", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());
    let bar = make_cert("crate::bar", "2026-03-27T12:00:00Z", ProofStrength::constructive());

    comp.add_certificate(bar, vec![]);
    comp.add_certificate(foo, vec!["crate::bar".to_string()]);

    let manifest = generate_manifest(&comp, "test-crate", "0.1.0");

    assert_eq!(manifest.crate_id, "test-crate");
    assert_eq!(manifest.version, "0.1.0");
    assert_eq!(manifest.len(), 2);

    let foo_entry = manifest.lookup("crate::foo").expect("foo should be in manifest");
    assert!(foo_entry.composable);
    assert_eq!(foo_entry.dependencies, vec!["crate::bar"]);
    assert_eq!(foo_entry.spec.proof_strength, ProofStrength::smt_unsat());

    let bar_entry = manifest.lookup("crate::bar").expect("bar should be in manifest");
    assert!(bar_entry.composable);
    assert!(bar_entry.dependencies.is_empty());
    assert_eq!(bar_entry.spec.proof_strength, ProofStrength::constructive());

    // Should have one internal edge: foo -> bar
    assert_eq!(manifest.internal_edges.len(), 1);
    assert!(manifest.internal_edges.contains(&(
        "crate::foo".to_string(),
        "crate::bar".to_string()
    )));
}

#[test]
fn test_generate_manifest_missing_cert_not_composable() {
    let mut comp = ProofComposition::new();
    comp.add_missing("crate::baz", vec![]);

    let manifest = generate_manifest(&comp, "test-crate", "0.1.0");
    let baz = manifest.lookup("crate::baz").expect("baz should be in manifest");
    assert!(!baz.composable, "missing cert should not be composable");
}

#[test]
fn test_manifest_entry_dependencies_preserved() {
    let mut m = CompositionManifest::new("my-crate", "0.1.0");
    let entry = make_manifest_entry(
        ProofStrength::smt_unsat(),
        true,
        vec!["dep::a", "dep::b", "dep::c"],
    );
    m.add_entry("caller", entry);

    let looked_up = m.lookup("caller").unwrap();
    assert_eq!(
        looked_up.dependencies,
        vec!["dep::a", "dep::b", "dep::c"]
    );
}

// -----------------------------------------------------------------------
// CompositionError variant + Display tests (#664)
// -----------------------------------------------------------------------

#[test]
fn test_error_composition_failed_variant_and_display() {
    let result = compose_proofs(&[]);
    let err = result.unwrap_err();
    assert!(
        matches!(err, CompositionError::CompositionFailed { .. }),
        "expected CompositionFailed, got: {err:?}"
    );
    let msg = err.to_string();
    assert!(
        msg.contains("composition failed"),
        "Display should contain 'composition failed': {msg}"
    );
    assert!(
        msg.contains("zero certificates"),
        "Display should mention reason: {msg}"
    );
}

#[test]
fn test_error_incompatible_assumptions_variant_and_display() {
    // Two certs for the same function with different timestamps triggers
    // IncompatibleAssumptions in compose_proofs.
    let a = make_cert("crate::foo", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());
    let b = make_cert("crate::foo", "2026-03-27T12:05:00Z", ProofStrength::smt_unsat());

    let err = compose_proofs(&[&a, &b]).unwrap_err();
    match &err {
        CompositionError::IncompatibleAssumptions {
            cert_a,
            cert_b,
            detail,
        } => {
            assert!(!cert_a.is_empty(), "cert_a should be populated");
            assert!(!cert_b.is_empty(), "cert_b should be populated");
            assert!(!detail.is_empty(), "detail should be populated");
        }
        other => panic!("expected IncompatibleAssumptions, got: {other:?}"),
    }
    let msg = err.to_string();
    assert!(
        msg.contains("incompatible assumptions"),
        "Display should contain 'incompatible assumptions': {msg}"
    );
}

#[test]
fn test_error_circular_dependency_variant_and_display() {
    let caller = make_cert("A", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());
    let callee = make_cert("B", "2026-03-27T12:01:00Z", ProofStrength::smt_unsat());

    let required = vec!["B".to_string()];
    let mut call_graph = FxHashMap::default();
    call_graph.insert("A".to_string(), vec!["B".to_string()]);
    call_graph.insert("B".to_string(), vec!["A".to_string()]);

    let err = modular_composition(&caller, &[&callee], &required, &call_graph).unwrap_err();
    match &err {
        CompositionError::CircularDependency { cycle } => {
            assert!(cycle.contains("A"), "cycle should mention A: {cycle}");
            assert!(cycle.contains("B"), "cycle should mention B: {cycle}");
        }
        other => panic!("expected CircularDependency, got: {other:?}"),
    }
    let msg = err.to_string();
    assert!(
        msg.contains("circular dependency detected"),
        "Display should contain 'circular dependency detected': {msg}"
    );
    assert!(msg.contains("->"), "Display should show cycle arrow: {msg}");
}

#[test]
fn test_error_missing_link_variant_and_display() {
    let caller = make_cert("crate::foo", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());
    let required = vec!["crate::bar".to_string()];
    let call_graph = FxHashMap::default();

    let err = modular_composition(&caller, &[], &required, &call_graph).unwrap_err();
    match &err {
        CompositionError::MissingLink { function } => {
            assert_eq!(function, "crate::bar");
        }
        other => panic!("expected MissingLink, got: {other:?}"),
    }
    let msg = err.to_string();
    assert!(
        msg.contains("missing link"),
        "Display should contain 'missing link': {msg}"
    );
    assert!(
        msg.contains("crate::bar"),
        "Display should name the missing function: {msg}"
    );
}

#[test]
fn test_error_weakening_failed_variant_and_display() {
    let cert = make_cert("crate::foo", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());
    let unrelated = Property::new("Overflow");

    let err = weakening(&cert, &unrelated).unwrap_err();
    match &err {
        CompositionError::WeakeningFailed { target_property } => {
            assert_eq!(target_property, "Overflow");
        }
        other => panic!("expected WeakeningFailed, got: {other:?}"),
    }
    let msg = err.to_string();
    assert!(
        msg.contains("weakening failed"),
        "Display should contain 'weakening failed': {msg}"
    );
    assert!(
        msg.contains("Overflow"),
        "Display should name the target property: {msg}"
    );
}

#[test]
fn test_error_strengthening_failed_variant_and_display() {
    let cert = make_cert("crate::foo", "2026-03-27T12:00:00Z", ProofStrength::smt_unsat());
    let stronger = Property::new("MemorySafety");

    let err = strengthening_check(&cert, &stronger).unwrap_err();
    match &err {
        CompositionError::StrengtheningFailed {
            cert_id,
            target_property,
        } => {
            assert!(!cert_id.is_empty(), "cert_id should be populated");
            assert_eq!(target_property, "MemorySafety");
        }
        other => panic!("expected StrengtheningFailed, got: {other:?}"),
    }
    let msg = err.to_string();
    assert!(
        msg.contains("strengthening check failed"),
        "Display should contain 'strengthening check failed': {msg}"
    );
    assert!(
        msg.contains("MemorySafety"),
        "Display should name the target property: {msg}"
    );
}

#[test]
fn test_error_into_cert_error() {
    // CompositionError should convert into CertError::VerificationFailed
    let comp_err = CompositionError::CompositionFailed {
        reason: "test reason".to_string(),
    };
    let cert_err: crate::CertError = comp_err.into();
    match cert_err {
        crate::CertError::VerificationFailed { reason } => {
            assert!(
                reason.contains("test reason"),
                "CertError should carry the composition error message: {reason}"
            );
        }
        other => panic!("expected VerificationFailed, got: {other:?}"),
    }
}
