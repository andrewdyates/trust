//! Tests for the Router and backend selection logic.

use std::sync::Arc;

use trust_types::*;

use crate::*;

#[test]
fn test_router_with_mock() {
    let router = Router::with_backends(vec![Box::new(mock_backend::MockBackend)]);

    let vc = VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: "test".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(false),
        contract_metadata: None,
    };

    let result = router.verify_one(&vc);
    assert!(result.is_proved() || result.is_failed());
}

#[test]
fn test_router_verify_all() {
    let router = Router::with_backends(vec![Box::new(mock_backend::MockBackend)]);

    let vcs = vec![
        VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "test".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
        },
        VerificationCondition {
            kind: VcKind::ArithmeticOverflow {
                op: BinOp::Add,
                operand_tys: (Ty::usize(), Ty::usize()),
            },
            function: "test".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        },
    ];

    let results = router.verify_all(&vcs);
    assert_eq!(results.len(), 2);
}

#[test]
fn test_router_verify_all_parallel() {
    let router = Router::with_backends(vec![Box::new(mock_backend::MockBackend)]);

    let vcs: Vec<_> = (0..8)
        .map(|i| VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: format!("fn_{i}").into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
        })
        .collect();

    let results = router.verify_all_parallel(&vcs, 4);
    assert_eq!(results.len(), 8);
    for (_, result) in &results {
        assert!(result.is_proved());
    }
}

#[test]
fn test_router_verify_all_parallel_fallback_single() {
    let router = Router::new();
    let vcs = vec![VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: "test".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(false),
        contract_metadata: None,
    }];

    // Single VC should use sequential path
    let results = router.verify_all_parallel(&vcs, 4);
    assert_eq!(results.len(), 1);
}

#[test]
fn test_router_with_arc_backends() {
    let backends: Vec<Arc<dyn VerificationBackend>> = vec![Arc::new(mock_backend::MockBackend)];
    let router = Router::with_arc_backends(backends);

    let vc = VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: "test".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(false),
        contract_metadata: None,
    };
    assert!(router.verify_one(&vc).is_proved());
}

#[test]
fn test_router_arc_backends_accessor() {
    let router = Router::new();
    let arcs = router.arc_backends();
    assert_eq!(arcs.len(), 1);
    assert_eq!(arcs[0].name(), "mock");
}

#[test]
fn test_backend_plan_prefers_solver_family_before_fallback() {
    struct PreferredBackend;
    struct FallbackBackend;

    impl VerificationBackend for PreferredBackend {
        fn name(&self) -> &str {
            "preferred"
        }

        fn role(&self) -> BackendRole {
            BackendRole::SmtSolver
        }

        fn can_handle(&self, _vc: &VerificationCondition) -> bool {
            true
        }

        fn verify(&self, _vc: &VerificationCondition) -> VerificationResult {
            VerificationResult::Proved {
                solver: "preferred".into(),
                time_ms: 0,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: None,
                solver_warnings: None,
            }
        }
    }

    impl VerificationBackend for FallbackBackend {
        fn name(&self) -> &str {
            "fallback"
        }

        fn role(&self) -> BackendRole {
            BackendRole::General
        }

        fn can_handle(&self, _vc: &VerificationCondition) -> bool {
            true
        }

        fn verify(&self, _vc: &VerificationCondition) -> VerificationResult {
            VerificationResult::Failed {
                solver: "fallback".into(),
                time_ms: 0,
                counterexample: None,
            }
        }
    }

    let router = Router::with_backends(vec![Box::new(FallbackBackend), Box::new(PreferredBackend)]);
    let vc = VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: "test".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(false),
        contract_metadata: None,
    };

    let plan = router.backend_plan(&vc);
    assert_eq!(plan[0].name, "preferred");
    assert_eq!(plan[0].role, BackendRole::SmtSolver);
    assert!(plan[0].can_handle);
    assert_eq!(plan[1].name, "fallback");

    let result = router.verify_one(&vc);
    assert!(result.is_proved());
    assert_eq!(result.solver_name(), "preferred");
}

// -----------------------------------------------------------------------
// CEGAR dispatch integration tests (#141)
// -----------------------------------------------------------------------

#[test]
fn test_non_termination_not_dispatched_to_cegar() {
    // tRust #194: NonTermination VCs must NOT be routed to CEGAR/IC3/PDR.
    // PDR and k-induction prove safety (AG !bad), not termination.
    let router = Router::with_cegar(
        cegar_backend::CegarBackendConfig::default(),
        vec![Box::new(mock_backend::MockBackend)],
    );

    let vc = VerificationCondition {
        kind: VcKind::NonTermination {
            context: "while loop".to_string(),
            measure: "n".to_string(),
        },
        function: "loop_fn".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };

    let plan = router.backend_plan(&vc);
    let cegar_entry = plan.iter().find(|e| e.name == "cegar");
    assert!(cegar_entry.is_some(), "CEGAR should appear in plan");
    assert!(
        !cegar_entry.unwrap().can_handle,
        "CEGAR should NOT handle NonTermination VCs (PDR proves safety, not termination)"
    );

    // Mock backend should handle it instead.
    let result = router.verify_one(&vc);
    assert_ne!(result.solver_name(), "cegar", "NonTermination must not be dispatched to CEGAR");
}

#[test]
fn test_cegar_backend_skipped_for_simple_safety_vc() {
    // DivisionByZero with a simple formula scores 0, below threshold (30).
    let router = Router::with_cegar(
        cegar_backend::CegarBackendConfig::default(),
        vec![Box::new(mock_backend::MockBackend)],
    );

    let vc = VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: "simple_fn".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(false),
        contract_metadata: None,
    };

    let plan = router.backend_plan(&vc);
    // CEGAR should not be able to handle this VC (score too low).
    let cegar_entry = plan.iter().find(|e| e.name == "cegar");
    assert!(cegar_entry.is_some(), "CEGAR should appear in plan");
    assert!(!cegar_entry.unwrap().can_handle, "CEGAR should NOT handle simple safety VC");

    // The mock backend should handle it instead.
    let result = router.verify_one(&vc);
    assert_eq!(result.solver_name(), "mock", "mock should handle simple VC, not CEGAR");
}

#[test]
fn test_cegar_backend_ranked_in_plan_for_l0_safety() {
    // For L0Safety, CEGAR is ranked 3rd (after SmtSolver=0, BoundedModelChecker=1).
    let router = Router::with_cegar(
        cegar_backend::CegarBackendConfig::default(),
        vec![Box::new(mock_backend::MockBackend)],
    );

    let vc = VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: "test".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(false),
        contract_metadata: None,
    };

    let plan = router.backend_plan(&vc);
    assert_eq!(plan.len(), 2);
    // Mock is General (rank 9), CEGAR is Cegar (rank 2 for L0Safety).
    // But CEGAR can't handle this VC, so mock (which can) should come first.
    assert_eq!(
        plan[0].name, "mock",
        "mock should be first (can_handle=true beats can_handle=false)"
    );
    assert_eq!(plan[1].name, "cegar", "cegar should be second");
}

#[test]
fn test_cegar_backend_ranked_high_for_l1_functional() {
    // For L1Functional (Postcondition), CEGAR is ranked 2nd after Deductive.
    // With a high-scoring formula, CEGAR can_handle=true should rank it well.
    let router = Router::with_cegar(
        cegar_backend::CegarBackendConfig {
            classifier_threshold: 5, // Low threshold so postcondition (10 pts) triggers CEGAR
            ..cegar_backend::CegarBackendConfig::default()
        },
        vec![Box::new(mock_backend::MockBackend)],
    );

    let vc = VerificationCondition {
        kind: VcKind::Postcondition,
        function: "post_fn".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };

    let plan = router.backend_plan(&vc);
    // CEGAR can handle (postcondition gives 10 pts > threshold 5).
    // Both can handle, so ranking by role: CEGAR (rank 1 for L1) beats General (rank 9).
    assert_eq!(plan[0].name, "cegar", "CEGAR should be preferred for L1Functional");
    assert!(plan[0].can_handle);

    let result = router.verify_one(&vc);
    assert_eq!(result.solver_name(), "cegar");
    assert!(result.is_proved());
}

#[test]
fn test_cegar_dispatch_with_complex_loop_invariant_formula() {
    // tRust #194: Test CEGAR dispatch with a complex loop-invariant assertion
    // (NOT NonTermination, which should not go to CEGAR — PDR proves safety only).
    let router = Router::with_cegar(
        cegar_backend::CegarBackendConfig {
            classifier_threshold: 30,
            max_iterations: 5,
            ic3_fallback: true,
            ..cegar_backend::CegarBackendConfig::default()
        },
        vec![Box::new(mock_backend::MockBackend)],
    );

    // Build a formula with loop pattern (primed variable) + deep nesting.
    let x = Formula::Var("x".into(), Sort::Int);
    let x_next = Formula::Var("x_next_step".into(), Sort::Int);
    let y = Formula::Var("y".into(), Sort::Int);
    let z = Formula::Var("z".into(), Sort::Int);
    let a = Formula::Var("a".into(), Sort::Int);
    let b = Formula::Var("b".into(), Sort::Int);
    let formula = Formula::And(vec![
        Formula::Gt(Box::new(x), Box::new(Formula::Int(0))),
        Formula::Lt(Box::new(x_next), Box::new(y.clone())),
        Formula::Gt(Box::new(z), Box::new(a)),
        Formula::Le(Box::new(b), Box::new(y)),
    ]);

    let vc = VerificationCondition {
        kind: VcKind::Assertion { message: "loop invariant: counter decreases".to_string() },
        function: "complex_fn".into(),
        location: SourceSpan::default(),
        formula,
        contract_metadata: None,
    };

    // Loop-invariant assertion (25) + loop pattern (20) + dimensionality = well above 30.
    let classification = cegar_classifier::classify(&vc);
    assert!(
        classification.should_use_cegar,
        "complex loop invariant VC should trigger CEGAR, score={}",
        classification.score
    );

    // Router should dispatch to CEGAR.
    let plan = router.backend_plan(&vc);
    let cegar_entry = plan.iter().find(|e| e.name == "cegar").unwrap();
    assert!(cegar_entry.can_handle, "CEGAR should handle complex loop invariant VC");

    let result = router.verify_one(&vc);
    // CEGAR or CEGAR-IC3 should handle it.
    let solver = result.solver_name();
    assert!(
        solver == "cegar" || solver == "cegar-ic3",
        "expected cegar or cegar-ic3, got: {solver}"
    );
}

#[test]
fn test_cegar_in_multi_backend_router_dispatch() {
    // Full router with CEGAR + multiple other backends.
    // Ensures CEGAR integrates correctly with the existing backend ecosystem.
    let router = Router::with_cegar(
        cegar_backend::CegarBackendConfig::default(),
        vec![
            // tRust #798: ZaniBackend and SunderBackend gated behind not(pipeline-v2).
            Box::new(tla2_backend::Tla2Backend),
            Box::new(mock_backend::MockBackend),
        ],
    );

    // tRust #194: NonTermination should NOT go to CEGAR.
    // tRust #556: sunder is disabled, so tla2 or mock handles NonTermination.
    let non_term_vc = VerificationCondition {
        kind: VcKind::NonTermination { context: "loop".to_string(), measure: "n".to_string() },
        function: "loop_fn".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };

    let plan = router.backend_plan(&non_term_vc);
    // CEGAR should NOT handle NonTermination (PDR proves safety, not termination).
    let cegar_entry = plan.iter().find(|e| e.name == "cegar");
    assert!(cegar_entry.is_some());
    assert!(!cegar_entry.unwrap().can_handle, "CEGAR must NOT handle NonTermination VCs");
    // sunder is disabled (#556), so the first handler should be tla2 or mock.
    let first_handler = plan.iter().find(|e| e.can_handle);
    assert!(first_handler.is_some());
    assert_ne!(first_handler.unwrap().name, "cegar", "NonTermination must not go to CEGAR");
    assert_ne!(first_handler.unwrap().name, "sunder", "sunder is disabled (#556)");

    // DivisionByZero should skip CEGAR and go to zani or mock.
    let safety_vc = VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: "div_fn".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(false),
        contract_metadata: None,
    };

    let plan = router.backend_plan(&safety_vc);
    let first_handler = plan.iter().find(|e| e.can_handle);
    assert!(first_handler.is_some());
    assert_ne!(first_handler.unwrap().name, "cegar", "simple safety VC should not go to CEGAR");
}

#[test]
fn test_with_cegar_constructor_includes_cegar_backend() {
    let router = Router::with_cegar(
        cegar_backend::CegarBackendConfig::default(),
        vec![Box::new(mock_backend::MockBackend)],
    );

    let arcs = router.arc_backends();
    assert_eq!(arcs.len(), 2, "should have CEGAR + mock");
    assert_eq!(arcs[0].name(), "cegar");
    assert_eq!(arcs[0].role(), BackendRole::Cegar);
    assert_eq!(arcs[1].name(), "mock");
}

#[test]
fn test_cegar_verify_all_with_mixed_vcs() {
    // tRust #194: Use Postcondition (not NonTermination) to test CEGAR dispatch
    // with mixed VCs. NonTermination must NOT go to CEGAR.
    let router = Router::with_cegar(
        cegar_backend::CegarBackendConfig {
            classifier_threshold: 5, // Low threshold so postcondition (10 pts) triggers CEGAR
            ..cegar_backend::CegarBackendConfig::default()
        },
        vec![Box::new(mock_backend::MockBackend)],
    );

    let vcs = vec![
        // Should go to CEGAR (Postcondition scores 10 > threshold 5).
        VerificationCondition {
            kind: VcKind::Postcondition,
            function: "cegar_fn".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        },
        // Should go to mock (DivisionByZero scores 0).
        VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "mock_fn".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
        },
    ];

    let results = router.verify_all(&vcs);
    assert_eq!(results.len(), 2);

    // First VC: CEGAR proves it.
    assert_eq!(results[0].1.solver_name(), "cegar");
    assert!(results[0].1.is_proved());

    // Second VC: mock handles it.
    assert_eq!(results[1].1.solver_name(), "mock");
    assert!(results[1].1.is_proved());
}

// -----------------------------------------------------------------------
// validate_dispatch integration tests (#422)
// -----------------------------------------------------------------------

#[test]
fn test_validate_dispatch_blocks_safety_solver_for_termination_vc() {
    // tRust #422: A backend named "pdr" claims can_handle=true for all VCs,
    // but validate_dispatch must block it for NonTermination because PDR
    // only proves safety (AG !bad), not termination.
    struct PdrBackend;

    impl VerificationBackend for PdrBackend {
        fn name(&self) -> &str {
            "pdr"
        }
        fn role(&self) -> BackendRole {
            BackendRole::SmtSolver
        }
        fn can_handle(&self, _vc: &VerificationCondition) -> bool {
            true // claims to handle everything
        }
        fn verify(&self, _vc: &VerificationCondition) -> VerificationResult {
            VerificationResult::Proved {
                solver: "pdr".into(),
                time_ms: 0,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: None,
                solver_warnings: None,
            }
        }
    }

    let router =
        Router::with_backends(vec![Box::new(PdrBackend), Box::new(mock_backend::MockBackend)]);

    let vc = VerificationCondition {
        kind: VcKind::NonTermination {
            context: "while loop".to_string(),
            measure: "n".to_string(),
        },
        function: "loop_fn".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };

    // PDR can_handle returns true, but validate_dispatch should block it.
    // The router should fall through to the mock backend instead.
    let result = router.verify_one(&vc);
    assert_ne!(
        result.solver_name(),
        "pdr",
        "PDR must not handle NonTermination VC even if can_handle=true (#422)"
    );
    assert_eq!(
        result.solver_name(),
        "mock",
        "mock should handle NonTermination when PDR is blocked by validate_dispatch"
    );
}

#[test]
fn test_validate_dispatch_allows_valid_solver_for_safety_vc() {
    // tRust #422: validate_dispatch should allow all solvers for safety VCs.
    struct PdrBackend;

    impl VerificationBackend for PdrBackend {
        fn name(&self) -> &str {
            "pdr"
        }
        fn role(&self) -> BackendRole {
            BackendRole::SmtSolver
        }
        fn can_handle(&self, _vc: &VerificationCondition) -> bool {
            true
        }
        fn verify(&self, _vc: &VerificationCondition) -> VerificationResult {
            VerificationResult::Proved {
                solver: "pdr".into(),
                time_ms: 0,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: None,
                solver_warnings: None,
            }
        }
    }

    let router =
        Router::with_backends(vec![Box::new(PdrBackend), Box::new(mock_backend::MockBackend)]);

    let vc = VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: "div_fn".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(false),
        contract_metadata: None,
    };

    // PDR is valid for safety VCs — validate_dispatch should allow it.
    let result = router.verify_one(&vc);
    assert_eq!(
        result.solver_name(),
        "pdr",
        "PDR should handle safety VCs (validate_dispatch allows it)"
    );
}

#[test]
fn test_validate_dispatch_blocks_all_safety_only_solvers_for_liveness() {
    // tRust #422: Safety-only solvers (ic3, bmc, k-induction) must be blocked
    // for liveness properties too, not just termination.
    struct Ic3Backend;

    impl VerificationBackend for Ic3Backend {
        fn name(&self) -> &str {
            "ic3"
        }
        fn role(&self) -> BackendRole {
            BackendRole::SmtSolver
        }
        fn can_handle(&self, _vc: &VerificationCondition) -> bool {
            true
        }
        fn verify(&self, _vc: &VerificationCondition) -> VerificationResult {
            VerificationResult::Proved {
                solver: "ic3".into(),
                time_ms: 0,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: None,
                solver_warnings: None,
            }
        }
    }

    let router =
        Router::with_backends(vec![Box::new(Ic3Backend), Box::new(mock_backend::MockBackend)]);

    let vc = VerificationCondition {
        kind: VcKind::Temporal { property: "eventually done".to_string() },
        function: "live_fn".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };

    let result = router.verify_one(&vc);
    assert_ne!(
        result.solver_name(),
        "ic3",
        "IC3 must not handle liveness VC (#422 validate_dispatch)"
    );
}

#[test]
fn test_select_backend_returns_none_when_all_invalid() {
    // tRust #422: If every backend is blocked by validate_dispatch, select_backend
    // returns None and the router returns Unknown.
    struct BmcBackend;

    impl VerificationBackend for BmcBackend {
        fn name(&self) -> &str {
            "bmc"
        }
        fn can_handle(&self, _vc: &VerificationCondition) -> bool {
            true
        }
        fn verify(&self, _vc: &VerificationCondition) -> VerificationResult {
            VerificationResult::Proved {
                solver: "bmc".into(),
                time_ms: 0,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: None,
                solver_warnings: None,
            }
        }
    }

    // Only a BMC backend: can_handle=true but invalid for termination.
    let router = Router::with_backends(vec![Box::new(BmcBackend)]);

    let vc = VerificationCondition {
        kind: VcKind::NonTermination { context: "loop".to_string(), measure: "n".to_string() },
        function: "stuck_fn".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };

    let result = router.verify_one(&vc);
    assert!(
        matches!(result, VerificationResult::Unknown { .. }),
        "should return Unknown when all backends are blocked: {result:?}"
    );
    assert_eq!(result.solver_name(), "none");
}

// tRust #798: This test uses ZaniBackend + SunderBackend (subprocess v1 backends),
// which are gated behind not(pipeline-v2).
#[cfg(not(feature = "pipeline-v2"))]
#[test]
fn test_first_class_backend_families_are_selected_by_kind() {
    let router = Router::with_backends(vec![
        Box::new(tla2_backend::Tla2Backend),
        Box::new(certus_backend::CertusBackend::new()),
        Box::new(sunder_backend::SunderBackend::new()),
        Box::new(zani_backend::ZaniBackend::new()),
        Box::new(mock_backend::MockBackend),
    ]);

    // tRust #556: sunder is disabled (can_handle returns false).
    // For L1Functional VCs (Postcondition/Precondition), the first handler
    // that can_handle will be certus (Ownership) or mock, not sunder.
    // sunder still appears in the plan but with can_handle=false.
    let cases = [
        (
            VerificationCondition {
                kind: VcKind::DivisionByZero,
                function: "l0".into(),
                location: SourceSpan::default(),
                formula: Formula::Bool(false),
                contract_metadata: None,
            },
            "zani",
            BackendRole::BoundedModelChecker,
        ),
        (
            VerificationCondition {
                kind: VcKind::Temporal { property: "eventually done".to_string() },
                function: "l2".into(),
                location: SourceSpan::default(),
                formula: Formula::Bool(false),
                contract_metadata: None,
            },
            "tla2",
            BackendRole::Temporal,
        ),
        (
            VerificationCondition {
                kind: VcKind::RefinementViolation {
                    spec_file: "Bank.tla".to_string(),
                    action: "withdraw".to_string(),
                },
                function: "l2-refine".into(),
                location: SourceSpan::default(),
                formula: Formula::Bool(false),
                contract_metadata: None,
            },
            "tla2",
            BackendRole::Temporal,
        ),
    ];

    for (vc, expected_name, expected_role) in cases {
        let plan = router.backend_plan(&vc);
        let first_handler = plan.iter().find(|e| e.can_handle);
        assert!(first_handler.is_some(), "should have a handler for {:?}", vc.kind);
        let first = first_handler.expect("handler");
        assert_eq!(first.name, expected_name);
        assert_eq!(first.role, expected_role);

        let result = router.verify_one(&vc);
        assert!(matches!(result, VerificationResult::Unknown { .. }));
        assert_eq!(result.solver_name(), expected_name);
    }

    // Postcondition/Precondition: sunder is disabled, so mock handles them
    let l1_cases = [VcKind::Postcondition, VcKind::Precondition { callee: "callee".to_string() }];
    for kind in l1_cases {
        let vc = VerificationCondition {
            kind: kind.clone(),
            function: "l1".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
        };
        let plan = router.backend_plan(&vc);
        // sunder should be in plan but NOT can_handle
        let sunder_entry = plan.iter().find(|e| e.name == "sunder");
        assert!(sunder_entry.is_some(), "sunder should still appear in plan");
        assert!(!sunder_entry.expect("sunder").can_handle, "sunder should be disabled (#556)");
        // Some other backend should handle it
        let first_handler = plan.iter().find(|e| e.can_handle);
        assert!(first_handler.is_some(), "some backend should handle L1 VC");
    }
}

// -----------------------------------------------------------------------
// #426: HigherOrder variant exists and lean5_backend uses it
// -----------------------------------------------------------------------

#[test]
fn test_higher_order_variant_exists_and_is_distinct() {
    // tRust #426: Verify the HigherOrder variant is a distinct BackendRole
    // and can be round-tripped through equality checks.
    let role = BackendRole::HigherOrder;
    assert_ne!(role, BackendRole::General);
    assert_ne!(role, BackendRole::SmtSolver);
    assert_ne!(role, BackendRole::Deductive);
    assert_ne!(role, BackendRole::Temporal);
    assert_ne!(role, BackendRole::Neural);
    assert_ne!(role, BackendRole::Cegar);
    assert_ne!(role, BackendRole::Ownership);
    assert_ne!(role, BackendRole::BoundedModelChecker);
    assert_eq!(role, BackendRole::HigherOrder);
}

// tRust #792: lean5_backend tests removed — lean5 cluster deleted.
// test_lean5_backend_returns_higher_order_role, test_l2domain_ranks_higher_order_above_deductive,
// test_l2domain_ranks_temporal_first moved to lean5 crate when available.

// -----------------------------------------------------------------------
// #441: verify_with_independence — constraint independence at dispatch
// -----------------------------------------------------------------------

/// Backend that proves any VC (for independence dispatch tests).
struct AlwaysProveBackend;

impl VerificationBackend for AlwaysProveBackend {
    fn name(&self) -> &str {
        "always-prove"
    }
    fn can_handle(&self, _vc: &VerificationCondition) -> bool {
        true
    }
    fn verify(&self, _vc: &VerificationCondition) -> VerificationResult {
        VerificationResult::Proved {
            solver: "always-prove".into(),
            time_ms: 1,
            strength: ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: None,
        }
    }
}

#[test]
fn test_verify_with_independence_splits_disjoint_conjuncts() {
    // tRust #441: And(x > 0, y > 0) — no shared vars → 2 partitions.
    let router = Router::with_backends(vec![Box::new(AlwaysProveBackend)]);
    let vc = VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: "test".into(),
        location: SourceSpan::default(),
        formula: Formula::And(vec![
            Formula::Gt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(0))),
            Formula::Lt(Box::new(Formula::Var("y".into(), Sort::Int)), Box::new(Formula::Int(10))),
        ]),
        contract_metadata: None,
    };

    let ir = router.verify_with_independence(&vc);
    assert!(ir.was_split, "disjoint conjuncts should be split");
    assert_eq!(ir.partition_count, 2);
    assert!(ir.result.is_proved(), "all sub-VCs should be proved");
    // Each partition dispatched separately, so total time = 2 * 1ms.
    assert_eq!(ir.result.time_ms(), 2);
}

#[test]
fn test_verify_with_independence_no_split_shared_var() {
    // tRust #441: And(x > 0, x < 10) — shared var x → 1 partition, no split.
    let router = Router::with_backends(vec![Box::new(AlwaysProveBackend)]);
    let vc = VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: "test".into(),
        location: SourceSpan::default(),
        formula: Formula::And(vec![
            Formula::Gt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(0))),
            Formula::Lt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(10))),
        ]),
        contract_metadata: None,
    };

    let ir = router.verify_with_independence(&vc);
    assert!(!ir.was_split, "shared variable should prevent splitting");
    assert_eq!(ir.partition_count, 1);
}

#[test]
fn test_verify_with_independence_non_conjunction() {
    // tRust #441: Single formula (not And) → no split.
    let router = Router::with_backends(vec![Box::new(AlwaysProveBackend)]);
    let vc = VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: "test".into(),
        location: SourceSpan::default(),
        formula: Formula::Gt(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        ),
        contract_metadata: None,
    };

    let ir = router.verify_with_independence(&vc);
    assert!(!ir.was_split);
    assert_eq!(ir.partition_count, 1);
}

#[test]
fn test_verify_with_independence_transitive_merge() {
    // tRust #441: f1={a,b}, f2={b,c}, f3={d} → two partitions.
    let router = Router::with_backends(vec![Box::new(AlwaysProveBackend)]);
    let vc = VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: "test".into(),
        location: SourceSpan::default(),
        formula: Formula::And(vec![
            Formula::Gt(
                Box::new(Formula::Var("a".into(), Sort::Int)),
                Box::new(Formula::Var("b".into(), Sort::Int)),
            ),
            Formula::Gt(
                Box::new(Formula::Var("b".into(), Sort::Int)),
                Box::new(Formula::Var("c".into(), Sort::Int)),
            ),
            Formula::Gt(Box::new(Formula::Var("d".into(), Sort::Int)), Box::new(Formula::Int(0))),
        ]),
        contract_metadata: None,
    };

    let ir = router.verify_with_independence(&vc);
    assert!(ir.was_split, "transitive merge should still yield 2 partitions");
    assert_eq!(ir.partition_count, 2);
    assert!(ir.result.is_proved());
}

#[test]
fn test_verify_with_independence_early_failure() {
    // tRust #441: If any partition fails, the overall result is failure.
    struct AlwaysFailBackend;

    impl VerificationBackend for AlwaysFailBackend {
        fn name(&self) -> &str {
            "always-fail"
        }
        fn can_handle(&self, _vc: &VerificationCondition) -> bool {
            true
        }
        fn verify(&self, _vc: &VerificationCondition) -> VerificationResult {
            VerificationResult::Failed {
                solver: "always-fail".into(),
                time_ms: 1,
                counterexample: None,
            }
        }
    }

    let router = Router::with_backends(vec![Box::new(AlwaysFailBackend)]);
    let vc = VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: "test".into(),
        location: SourceSpan::default(),
        formula: Formula::And(vec![
            Formula::Gt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(0))),
            Formula::Lt(Box::new(Formula::Var("y".into(), Sort::Int)), Box::new(Formula::Int(10))),
        ]),
        contract_metadata: None,
    };

    let ir = router.verify_with_independence(&vc);
    assert!(ir.was_split);
    assert!(ir.result.is_failed(), "failure in any partition → overall failure");
}

// tRust #798: z4_direct tests removed — z4 integration now via trust-zani-lib (Pipeline v2).

// -------------------------------------------------------------------
// tRust #708: Arena-aware verification dispatch tests
// -------------------------------------------------------------------

#[test]
fn test_arena_vc_intern_batch() {
    let vcs = vec![
        VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "f1".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
        },
        VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "f2".into(),
            location: SourceSpan::default(),
            formula: Formula::Add(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(1)),
            ),
            contract_metadata: None,
        },
    ];

    let (arena, arena_vcs) = ArenaVc::intern_batch(&vcs);
    assert_eq!(arena_vcs.len(), 2);
    assert!(!arena.is_empty());

    // Roundtrip: arena formula matches original
    for avc in &arena_vcs {
        let roundtrip = arena.to_formula(avc.root);
        assert_eq!(roundtrip, avc.vc.formula);
    }
}

#[test]
fn test_arena_vc_intern_single() {
    use trust_types::formula_arena::FormulaArena;

    let vc = VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: "test".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(false),
        contract_metadata: None,
    };

    let mut arena = FormulaArena::new();
    let avc = ArenaVc::intern(&vc, &mut arena);
    assert_eq!(arena.to_formula(avc.root), Formula::Bool(false));
}

#[test]
fn test_verify_one_arena_delegates_to_verify() {
    // The default verify_arena impl delegates to verify.
    // MockBackend doesn't override verify_arena, so the result should
    // be the same as verify_one.
    let router = Router::with_backends(vec![Box::new(mock_backend::MockBackend)]);

    let vc = VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: "test".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(false),
        contract_metadata: None,
    };

    let mut arena = trust_types::formula_arena::FormulaArena::new();
    let root = arena.intern(&vc.formula);

    let result = router.verify_one_arena(&vc, root, &arena);
    assert!(result.is_proved(), "arena dispatch should prove trivially false");
    assert_eq!(result.solver_name(), "mock");
}

#[test]
fn test_verify_all_arena_multiple_vcs() {
    let router = Router::with_backends(vec![Box::new(mock_backend::MockBackend)]);

    let vcs = vec![
        VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "proved".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
        },
        VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "failed".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        },
    ];

    let (arena, arena_vcs) = ArenaVc::intern_batch(&vcs);
    let results = router.verify_all_arena(&arena_vcs, &arena);

    assert_eq!(results.len(), 2);
    assert!(results[0].1.is_proved());
    assert!(results[1].1.is_failed());
}

#[test]
fn test_verify_all_arena_parallel_produces_results() {
    let router = Router::with_backends(vec![Box::new(mock_backend::MockBackend)]);

    let vcs: Vec<_> = (0..8)
        .map(|i| VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: format!("fn_{i}").into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
        })
        .collect();

    let (arena, arena_vcs) = ArenaVc::intern_batch(&vcs);
    let results = router.verify_all_arena_parallel(&arena_vcs, Arc::new(arena), 4);

    assert_eq!(results.len(), 8);
    for (_, result) in &results {
        assert!(result.is_proved());
    }
}

#[test]
fn test_verify_arena_custom_backend_receives_arena() {
    // Test that a backend overriding verify_arena receives the arena.
    use std::sync::atomic::{AtomicBool, Ordering};

    struct ArenaAwareBackend {
        arena_called: Arc<AtomicBool>,
    }

    impl VerificationBackend for ArenaAwareBackend {
        fn name(&self) -> &str {
            "arena-aware"
        }
        fn can_handle(&self, _vc: &VerificationCondition) -> bool {
            true
        }
        fn verify(&self, _vc: &VerificationCondition) -> VerificationResult {
            VerificationResult::Proved {
                solver: "arena-aware-fallback".into(),
                time_ms: 0,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: None,
                solver_warnings: None,
            }
        }
        fn verify_arena(
            &self,
            _vc: &VerificationCondition,
            root: trust_types::formula_arena::FormulaRef,
            arena: &trust_types::formula_arena::FormulaArena,
        ) -> VerificationResult {
            self.arena_called.store(true, Ordering::SeqCst);
            // Use the arena directly to emit SMT-LIB without materialization.
            let _smtlib = arena.to_smtlib(root);
            VerificationResult::Proved {
                solver: "arena-aware".into(),
                time_ms: 0,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: None,
                solver_warnings: None,
            }
        }
    }

    let arena_called = Arc::new(AtomicBool::new(false));
    let backend = ArenaAwareBackend { arena_called: arena_called.clone() };
    let router = Router::with_backends(vec![Box::new(backend)]);

    let vc = VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: "test".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(false),
        contract_metadata: None,
    };

    let mut arena = trust_types::formula_arena::FormulaArena::new();
    let root = arena.intern(&vc.formula);

    let result = router.verify_one_arena(&vc, root, &arena);
    assert!(result.is_proved());
    assert_eq!(result.solver_name(), "arena-aware");
    assert!(
        arena_called.load(Ordering::SeqCst),
        "verify_arena should have been called, not verify"
    );
}

// -----------------------------------------------------------------------
// #882: MemoryGuard integration tests
// -----------------------------------------------------------------------

#[test]
fn test_router_with_memory_guard_builder() {
    use crate::memory_guard::MemoryGuard;

    let guard = MemoryGuard::new(2048);
    let router =
        Router::with_backends(vec![Box::new(mock_backend::MockBackend)]).with_memory_guard(guard);

    assert_eq!(router.memory_guard().limit_mb(), 2048);
}

#[test]
fn test_router_default_memory_guard() {
    let router = Router::new();
    // Default MemoryGuard has 1024 MB limit.
    assert_eq!(router.memory_guard().limit_mb(), 1024);
}

#[test]
fn test_router_memory_guard_unlimited_passes() {
    use crate::memory_guard::MemoryGuard;

    let guard = MemoryGuard::new(0); // unlimited
    let router =
        Router::with_backends(vec![Box::new(mock_backend::MockBackend)]).with_memory_guard(guard);

    let vc = VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: "test".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(false),
        contract_metadata: None,
    };

    // With unlimited guard, dispatch should proceed normally.
    let result = router.verify_one(&vc);
    assert!(result.is_proved(), "unlimited memory guard should not block dispatch");
    assert_eq!(result.solver_name(), "mock");
}

#[test]
fn test_router_memory_guard_high_limit_passes() {
    use crate::memory_guard::MemoryGuard;

    let guard = MemoryGuard::new(64 * 1024); // 64 GB — well above any test process
    let router =
        Router::with_backends(vec![Box::new(mock_backend::MockBackend)]).with_memory_guard(guard);

    let vc = VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: "test".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(false),
        contract_metadata: None,
    };

    let result = router.verify_one(&vc);
    assert!(result.is_proved(), "high limit should not block dispatch");
    assert_eq!(result.solver_name(), "mock");
}

#[test]
fn test_router_memory_guard_low_limit_blocks_dispatch() {
    use crate::memory_guard::MemoryGuard;

    // 1 MB limit — the test process uses more than this.
    let guard = MemoryGuard::new(1);
    let router =
        Router::with_backends(vec![Box::new(mock_backend::MockBackend)]).with_memory_guard(guard);

    let vc = VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: "test".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(false),
        contract_metadata: None,
    };

    let result = router.verify_one(&vc);
    assert!(
        matches!(result, VerificationResult::Unknown { .. }),
        "1MB limit should block dispatch: {result:?}"
    );
    assert_eq!(result.solver_name(), "memory-guard");
    let reason = match &result {
        VerificationResult::Unknown { reason, .. } => reason.as_str(),
        _ => panic!("expected Unknown"),
    };
    assert!(reason.contains("memory limit exceeded"), "reason: {reason}");
}

#[test]
fn test_router_memory_guard_blocks_verify_all() {
    use crate::memory_guard::MemoryGuard;

    let guard = MemoryGuard::new(1); // 1 MB — will exceed
    let router =
        Router::with_backends(vec![Box::new(mock_backend::MockBackend)]).with_memory_guard(guard);

    let vcs = vec![
        VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "fn1".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
        },
        VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "fn2".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
        },
    ];

    let results = router.verify_all(&vcs);
    assert_eq!(results.len(), 2);
    for (_, result) in &results {
        assert_eq!(
            result.solver_name(),
            "memory-guard",
            "all VCs should be blocked by memory guard"
        );
    }
}

#[test]
fn test_router_memory_guard_blocks_arena_dispatch() {
    use crate::memory_guard::MemoryGuard;

    let guard = MemoryGuard::new(1); // 1 MB — will exceed
    let router =
        Router::with_backends(vec![Box::new(mock_backend::MockBackend)]).with_memory_guard(guard);

    let vc = VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: "test".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(false),
        contract_metadata: None,
    };

    let mut arena = trust_types::formula_arena::FormulaArena::new();
    let root = arena.intern(&vc.formula);

    let result = router.verify_one_arena(&vc, root, &arena);
    assert_eq!(
        result.solver_name(),
        "memory-guard",
        "arena dispatch should be blocked by memory guard"
    );
}

#[test]
fn test_router_memory_guard_peak_tracked_after_dispatch() {
    use crate::memory_guard::MemoryGuard;

    let guard = MemoryGuard::new(64 * 1024); // high limit
    let router =
        Router::with_backends(vec![Box::new(mock_backend::MockBackend)]).with_memory_guard(guard);

    assert_eq!(router.memory_guard().peak_rss_bytes(), 0, "peak should be 0 before any check");

    let vc = VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: "test".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(false),
        contract_metadata: None,
    };

    let _ = router.verify_one(&vc);
    assert!(
        router.memory_guard().peak_rss_bytes() > 0,
        "peak RSS should be tracked after dispatch"
    );
}
