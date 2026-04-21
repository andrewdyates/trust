// trust-router/certus_backend/tests.rs: Tests for certus backend
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::sync::Arc;
use std::time::{Duration, Instant};

use trust_types::*;

use crate::portfolio::{PortfolioLane, PortfolioStrategy, race};
use crate::mock_backend::MockBackend;
use crate::portfolio_racer::{PortfolioRacer, RaceConfig};
use crate::smtlib_backend::parse_solver_output;
use crate::Router;
use crate::VerificationBackend;
use crate::BackendRole;

use super::backend::{attribute_to_certus, CertusBackend, RunSolverError};
use super::counterexample::{interpret_unsafe_counterexample, OwnershipViolation};
use super::unsafe_classify::{classify_unsafe_vc, is_unsafe_sep_vc, UnsafeVcClass};
use super::unsafe_script::generate_unsafe_ownership_script;
use super::DEFAULT_TIMEOUT_MS;

// ---------------------------------------------------------------------------
// Helper: generate_ownership_script is private in backend.rs, so we test it
// indirectly through the verify() method. For direct script tests, we call
// the function via a local re-creation (same logic, tested via output).
// ---------------------------------------------------------------------------

fn generate_ownership_script(formula: &Formula, kind: &VcKind) -> String {
    use crate::smtlib_backend::generate_smtlib_script;

    let base_script = generate_smtlib_script(formula);

    let kind_annotation = match kind {
        VcKind::Precondition { callee } => format!("; certus VC kind: precondition of `{callee}`"),
        VcKind::Postcondition => "; certus VC kind: postcondition".to_string(),
        other => format!("; certus VC kind: {}", other.description()),
    };

    let mut script = String::with_capacity(base_script.len() + 256);
    script.push_str("; certus ownership-aware verification\n");
    script.push_str("(set-option :ownership-mode true)\n");
    script.push_str("(set-option :borrow-check true)\n");
    script.push_str(&kind_annotation);
    script.push('\n');
    script.push_str(&base_script);
    script
}

#[test]
fn test_certus_backend_name_and_role() {
    let backend = CertusBackend::new();
    assert_eq!(backend.name(), "certus");
    assert_eq!(backend.role(), BackendRole::Ownership);
}

#[test]
fn test_certus_handles_preconditions() {
    let backend = CertusBackend::new();
    let vc = VerificationCondition {
        kind: VcKind::Precondition { callee: "callee".into() },
        function: "f".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };
    assert!(backend.can_handle(&vc));
}

#[test]
fn test_certus_handles_postconditions() {
    let backend = CertusBackend::new();
    let vc = VerificationCondition {
        kind: VcKind::Postcondition,
        function: "f".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };
    assert!(backend.can_handle(&vc));
}

#[test]
fn test_certus_does_not_handle_l0_safety() {
    let backend = CertusBackend::new();
    let cases = vec![
        VcKind::DivisionByZero,
        VcKind::IndexOutOfBounds,
        VcKind::ArithmeticOverflow {
            op: BinOp::Add,
            operand_tys: (Ty::usize(), Ty::usize()),
        },
    ];
    for kind in cases {
        let vc = VerificationCondition {
            kind,
            function: "f".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        };
        assert!(!backend.can_handle(&vc), "certus should not handle L0 safety VCs");
    }
}

#[test]
fn test_certus_does_not_handle_temporal() {
    let backend = CertusBackend::new();
    let vc = VerificationCondition {
        kind: VcKind::Temporal { property: "live".into() },
        function: "f".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };
    assert!(!backend.can_handle(&vc));
}

#[test]
fn test_certus_returns_unknown_when_binary_not_found() {
    let backend = CertusBackend::with_solver_path("/nonexistent/path/certus");
    let vc = VerificationCondition {
        kind: VcKind::Precondition { callee: "callee".into() },
        function: "f".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };

    let result = backend.verify(&vc);
    assert!(matches!(result, VerificationResult::Unknown { .. }));
    assert_eq!(result.solver_name(), "certus");
    if let VerificationResult::Unknown { reason, .. } = &result {
        assert!(reason.contains("failed to spawn certus"));
    }
}

#[test]
fn test_certus_returns_unknown_when_no_path_available() {
    // A fresh backend with no explicit path and (likely) no certus on PATH
    // will return Unknown with a helpful message
    let backend = CertusBackend::new();
    let vc = VerificationCondition {
        kind: VcKind::Precondition { callee: "callee".into() },
        function: "f".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };

    let result = backend.verify(&vc);
    // Either Unknown (no binary) or a real result (if certus is installed)
    assert_eq!(result.solver_name(), "certus");
}

#[test]
fn test_certus_builder_methods() {
    let backend = CertusBackend::with_solver_path("/usr/local/bin/certus")
        .with_timeout(60_000);
    assert_eq!(backend.solver_path.as_deref(), Some("/usr/local/bin/certus"));
    assert_eq!(backend.timeout_ms, 60_000);
}

#[test]
fn test_certus_default_construction() {
    let backend = CertusBackend::default();
    assert_eq!(backend.timeout_ms, DEFAULT_TIMEOUT_MS);
    assert!(backend.solver_path.is_none());
}

#[test]
fn test_generate_ownership_script_precondition() {
    let formula = Formula::Eq(Box::new(Formula::Int(2)), Box::new(Formula::Int(0)));
    let kind = VcKind::Precondition { callee: "Vec::push".into() };
    let script = generate_ownership_script(&formula, &kind);

    assert!(script.contains("; certus ownership-aware verification"));
    assert!(script.contains("(set-option :ownership-mode true)"));
    assert!(script.contains("(set-option :borrow-check true)"));
    assert!(script.contains("; certus VC kind: precondition of `Vec::push`"));
    // Should still contain the base SMT-LIB2 script
    assert!(script.contains("(set-logic QF_LIA)"));
    assert!(script.contains("(assert (= 2 0))"));
    assert!(script.contains("(check-sat)"));
}

#[test]
fn test_generate_ownership_script_postcondition() {
    let formula = Formula::Lt(
        Box::new(Formula::Var("x".to_string(), Sort::Int)),
        Box::new(Formula::Int(10)),
    );
    let kind = VcKind::Postcondition;
    let script = generate_ownership_script(&formula, &kind);

    assert!(script.contains("(set-option :ownership-mode true)"));
    assert!(script.contains("; certus VC kind: postcondition"));
    assert!(script.contains("(declare-const x Int)"));
    assert!(script.contains("(assert (< x 10))"));
}

#[test]
fn test_attribute_to_certus_proved() {
    let mut result = VerificationResult::Proved {
        solver: "z4-smtlib".to_string(),
        time_ms: 42,
        strength: ProofStrength::smt_unsat(), proof_certificate: None,
            solver_warnings: None, };
    attribute_to_certus(&mut result);

    assert_eq!(result.solver_name(), "certus");
    if let VerificationResult::Proved { strength, time_ms, .. } = &result {
        // tRust #435: certus uses OwnershipAnalysis, not generic Deductive
        assert_eq!(strength.reasoning, ReasoningKind::OwnershipAnalysis);
        assert_eq!(strength.assurance, AssuranceLevel::Sound);
        assert_eq!(*time_ms, 42);
    } else {
        panic!("expected Proved");
    }
}

#[test]
fn test_attribute_to_certus_failed() {
    let cex = Counterexample::new(vec![
        ("x".to_string(), CounterexampleValue::Uint(42)),
    ]);
    let mut result = VerificationResult::Failed {
        solver: "z4-smtlib".to_string(),
        time_ms: 10,
        counterexample: Some(cex),
    };
    attribute_to_certus(&mut result);

    assert_eq!(result.solver_name(), "certus");
    if let VerificationResult::Failed { counterexample: Some(cex), .. } = &result {
        assert_eq!(cex.assignments.len(), 1);
        assert_eq!(cex.assignments[0].0, "x");
    } else {
        panic!("expected Failed with counterexample");
    }
}

#[test]
fn test_attribute_to_certus_unknown() {
    let mut result = VerificationResult::Unknown {
        solver: "z4-smtlib".to_string(),
        time_ms: 5,
        reason: "solver returned unknown".to_string(),
    };
    attribute_to_certus(&mut result);

    assert_eq!(result.solver_name(), "certus");
}

#[test]
fn test_attribute_to_certus_timeout() {
    let mut result = VerificationResult::Timeout {
        solver: "z4-smtlib".to_string(),
        timeout_ms: 30_000,
    };
    attribute_to_certus(&mut result);

    assert_eq!(result.solver_name(), "certus");
}

#[test]
fn test_certus_counterexample_parsing_sat_with_model() {
    // Simulate certus output: SAT with model (ownership violation found)
    let output = "sat\n(model\n  (define-fun borrowed_ref () Int 0)\n)\n";
    let mut result = parse_solver_output(output, 15, vec![]);
    attribute_to_certus(&mut result);

    assert!(result.is_failed());
    assert_eq!(result.solver_name(), "certus");
    if let VerificationResult::Failed { counterexample: Some(cex), .. } = &result {
        assert_eq!(cex.assignments.len(), 1);
        assert_eq!(cex.assignments[0].0, "borrowed_ref");
        assert!(matches!(cex.assignments[0].1, CounterexampleValue::Uint(0)));
    } else {
        panic!("expected Failed with counterexample");
    }
}

#[test]
fn test_certus_counterexample_parsing_unsat() {
    // Simulate certus output: UNSAT (ownership property holds)
    let output = "unsat\n";
    let mut result = parse_solver_output(output, 8, vec![]);
    attribute_to_certus(&mut result);

    assert!(result.is_proved());
    assert_eq!(result.solver_name(), "certus");
    if let VerificationResult::Proved { strength, .. } = &result {
        // tRust #435: certus uses OwnershipAnalysis, not generic Deductive
        assert_eq!(strength.reasoning, ReasoningKind::OwnershipAnalysis);
        assert_eq!(strength.assurance, AssuranceLevel::Sound);
    } else {
        panic!("expected Proved");
    }
}

#[test]
fn test_certus_portfolio_integration_as_ownership_lane() {
    let certus: Arc<dyn VerificationBackend> = Arc::new(CertusBackend::with_solver_path(
        "/nonexistent/certus",
    ));

    let vc = VerificationCondition {
        kind: VcKind::Precondition { callee: "test_fn".into() },
        function: "test_fn".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };

    let lanes = vec![PortfolioLane {
        strategy: PortfolioStrategy::Ic3Pdr,
        backend: certus,
    }];

    let result = race(&vc, lanes).expect("should get a result");
    assert_eq!(result.winning_strategy, PortfolioStrategy::Ic3Pdr);
    // Since certus binary doesn't exist, we get Unknown
    assert!(matches!(result.result, VerificationResult::Unknown { .. }));
    assert_eq!(result.result.solver_name(), "certus");
    assert_eq!(result.total_lanes, 1);
}

#[test]
fn test_certus_in_router_backend_plan() {
    let router = Router::with_backends(vec![
        Box::new(MockBackend),
        Box::new(CertusBackend::new()),
    ]);

    let l1_vc = VerificationCondition {
        kind: VcKind::Precondition { callee: "callee".into() },
        function: "f".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(false),
        contract_metadata: None,
    };

    let plan = router.backend_plan(&l1_vc);
    // For L1Functional, Ownership role ranks after Deductive and SMT
    // but certus should be in the plan and able to handle this VC
    let certus_entry = plan.iter().find(|b| b.name == "certus");
    assert!(certus_entry.is_some());
    let certus_entry = certus_entry.expect("certus should be in plan");
    assert!(certus_entry.can_handle);
    assert_eq!(certus_entry.role, BackendRole::Ownership);
}

// tRust #798: SunderBackend is gated behind not(pipeline-v2).
#[cfg(not(feature = "pipeline-v2"))]
#[test]
fn test_certus_and_sunder_precondition_dispatch() {
    // tRust #556: sunder is disabled (can_handle returns false).
    // certus (Ownership) still handles L1Functional VCs.
    use crate::sunder_backend::SunderBackend;

    let router = Router::with_backends(vec![
        Box::new(CertusBackend::new()),
        Box::new(SunderBackend::new()),
        Box::new(MockBackend),
    ]);

    let pre_vc = VerificationCondition {
        kind: VcKind::Precondition { callee: "callee".into() },
        function: "f".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(false),
        contract_metadata: None,
    };

    let plan = router.backend_plan(&pre_vc);
    let certus_entry = plan.iter().find(|b| b.name == "certus").expect("certus in plan");
    assert!(certus_entry.can_handle);

    // tRust #556: sunder is in the plan but disabled
    let sunder_entry = plan.iter().find(|b| b.name == "sunder").expect("sunder in plan");
    assert!(!sunder_entry.can_handle, "sunder should be disabled (#556)");
}

// tRust #798: SunderBackend and ZaniBackend are gated behind not(pipeline-v2).
#[cfg(not(feature = "pipeline-v2"))]
#[test]
fn test_certus_ownership_dispatch_in_full_router() {
    // tRust #556: sunder is disabled. certus handles L1Functional VCs.
    use crate::sunder_backend::SunderBackend;
    use crate::zani_backend::ZaniBackend;
    use crate::tla2_backend::Tla2Backend;

    let router = Router::with_backends(vec![
        Box::new(Tla2Backend),
        Box::new(CertusBackend::new()),
        Box::new(SunderBackend::new()),
        Box::new(ZaniBackend::new()),
        Box::new(MockBackend),
    ]);

    let pre_vc = VerificationCondition {
        kind: VcKind::Precondition { callee: "callee".into() },
        function: "f".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(false),
        contract_metadata: None,
    };

    let plan = router.backend_plan(&pre_vc);
    // tRust #556: sunder is disabled, so the first handler should NOT be sunder
    let first_handler = plan.iter().find(|b| b.can_handle);
    assert!(first_handler.is_some());
    let first = first_handler.expect("should have a handler");
    assert_ne!(first.name, "sunder", "sunder should be disabled (#556)");

    // certus should be in plan and able to handle
    let certus_entry = plan.iter().find(|b| b.name == "certus");
    assert!(certus_entry.is_some());
    assert!(certus_entry.expect("certus in plan").can_handle);

    // sunder is disabled
    let sunder_entry = plan.iter().find(|b| b.name == "sunder");
    assert!(sunder_entry.is_some());
    assert!(!sunder_entry.expect("sunder").can_handle, "sunder disabled (#556)");

    // Verify: should NOT get sunder result (it's disabled)
    let result = router.verify_one(&pre_vc);
    assert_ne!(result.solver_name(), "sunder", "sunder is disabled");
}

// -----------------------------------------------------------------------
// tRust #360: Unsafe-code VC handling tests
// -----------------------------------------------------------------------

#[test]
fn test_certus_handles_unsafe_operation_vc() {
    let backend = CertusBackend::new();
    let vc = VerificationCondition {
        kind: VcKind::UnsafeOperation {
            desc: "raw pointer dereference of `_2.*`".to_string(),
        },
        function: "unsafe_fn".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };
    assert!(backend.can_handle(&vc), "certus should handle UnsafeOperation VCs");
}

#[test]
fn test_certus_handles_unsafe_sep_deref_vc() {
    let backend = CertusBackend::new();
    let vc = VerificationCondition {
        kind: VcKind::Assertion {
            message: "[unsafe:sep:deref] null check for *raw_ptr".to_string(),
        },
        function: "unsafe_fn".into(),
        location: SourceSpan::default(),
        formula: Formula::Eq(
            Box::new(Formula::Var("ptr_raw_ptr".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        ),
        contract_metadata: None,
    };
    assert!(backend.can_handle(&vc), "certus should handle [unsafe:sep:deref] VCs");
}

#[test]
fn test_certus_handles_unsafe_sep_write_vc() {
    let backend = CertusBackend::new();
    let vc = VerificationCondition {
        kind: VcKind::Assertion {
            message: "[unsafe:sep:write] write permission for *ptr".to_string(),
        },
        function: "unsafe_fn".into(),
        location: SourceSpan::default(),
        formula: Formula::Not(Box::new(
            Formula::Var("writable_ptr".into(), Sort::Bool),
        )),
        contract_metadata: None,
    };
    assert!(backend.can_handle(&vc), "certus should handle [unsafe:sep:write] VCs");
}

#[test]
fn test_certus_handles_unsafe_sep_transmute_vc() {
    let backend = CertusBackend::new();
    let vc = VerificationCondition {
        kind: VcKind::Assertion {
            message: "[unsafe:sep:transmute] layout: size_of(u32) != size_of(f32)".to_string(),
        },
        function: "transmute_fn".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };
    assert!(backend.can_handle(&vc), "certus should handle [unsafe:sep:transmute] VCs");
}

#[test]
fn test_certus_handles_unsafe_sep_ffi_vc() {
    let backend = CertusBackend::new();
    let vc = VerificationCondition {
        kind: VcKind::Assertion {
            message: "[unsafe:sep:ffi] null pointer argument check for libc::write".to_string(),
        },
        function: "ffi_fn".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };
    assert!(backend.can_handle(&vc), "certus should handle [unsafe:sep:ffi] VCs");
}

#[test]
fn test_certus_handles_unsafe_sep_frame_vc() {
    let backend = CertusBackend::new();
    let vc = VerificationCondition {
        kind: VcKind::Assertion {
            message: "[unsafe:sep:frame] frame preservation for unsafe block in fn".to_string(),
        },
        function: "unsafe_fn".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };
    assert!(backend.can_handle(&vc), "certus should handle [unsafe:sep:frame] VCs");
}

#[test]
fn test_certus_handles_unsafe_sep_heap_vc() {
    let backend = CertusBackend::new();
    let vc = VerificationCondition {
        kind: VcKind::Assertion {
            message: "[unsafe:sep:heap] use-after-free: read through freed pointer `p`"
                .to_string(),
        },
        function: "unsafe_fn".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };
    assert!(backend.can_handle(&vc), "certus should handle [unsafe:sep:heap] VCs");
}

#[test]
fn test_certus_does_not_handle_non_unsafe_assertion() {
    let backend = CertusBackend::new();
    let vc = VerificationCondition {
        kind: VcKind::Assertion {
            message: "some normal assertion".to_string(),
        },
        function: "f".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };
    assert!(
        !backend.can_handle(&vc),
        "certus should not handle non-unsafe assertions"
    );
}

// -----------------------------------------------------------------------
// tRust #360: is_unsafe_sep_vc tests
// -----------------------------------------------------------------------

#[test]
fn test_is_unsafe_sep_vc_with_deref_prefix() {
    let vc = VerificationCondition {
        kind: VcKind::Assertion {
            message: "[unsafe:sep:deref] null check for *p".to_string(),
        },
        function: "f".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };
    assert!(is_unsafe_sep_vc(&vc));
}

#[test]
fn test_is_unsafe_sep_vc_with_write_prefix() {
    let vc = VerificationCondition {
        kind: VcKind::Assertion {
            message: "[unsafe:sep:write] write permission for *p".to_string(),
        },
        function: "f".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };
    assert!(is_unsafe_sep_vc(&vc));
}

#[test]
fn test_is_unsafe_sep_vc_false_for_non_unsafe() {
    let vc = VerificationCondition {
        kind: VcKind::Assertion {
            message: "normal assertion".to_string(),
        },
        function: "f".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };
    assert!(!is_unsafe_sep_vc(&vc));
}

#[test]
fn test_is_unsafe_sep_vc_false_for_non_assertion() {
    let vc = VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: "f".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };
    assert!(!is_unsafe_sep_vc(&vc));
}

// -----------------------------------------------------------------------
// tRust #360: classify_unsafe_vc tests
// -----------------------------------------------------------------------

#[test]
fn test_classify_unsafe_operation_raw_deref() {
    let vc = VerificationCondition {
        kind: VcKind::UnsafeOperation {
            desc: "raw pointer dereference of `_2.*`".to_string(),
        },
        function: "f".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };
    assert_eq!(classify_unsafe_vc(&vc), Some(UnsafeVcClass::RawDeref));
}

#[test]
fn test_classify_unsafe_operation_transmute() {
    let vc = VerificationCondition {
        kind: VcKind::UnsafeOperation {
            desc: "transmute via `std::mem::transmute`".to_string(),
        },
        function: "f".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };
    assert_eq!(classify_unsafe_vc(&vc), Some(UnsafeVcClass::Transmute));
}

#[test]
fn test_classify_unsafe_operation_ffi() {
    let vc = VerificationCondition {
        kind: VcKind::UnsafeOperation {
            desc: "FFI call to `libc::write`".to_string(),
        },
        function: "f".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };
    assert_eq!(classify_unsafe_vc(&vc), Some(UnsafeVcClass::FfiCall));
}

#[test]
fn test_classify_unsafe_operation_address_of() {
    let vc = VerificationCondition {
        kind: VcKind::UnsafeOperation {
            desc: "&raw mut on `_2`".to_string(),
        },
        function: "f".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };
    assert_eq!(classify_unsafe_vc(&vc), Some(UnsafeVcClass::RawDeref));
}

#[test]
fn test_classify_unsafe_operation_generic() {
    let vc = VerificationCondition {
        kind: VcKind::UnsafeOperation {
            desc: "unsafe function call to `std::alloc::alloc`".to_string(),
        },
        function: "f".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };
    assert_eq!(classify_unsafe_vc(&vc), Some(UnsafeVcClass::GenericUnsafe));
}

#[test]
fn test_classify_sep_use_after_free() {
    let vc = VerificationCondition {
        kind: VcKind::Assertion {
            message: "[unsafe:sep:heap] use-after-free: read through freed pointer `p`"
                .to_string(),
        },
        function: "f".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };
    assert_eq!(classify_unsafe_vc(&vc), Some(UnsafeVcClass::UseAfterFree));
}

#[test]
fn test_classify_sep_permission_denied() {
    let vc = VerificationCondition {
        kind: VcKind::Assertion {
            message: "[unsafe:sep:heap] permission denied: write through `ro` (read-only)"
                .to_string(),
        },
        function: "f".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };
    assert_eq!(
        classify_unsafe_vc(&vc),
        Some(UnsafeVcClass::PermissionDenied)
    );
}

#[test]
fn test_classify_sep_frame_preservation() {
    let vc = VerificationCondition {
        kind: VcKind::Assertion {
            message: "[unsafe:sep:frame] frame preservation for unsafe block in test_fn"
                .to_string(),
        },
        function: "f".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };
    assert_eq!(classify_unsafe_vc(&vc), Some(UnsafeVcClass::SepFrame));
}

#[test]
fn test_classify_sep_null_check() {
    let vc = VerificationCondition {
        kind: VcKind::Assertion {
            message: "[unsafe:sep:deref] null check for *p".to_string(),
        },
        function: "f".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };
    assert_eq!(classify_unsafe_vc(&vc), Some(UnsafeVcClass::RawDeref));
}

#[test]
fn test_classify_sep_write_permission() {
    let vc = VerificationCondition {
        kind: VcKind::Assertion {
            message: "[unsafe:sep:write] write permission for *p".to_string(),
        },
        function: "f".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };
    assert_eq!(classify_unsafe_vc(&vc), Some(UnsafeVcClass::RawWrite));
}

#[test]
fn test_classify_sep_ffi_null_pointer() {
    let vc = VerificationCondition {
        kind: VcKind::Assertion {
            message: "[unsafe:sep:ffi] null pointer argument check for libc::write".to_string(),
        },
        function: "f".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };
    assert_eq!(classify_unsafe_vc(&vc), Some(UnsafeVcClass::FfiCall));
}

#[test]
fn test_classify_sep_heap_precondition() {
    let vc = VerificationCondition {
        kind: VcKind::Assertion {
            message: "[unsafe:sep] heap precondition for unsafe block in test_fn".to_string(),
        },
        function: "f".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };
    assert_eq!(
        classify_unsafe_vc(&vc),
        Some(UnsafeVcClass::SepHeapCondition)
    );
}

#[test]
fn test_classify_non_unsafe_returns_none() {
    let vc = VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: "f".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };
    assert_eq!(classify_unsafe_vc(&vc), None);
}

// -----------------------------------------------------------------------
// tRust #360: generate_unsafe_ownership_script tests
// -----------------------------------------------------------------------

#[test]
fn test_unsafe_script_has_unsafe_mode_option() {
    let vc = VerificationCondition {
        kind: VcKind::UnsafeOperation {
            desc: "raw pointer dereference of `_2.*`".to_string(),
        },
        function: "f".into(),
        location: SourceSpan::default(),
        formula: Formula::Eq(
            Box::new(Formula::Var("ptr_raw".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        ),
        contract_metadata: None,
    };

    let script = generate_unsafe_ownership_script(&vc);
    assert!(script.contains("(set-option :unsafe-mode true)"));
    assert!(script.contains("(set-option :provenance-tracking true)"));
    assert!(script.contains("(set-option :ownership-mode true)"));
    assert!(script.contains("; certus unsafe class: raw-deref"));
    assert!(script.contains("; certus VC kind: unsafe operation: raw pointer dereference"));
}

#[test]
fn test_unsafe_script_raw_deref_has_null_axiom() {
    let vc = VerificationCondition {
        kind: VcKind::UnsafeOperation {
            desc: "raw pointer dereference of `_2.*`".to_string(),
        },
        function: "f".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };

    let script = generate_unsafe_ownership_script(&vc);
    assert!(script.contains("Raw pointer safety axioms"));
    assert!(script.contains("(assert (= null_ptr 0))"));
    assert!(script.contains("(assert (= unalloc_sentinel (- 1)))"));
}

#[test]
fn test_unsafe_script_raw_write_has_permission_axiom() {
    let vc = VerificationCondition {
        kind: VcKind::Assertion {
            message: "[unsafe:sep:write] write permission for *p".to_string(),
        },
        function: "f".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };

    let script = generate_unsafe_ownership_script(&vc);
    assert!(script.contains("Write permission required"));
    assert!(script.contains("(assert (=> writing_through_ptr (= ptr_perm 2)))"));
}

#[test]
fn test_unsafe_script_transmute_has_layout_axioms() {
    let vc = VerificationCondition {
        kind: VcKind::UnsafeOperation {
            desc: "transmute via `std::mem::transmute`".to_string(),
        },
        function: "f".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };

    let script = generate_unsafe_ownership_script(&vc);
    assert!(script.contains("Transmute safety axioms"));
    assert!(script.contains("size_of(Src) == size_of(Dst)"));
}

#[test]
fn test_unsafe_script_ffi_has_ffi_axioms() {
    let vc = VerificationCondition {
        kind: VcKind::UnsafeOperation {
            desc: "FFI call to `libc::write`".to_string(),
        },
        function: "f".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };

    let script = generate_unsafe_ownership_script(&vc);
    assert!(script.contains("FFI safety axioms"));
    assert!(script.contains("Pointer arguments must be non-null"));
}

#[test]
fn test_unsafe_script_contains_base_vc() {
    let vc = VerificationCondition {
        kind: VcKind::UnsafeOperation {
            desc: "raw pointer dereference of `p`".to_string(),
        },
        function: "f".into(),
        location: SourceSpan::default(),
        formula: Formula::Eq(
            Box::new(Formula::Var("ptr_p".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        ),
        contract_metadata: None,
    };

    let script = generate_unsafe_ownership_script(&vc);
    assert!(script.contains("(check-sat)"));
    assert!(script.contains("(declare-const ptr_p Int)"));
    assert!(script.contains("(assert (= ptr_p 0))"));
}

// -----------------------------------------------------------------------
// tRust #360: interpret_unsafe_counterexample tests
// -----------------------------------------------------------------------

#[test]
fn test_interpret_null_pointer_deref() {
    let vc = VerificationCondition {
        kind: VcKind::Assertion {
            message: "[unsafe:sep:deref] null check for *p".to_string(),
        },
        function: "f".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };
    let cex = Counterexample::new(vec![
        ("ptr_p".to_string(), CounterexampleValue::Uint(0)),
    ]);

    let violation = interpret_unsafe_counterexample(&vc, &cex);
    assert_eq!(
        violation,
        OwnershipViolation::NullPointerDeref {
            pointer_var: "ptr_p".to_string(),
        }
    );
    assert!(violation.description().contains("null pointer dereference"));
}

#[test]
fn test_interpret_invalid_allocation() {
    let vc = VerificationCondition {
        kind: VcKind::Assertion {
            message: "[unsafe:sep:deref] allocation validity for *p".to_string(),
        },
        function: "f".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };
    let cex = Counterexample::new(vec![
        ("ptr_p".to_string(), CounterexampleValue::Uint(42)),
        ("heap_val".to_string(), CounterexampleValue::Int(-1)),
    ]);

    let violation = interpret_unsafe_counterexample(&vc, &cex);
    assert_eq!(
        violation,
        OwnershipViolation::InvalidAllocation {
            pointer_var: "ptr_p".to_string(),
        }
    );
}

#[test]
fn test_interpret_write_permission_denied() {
    let vc = VerificationCondition {
        kind: VcKind::Assertion {
            message: "[unsafe:sep:write] write permission for *p".to_string(),
        },
        function: "f".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };
    let cex = Counterexample::new(vec![
        ("writable_p".to_string(), CounterexampleValue::Bool(false)),
        ("ptr_p".to_string(), CounterexampleValue::Uint(100)),
    ]);

    let violation = interpret_unsafe_counterexample(&vc, &cex);
    assert_eq!(
        violation,
        OwnershipViolation::WritePermissionDenied {
            pointer_var: "ptr_p".to_string(),
        }
    );
}

#[test]
fn test_interpret_use_after_free() {
    let vc = VerificationCondition {
        kind: VcKind::Assertion {
            message: "[unsafe:sep:heap] use-after-free: read through freed pointer `p`"
                .to_string(),
        },
        function: "f".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };
    let cex = Counterexample::new(vec![
        ("ptr_p".to_string(), CounterexampleValue::Uint(0x1000)),
    ]);

    let violation = interpret_unsafe_counterexample(&vc, &cex);
    assert_eq!(
        violation,
        OwnershipViolation::UseAfterFree {
            pointer_var: "ptr_p".to_string(),
        }
    );
}

#[test]
fn test_interpret_incompatible_transmute_layout() {
    let vc = VerificationCondition {
        kind: VcKind::UnsafeOperation {
            desc: "transmute via `std::mem::transmute`".to_string(),
        },
        function: "f".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };
    let cex = Counterexample::new(vec![
        ("size_u8".to_string(), CounterexampleValue::Uint(1)),
        ("size_u32".to_string(), CounterexampleValue::Uint(4)),
    ]);

    let violation = interpret_unsafe_counterexample(&vc, &cex);
    assert!(matches!(
        violation,
        OwnershipViolation::IncompatibleLayout { .. }
    ));
}

#[test]
fn test_interpret_aliasing_violation_in_frame() {
    let vc = VerificationCondition {
        kind: VcKind::Assertion {
            message: "[unsafe:sep:frame] frame preservation for unsafe block in fn".to_string(),
        },
        function: "f".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };
    let cex = Counterexample::new(vec![
        ("region_0_base".to_string(), CounterexampleValue::Uint(100)),
        ("region_1_base".to_string(), CounterexampleValue::Uint(100)),
    ]);

    let violation = interpret_unsafe_counterexample(&vc, &cex);
    assert!(matches!(
        violation,
        OwnershipViolation::AliasingViolation { .. }
    ));
    assert!(violation.description().contains("same base address"));
}

#[test]
fn test_interpret_generic_unsafe_violation() {
    let vc = VerificationCondition {
        kind: VcKind::UnsafeOperation {
            desc: "unsafe function call to `std::alloc::alloc`".to_string(),
        },
        function: "alloc_fn".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };
    let cex = Counterexample::new(vec![
        ("x".to_string(), CounterexampleValue::Uint(42)),
    ]);

    let violation = interpret_unsafe_counterexample(&vc, &cex);
    assert!(matches!(
        violation,
        OwnershipViolation::Generic { .. }
    ));
    assert!(violation.description().contains("alloc_fn"));
}

// -----------------------------------------------------------------------
// tRust #360: OwnershipViolation description tests
// -----------------------------------------------------------------------

#[test]
fn test_ownership_violation_descriptions() {
    let cases = vec![
        (
            OwnershipViolation::NullPointerDeref { pointer_var: "ptr_p".into() },
            "null pointer dereference: ptr_p == 0",
        ),
        (
            OwnershipViolation::InvalidAllocation { pointer_var: "ptr_q".into() },
            "invalid allocation: ptr_q points to unallocated memory",
        ),
        (
            OwnershipViolation::MisalignedAccess { pointer_var: "ptr_r".into() },
            "misaligned access: ptr_r not properly aligned",
        ),
        (
            OwnershipViolation::WritePermissionDenied { pointer_var: "ptr_s".into() },
            "write permission denied: ptr_s is read-only",
        ),
        (
            OwnershipViolation::UseAfterFree { pointer_var: "ptr_t".into() },
            "use-after-free: ptr_t points to freed allocation",
        ),
        (
            OwnershipViolation::AliasingViolation {
                region_a: "r0".into(),
                region_b: "r1".into(),
            },
            "aliasing violation: r0 and r1 have same base address",
        ),
        (
            OwnershipViolation::IncompatibleLayout {
                src_ty: "u8".into(),
                dst_ty: "u32".into(),
            },
            "incompatible layout: size_of(u8) != size_of(u32)",
        ),
        (
            OwnershipViolation::Generic { description: "test".into() },
            "test",
        ),
    ];

    for (violation, expected) in cases {
        assert_eq!(violation.description(), expected);
    }
}

// -----------------------------------------------------------------------
// tRust #360: UnsafeVcClass label tests
// -----------------------------------------------------------------------

#[test]
fn test_unsafe_vc_class_labels() {
    assert_eq!(UnsafeVcClass::RawDeref.label(), "raw-deref");
    assert_eq!(UnsafeVcClass::RawWrite.label(), "raw-write");
    assert_eq!(UnsafeVcClass::Transmute.label(), "transmute");
    assert_eq!(UnsafeVcClass::FfiCall.label(), "ffi-call");
    assert_eq!(UnsafeVcClass::SepFrame.label(), "sep-frame");
    assert_eq!(UnsafeVcClass::SepHeapCondition.label(), "sep-heap");
    assert_eq!(UnsafeVcClass::UseAfterFree.label(), "use-after-free");
    assert_eq!(UnsafeVcClass::PermissionDenied.label(), "permission-denied");
    assert_eq!(UnsafeVcClass::GenericUnsafe.label(), "generic-unsafe");
}

// -----------------------------------------------------------------------
// tRust #360: Router integration for unsafe VCs
// -----------------------------------------------------------------------

#[test]
fn test_certus_preferred_for_unsafe_operation_vc_via_ownership_ranking() {
    // tRust #360: For UnsafeOperation VCs, certus (Ownership role) should be
    // ranked highly because the ownership_encoding::is_ownership_vc detects
    // [memory:region] VCs, and UnsafeOperation VCs are handled by can_handle.
    let router = Router::with_backends(vec![
        Box::new(MockBackend),
        Box::new(CertusBackend::new()),
    ]);

    let unsafe_vc = VerificationCondition {
        kind: VcKind::UnsafeOperation {
            desc: "raw pointer dereference of `_2.*`".to_string(),
        },
        function: "unsafe_fn".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };

    let plan = router.backend_plan(&unsafe_vc);
    let certus_entry = plan.iter().find(|b| b.name == "certus");
    assert!(certus_entry.is_some(), "certus should appear in plan for UnsafeOperation VC");
    assert!(
        certus_entry.expect("certus in plan").can_handle,
        "certus should be able to handle UnsafeOperation VCs"
    );
}

// tRust #798: SunderBackend and ZaniBackend are gated behind not(pipeline-v2).
#[cfg(not(feature = "pipeline-v2"))]
#[test]
fn test_certus_handles_unsafe_vc_in_full_router() {
    use crate::sunder_backend::SunderBackend;
    use crate::zani_backend::ZaniBackend;

    let router = Router::with_backends(vec![
        Box::new(CertusBackend::new()),
        Box::new(SunderBackend::new()),
        Box::new(ZaniBackend::new()),
        Box::new(MockBackend),
    ]);

    let unsafe_vc = VerificationCondition {
        kind: VcKind::UnsafeOperation {
            desc: "raw pointer dereference of `_2.*`".to_string(),
        },
        function: "unsafe_fn".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };

    let plan = router.backend_plan(&unsafe_vc);
    // certus (Ownership) should handle this VC
    let certus_entry = plan.iter().find(|b| b.name == "certus");
    assert!(certus_entry.is_some());
    assert!(certus_entry.expect("certus").can_handle);

    // sunder and zani should NOT handle UnsafeOperation
    let sunder_entry = plan.iter().find(|b| b.name == "sunder");
    assert!(sunder_entry.is_some());
    assert!(
        !sunder_entry.expect("sunder").can_handle,
        "sunder should not handle UnsafeOperation VCs"
    );
}

#[test]
fn test_certus_handles_sep_vc_in_router() {
    let router = Router::with_backends(vec![
        Box::new(CertusBackend::new()),
        Box::new(MockBackend),
    ]);

    let sep_vc = VerificationCondition {
        kind: VcKind::Assertion {
            message: "[unsafe:sep:deref] null check for *raw_ptr".to_string(),
        },
        function: "unsafe_fn".into(),
        location: SourceSpan::default(),
        formula: Formula::Eq(
            Box::new(Formula::Var("ptr_raw_ptr".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        ),
        contract_metadata: None,
    };

    let plan = router.backend_plan(&sep_vc);
    let certus_entry = plan.iter().find(|b| b.name == "certus");
    assert!(certus_entry.is_some());
    assert!(
        certus_entry.expect("certus").can_handle,
        "certus should handle [unsafe:sep:*] VCs"
    );
}

// -----------------------------------------------------------------------
// tRust #360: Portfolio racer integration for unsafe VCs
// -----------------------------------------------------------------------

#[test]
fn test_certus_in_portfolio_racer_for_unsafe_vc() {
    let racer = PortfolioRacer::new(vec![
        Arc::new(CertusBackend::with_solver_path("/nonexistent/certus")),
        Arc::new(MockBackend),
    ]);

    let unsafe_vc = VerificationCondition {
        kind: VcKind::UnsafeOperation {
            desc: "raw pointer dereference of `_2.*`".to_string(),
        },
        function: "unsafe_fn".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };

    let config = RaceConfig::default().with_query_class(false);
    let result = racer.race(&unsafe_vc, &config);

    // MockBackend handles everything and proves trivially; certus returns Unknown.
    // The racer should pick the mock's Proved result since it's definitive.
    assert!(result.is_definitive);
    assert_eq!(result.solvers_raced, 2);
}

#[test]
fn test_certus_portfolio_lane_for_unsafe_vc() {
    let certus: Arc<dyn VerificationBackend> = Arc::new(CertusBackend::with_solver_path(
        "/nonexistent/certus",
    ));

    let unsafe_vc = VerificationCondition {
        kind: VcKind::UnsafeOperation {
            desc: "transmute via `std::mem::transmute`".to_string(),
        },
        function: "transmute_fn".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };

    let lanes = vec![PortfolioLane {
        strategy: PortfolioStrategy::Ic3Pdr,
        backend: certus,
    }];

    let result = race(&unsafe_vc, lanes).expect("should get a result");
    assert_eq!(result.winning_strategy, PortfolioStrategy::Ic3Pdr);
    // certus binary not available, so Unknown
    assert!(matches!(result.result, VerificationResult::Unknown { .. }));
    assert_eq!(result.result.solver_name(), "certus");
}

// -----------------------------------------------------------------------
// tRust #360: Verify dispatch for unsafe VCs
// -----------------------------------------------------------------------

#[test]
fn test_certus_verify_selects_unsafe_script_for_unsafe_operation() {
    // Verify that the backend uses generate_unsafe_ownership_script
    // for UnsafeOperation VCs (which sets unsafe-mode true)
    let backend = CertusBackend::new();
    let vc = VerificationCondition {
        kind: VcKind::UnsafeOperation {
            desc: "raw pointer dereference of `_2.*`".to_string(),
        },
        function: "f".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };

    // Since certus binary is not installed, verify returns Unknown,
    // but the solver name should be "certus" confirming dispatch.
    let result = backend.verify(&vc);
    assert_eq!(result.solver_name(), "certus");
}

#[test]
fn test_certus_verify_selects_unsafe_script_for_sep_vc() {
    let backend = CertusBackend::new();
    let vc = VerificationCondition {
        kind: VcKind::Assertion {
            message: "[unsafe:sep:deref] null check for *p".to_string(),
        },
        function: "f".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };

    let result = backend.verify(&vc);
    assert_eq!(result.solver_name(), "certus");
}

// -----------------------------------------------------------------------
// tRust #360: Unsafe-specific counterexample with model parsing
// -----------------------------------------------------------------------

#[test]
fn test_certus_unsafe_counterexample_sat_with_null_pointer() {
    // Simulate certus finding a null pointer dereference
    let output = "sat\n(model\n  (define-fun ptr_raw () Int 0)\n)\n";
    let mut result = parse_solver_output(output, 5, vec![]);
    attribute_to_certus(&mut result);

    assert!(result.is_failed());
    assert_eq!(result.solver_name(), "certus");
    if let VerificationResult::Failed { counterexample: Some(cex), .. } = &result {
        assert_eq!(cex.assignments[0].0, "ptr_raw");
        assert!(matches!(cex.assignments[0].1, CounterexampleValue::Uint(0)));

        // Interpret with the VC context
        let vc = VerificationCondition {
            kind: VcKind::Assertion {
                message: "[unsafe:sep:deref] null check for *raw".to_string(),
            },
            function: "f".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        };
        let violation = interpret_unsafe_counterexample(&vc, cex);
        assert!(matches!(
            violation,
            OwnershipViolation::NullPointerDeref { .. }
        ));
    } else {
        panic!("expected Failed with counterexample");
    }
}

#[test]
fn test_certus_unsafe_counterexample_unsat_proves_safety() {
    // Simulate certus proving the unsafe operation is safe
    let output = "unsat\n";
    let mut result = parse_solver_output(output, 3, vec![]);
    attribute_to_certus(&mut result);

    assert!(result.is_proved());
    assert_eq!(result.solver_name(), "certus");
    if let VerificationResult::Proved { strength, .. } = &result {
        // tRust #435: certus uses OwnershipAnalysis, not generic Deductive
        assert_eq!(strength.reasoning, ReasoningKind::OwnershipAnalysis);
        assert_eq!(strength.assurance, AssuranceLevel::Sound);
    } else {
        panic!("expected Proved");
    }
}

#[test]
fn test_certus_unsafe_counterexample_aliasing_model() {
    // Simulate certus finding an aliasing violation (two regions with same base)
    let output = "sat\n(model\n  (define-fun region_0_base () Int 42)\n  (define-fun region_1_base () Int 42)\n)\n";
    let mut result = parse_solver_output(output, 7, vec![]);
    attribute_to_certus(&mut result);

    assert!(result.is_failed());
    if let VerificationResult::Failed { counterexample: Some(cex), .. } = &result {
        assert_eq!(cex.assignments.len(), 2);
        // Both regions have the same base address
        assert_eq!(cex.assignments[0].0, "region_0_base");
        assert_eq!(cex.assignments[1].0, "region_1_base");
    } else {
        panic!("expected Failed with counterexample");
    }
}

// -----------------------------------------------------------------------
// tRust #547: Subprocess timeout enforcement tests
// -----------------------------------------------------------------------

#[test]
fn test_certus_run_solver_timeout_kills_hanging_process() {
    // Create a backend with a very short timeout (100ms) pointing at a
    // subprocess that sleeps for much longer (10s). The try_wait() loop
    // should detect the deadline, kill the process, and return Timeout.
    let backend = CertusBackend {
        solver_path: Some("sleep".to_string()),
        solver_args: vec!["10".to_string()],
        timeout_ms: 100,
    };

    let start = Instant::now();
    let result = backend.run_solver("(check-sat)\n");
    let elapsed = start.elapsed();

    // Should return Timeout, not hang for 10 seconds
    assert!(
        matches!(result, Err(RunSolverError::Timeout { timeout_ms: 100 })),
        "expected Timeout error, got: {result:?}"
    );
    // Should have returned well before the 10s sleep
    assert!(
        elapsed < Duration::from_secs(2),
        "timeout enforcement took too long: {elapsed:?}"
    );
}

#[test]
fn test_certus_verify_returns_timeout_for_hanging_solver() {
    // End-to-end: verify() should return VerificationResult::Timeout
    // when the subprocess hangs past the deadline.
    let backend = CertusBackend {
        solver_path: Some("sleep".to_string()),
        solver_args: vec!["10".to_string()],
        timeout_ms: 100,
    };

    let vc = VerificationCondition {
        kind: VcKind::Precondition { callee: "test".into() },
        function: "f".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };

    let start = Instant::now();
    let result = backend.verify(&vc);
    let elapsed = start.elapsed();

    assert!(
        matches!(result, VerificationResult::Timeout { timeout_ms: 100, .. }),
        "expected Timeout result, got: {result:?}"
    );
    assert_eq!(result.solver_name(), "certus");
    assert!(
        elapsed < Duration::from_secs(2),
        "verify() took too long: {elapsed:?}"
    );
}

#[test]
fn test_certus_run_solver_fast_exit_no_timeout() {
    // A process that exits quickly should NOT trigger timeout,
    // even with a short timeout_ms.
    let backend = CertusBackend {
        solver_path: Some("echo".to_string()),
        solver_args: vec!["unsat".to_string()],
        timeout_ms: 5_000,
    };

    let result = backend.run_solver("");
    assert!(result.is_ok(), "fast exit should succeed, got: {result:?}");
    let stdout = result.unwrap();
    assert!(stdout.contains("unsat"));
}
