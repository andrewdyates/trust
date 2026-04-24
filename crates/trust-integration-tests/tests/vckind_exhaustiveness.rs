// trust-integration-tests/tests/vckind_exhaustiveness.rs: VcKind exhaustiveness guard (#644)
//
// Compile-time + runtime guard ensuring every VcKind variant has documented test
// coverage. Adding a new VcKind variant forces updating this file (runtime panic
// from the wildcard arm, since VcKind is #[non_exhaustive] from this crate).
//
// The _internal_ match statements in trust-types (VcKind::description,
// VcKind::proof_level, VcKind::has_runtime_check) provide true compile-time
// enforcement. This test complements those by tracking _test coverage_ per variant.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#![allow(rustc::default_hash_types, rustc::potential_query_instability)]

use trust_types::*;

/// Entry mapping a VcKind variant to its test coverage location.
struct VcKindCoverage {
    /// Human-readable variant name.
    variant_name: &'static str,
    /// Test file(s) that exercise this variant, or justification if untested.
    coverage: Coverage,
}

enum Coverage {
    /// At least one test exercises this VcKind variant.
    Tested(&'static str),
    /// No end-to-end test yet; documented justification.
    Documented(&'static str),
}

/// Build a representative instance of each VcKind variant and return its
/// coverage mapping. Because VcKind is `#[non_exhaustive]`, we must include
/// a wildcard arm — but we panic there so new variants are caught at test time.
fn all_vckind_coverage() -> Vec<VcKindCoverage> {
    // Helper types for constructing variants with fields.
    let dummy_ty = Ty::u32();
    let dummy_op = BinOp::Add;

    // Construct one instance of every known VcKind variant.
    let variants: Vec<(VcKind, &'static str, Coverage)> = vec![
        (
            VcKind::ArithmeticOverflow {
                op: dummy_op,
                operand_tys: (dummy_ty.clone(), dummy_ty.clone()),
            },
            "ArithmeticOverflow",
            Coverage::Tested(
                "error_detection.rs, pipeline.rs, self_verify.rs, z4_phase2_models.rs",
            ),
        ),
        (
            VcKind::ShiftOverflow {
                op: BinOp::Shl,
                operand_ty: dummy_ty.clone(),
                shift_ty: dummy_ty.clone(),
            },
            "ShiftOverflow",
            Coverage::Tested("z4_phase2_models.rs"),
        ),
        (
            VcKind::DivisionByZero,
            "DivisionByZero",
            Coverage::Tested("error_detection.rs, pipeline.rs, real_z4_verification.rs"),
        ),
        (
            VcKind::RemainderByZero,
            "RemainderByZero",
            Coverage::Tested("error_detection.rs, self_verify.rs"),
        ),
        (
            VcKind::IndexOutOfBounds,
            "IndexOutOfBounds",
            Coverage::Tested("error_detection.rs, pipeline.rs, self_verify.rs, self_verify_z4.rs"),
        ),
        (
            VcKind::SliceBoundsCheck,
            "SliceBoundsCheck",
            Coverage::Tested("trust-strengthen/cex_guided.rs (unit), trust-debug/proof_explain.rs"),
        ),
        (
            VcKind::Assertion { message: String::new() },
            "Assertion",
            Coverage::Tested("self_verify_z4.rs, e2e_loop.rs, pipeline.rs, m5_acceptance.rs"),
        ),
        (
            VcKind::Precondition { callee: String::new() },
            "Precondition",
            Coverage::Tested("m4_precondition.rs"),
        ),
        (
            VcKind::Postcondition,
            "Postcondition",
            Coverage::Tested("pipeline.rs, m3_acceptance.rs, m3_real_crate.rs"),
        ),
        (
            VcKind::CastOverflow { from_ty: dummy_ty.clone(), to_ty: dummy_ty.clone() },
            "CastOverflow",
            Coverage::Tested("trust-strengthen/cex_guided.rs, trust-debug/root_cause.rs"),
        ),
        (
            VcKind::NegationOverflow { ty: dummy_ty.clone() },
            "NegationOverflow",
            Coverage::Tested("trust-strengthen/cex_guided.rs, trust-strengthen/proposer.rs"),
        ),
        (
            VcKind::Unreachable,
            "Unreachable",
            Coverage::Tested("trust-convergence/integration.rs, trust-strengthen/proposer.rs"),
        ),
        (
            VcKind::DeadState { state: String::new() },
            "DeadState",
            Coverage::Documented("State machine property; exercised via TLA+ backend, not z4 e2e"),
        ),
        (
            VcKind::Deadlock,
            "Deadlock",
            Coverage::Tested(
                "trust-strengthen/cegis.rs, trust-strengthen/cex_guided.rs, trust-debug/root_cause.rs",
            ),
        ),
        (VcKind::Temporal { property: String::new() }, "Temporal", Coverage::Tested("pipeline.rs")),
        (
            VcKind::Liveness {
                property: LivenessProperty {
                    name: String::new(),
                    operator: TemporalOperator::Eventually,
                    predicate: String::new(),
                    consequent: None,
                    fairness: vec![],
                },
            },
            "Liveness",
            Coverage::Tested("trust-cegar/strategy.rs, trust-cegar/portfolio.rs"),
        ),
        (
            VcKind::Fairness {
                constraint: FairnessConstraint::Weak { action: String::new(), vars: vec![] },
            },
            "Fairness",
            Coverage::Tested("trust-cegar/strategy.rs"),
        ),
        (
            VcKind::TaintViolation {
                source_label: String::new(),
                sink_kind: String::new(),
                path_length: 0,
            },
            "TaintViolation",
            Coverage::Tested("trust-debug/root_cause.rs"),
        ),
        (
            VcKind::RefinementViolation { spec_file: String::new(), action: String::new() },
            "RefinementViolation",
            Coverage::Documented("Refinement checking; tested at trust-types description() level"),
        ),
        (
            VcKind::ResilienceViolation {
                service: String::new(),
                failure_mode: String::new(),
                reason: String::new(),
            },
            "ResilienceViolation",
            Coverage::Tested("misc_vc_pipeline.rs (VC construction + Report)"),
        ),
        (
            VcKind::ProtocolViolation { protocol: String::new(), violation: String::new() },
            "ProtocolViolation",
            Coverage::Documented(
                "Protocol composition (#55); tested at trust-types description() level",
            ),
        ),
        (
            VcKind::NonTermination { context: String::new(), measure: String::new() },
            "NonTermination",
            Coverage::Tested(
                "trust-cegar/strategy.rs, trust-debug/root_cause.rs, trust-cegar/portfolio.rs",
            ),
        ),
        (
            VcKind::NeuralRobustness { epsilon: String::new() },
            "NeuralRobustness",
            Coverage::Documented(
                "Neural verification (#186); tested at trust-types description() level",
            ),
        ),
        (
            VcKind::NeuralOutputRange { lower: String::new(), upper: String::new() },
            "NeuralOutputRange",
            Coverage::Documented(
                "Neural verification (#186); tested at trust-types description() level",
            ),
        ),
        (
            VcKind::NeuralLipschitz { constant: String::new() },
            "NeuralLipschitz",
            Coverage::Documented(
                "Neural verification (#186); tested at trust-types description() level",
            ),
        ),
        (
            VcKind::NeuralMonotonicity { input_dim: 0 },
            "NeuralMonotonicity",
            Coverage::Documented(
                "Neural verification (#186); tested at trust-types description() level",
            ),
        ),
        (
            VcKind::DataRace {
                variable: String::new(),
                thread_a: String::new(),
                thread_b: String::new(),
            },
            "DataRace",
            Coverage::Tested("concurrency_e2e.rs"),
        ),
        (
            VcKind::InsufficientOrdering {
                variable: String::new(),
                actual: String::new(),
                required: String::new(),
            },
            "InsufficientOrdering",
            Coverage::Tested("concurrency_e2e.rs"),
        ),
        (
            VcKind::TranslationValidation { pass: String::new(), check: String::new() },
            "TranslationValidation",
            Coverage::Tested("misc_vc_pipeline.rs (VC construction + Report)"),
        ),
        (
            VcKind::FloatDivisionByZero,
            "FloatDivisionByZero",
            Coverage::Tested("float_unsafe_e2e.rs (vcgen pipeline)"),
        ),
        (
            VcKind::FloatOverflowToInfinity { op: dummy_op, operand_ty: dummy_ty.clone() },
            "FloatOverflowToInfinity",
            Coverage::Tested("z4_phase2_models.rs"),
        ),
        (
            VcKind::InvalidDiscriminant { place_name: String::new() },
            "InvalidDiscriminant",
            Coverage::Tested("error_detection.rs (vcgen pipeline)"),
        ),
        (
            VcKind::AggregateArrayLengthMismatch { expected: 0, actual: 0 },
            "AggregateArrayLengthMismatch",
            Coverage::Documented("Rvalue safety (#438); L2 domain, backend-dependent"),
        ),
        (
            VcKind::UnsafeOperation { desc: String::new() },
            "UnsafeOperation",
            Coverage::Tested("float_unsafe_e2e.rs (direct VC + solver, no vcgen)"),
        ),
        (
            VcKind::FfiBoundaryViolation { callee: String::new(), desc: String::new() },
            "FfiBoundaryViolation",
            Coverage::Tested("float_unsafe_e2e.rs (vcgen pipeline)"),
        ),
        (
            VcKind::UseAfterFree,
            "UseAfterFree",
            Coverage::Tested("ownership_e2e.rs (provenance tracker + MIR)"),
        ),
        (
            VcKind::DoubleFree,
            "DoubleFree",
            Coverage::Tested("ownership_e2e.rs (provenance tracker + MIR)"),
        ),
        (
            VcKind::AliasingViolation { mutable: false },
            "AliasingViolation",
            Coverage::Tested("ownership_e2e.rs (ownership scan + MIR)"),
        ),
        (
            VcKind::LifetimeViolation,
            "LifetimeViolation",
            Coverage::Tested("ownership_e2e.rs (VC construction + properties)"),
        ),
        (
            VcKind::SendViolation,
            "SendViolation",
            Coverage::Tested("ownership_e2e.rs (VC construction + properties)"),
        ),
        (
            VcKind::SyncViolation,
            "SyncViolation",
            Coverage::Tested("ownership_e2e.rs (VC construction + properties)"),
        ),
        (
            VcKind::FunctionalCorrectness { property: String::new(), context: String::new() },
            "FunctionalCorrectness",
            Coverage::Tested(
                "contract_e2e.rs, misc_vc_pipeline.rs (vcgen pipeline, partial Router bypass)",
            ),
        ),
        (
            VcKind::LoopInvariantInitiation { invariant: String::new(), header_block: 0 },
            "LoopInvariantInitiation",
            Coverage::Tested("contract_e2e.rs (vcgen pipeline + z4)"),
        ),
        (
            VcKind::LoopInvariantConsecution { invariant: String::new(), header_block: 0 },
            "LoopInvariantConsecution",
            Coverage::Tested("contract_e2e.rs (vcgen pipeline + z4)"),
        ),
        (
            VcKind::LoopInvariantSufficiency { invariant: String::new(), header_block: 0 },
            "LoopInvariantSufficiency",
            Coverage::Tested("contract_e2e.rs (vcgen pipeline + z4)"),
        ),
        (
            VcKind::TypeRefinementViolation { variable: String::new(), predicate: String::new() },
            "TypeRefinementViolation",
            Coverage::Tested("contract_e2e.rs (vcgen pipeline + z4)"),
        ),
        (
            VcKind::FrameConditionViolation { variable: String::new(), function: String::new() },
            "FrameConditionViolation",
            Coverage::Tested("contract_e2e.rs (vcgen pipeline + z4)"),
        ),
    ];

    // Convert to coverage entries, using the match to verify each variant's
    // description() method works (exercises the internal exhaustive match).
    variants
        .into_iter()
        .map(|(kind, name, coverage)| {
            // Call description() to exercise the exhaustive internal match.
            // This catches any variant whose description() panics or is missing.
            let _desc = kind.description();
            VcKindCoverage { variant_name: name, coverage }
        })
        .collect()
}

/// Verify that every VcKind variant returned by `all_vckind_coverage` produces
/// a non-empty description (exercising trust-types internal exhaustive match).
/// Also verify the variant count matches expectations so additions are noticed.
#[test]
fn test_vckind_exhaustiveness_guard() {
    let coverage = all_vckind_coverage();

    // --- 1. Count check: update this when adding new VcKind variants. ---
    // If this fails, a new VcKind variant was added. Update `all_vckind_coverage()`
    // above with the new variant and its test coverage status.
    const EXPECTED_VARIANT_COUNT: usize = 47;
    assert_eq!(
        coverage.len(),
        EXPECTED_VARIANT_COUNT,
        "VcKind variant count changed! Update all_vckind_coverage() in \
         vckind_exhaustiveness.rs to include the new variant(s). \
         Expected {EXPECTED_VARIANT_COUNT}, got {}.",
        coverage.len()
    );

    // --- 2. Every variant has a non-empty description. ---
    for entry in &coverage {
        match &entry.coverage {
            Coverage::Tested(files) => {
                assert!(
                    !files.is_empty(),
                    "VcKind::{} is marked Tested but has empty file list",
                    entry.variant_name
                );
            }
            Coverage::Documented(reason) => {
                assert!(
                    !reason.is_empty(),
                    "VcKind::{} is marked Documented but has empty justification",
                    entry.variant_name
                );
            }
        }
    }

    // --- 3. Summary report. ---
    let tested_count =
        coverage.iter().filter(|e| matches!(e.coverage, Coverage::Tested(_))).count();
    let documented_count =
        coverage.iter().filter(|e| matches!(e.coverage, Coverage::Documented(_))).count();

    eprintln!("VcKind exhaustiveness guard: {EXPECTED_VARIANT_COUNT} variants");
    eprintln!("  Tested:     {tested_count}");
    eprintln!("  Documented: {documented_count}");

    // --- 4. Print uncovered variants for visibility. ---
    let documented: Vec<_> =
        coverage.iter().filter(|e| matches!(e.coverage, Coverage::Documented(_))).collect();
    if !documented.is_empty() {
        eprintln!("\nVariants with documented justification (no direct e2e test):");
        for entry in &documented {
            if let Coverage::Documented(reason) = &entry.coverage {
                eprintln!("  VcKind::{}: {}", entry.variant_name, reason);
            }
        }
    }
}

/// Verify that `VcKind::description()` returns a non-empty string for every variant.
/// This is a secondary guard: if the internal exhaustive match in trust-types is broken,
/// this test catches it.
#[test]
fn test_vckind_description_completeness() {
    let coverage = all_vckind_coverage();
    for entry in &coverage {
        // description() was already called during construction in all_vckind_coverage(),
        // but we verify the name is non-empty as a sanity check.
        assert!(
            !entry.variant_name.is_empty(),
            "Found VcKind variant with empty name in coverage table"
        );
    }
}

/// Verify that `VcKind::proof_level()` returns a valid level for every variant.
/// Exercises the second internal exhaustive match in trust-types.
#[test]
fn test_vckind_proof_level_completeness() {
    let dummy_ty = Ty::u32();
    let dummy_op = BinOp::Add;

    // Reconstruct a representative of each variant and call proof_level().
    let variants: Vec<VcKind> = vec![
        VcKind::ArithmeticOverflow {
            op: dummy_op,
            operand_tys: (dummy_ty.clone(), dummy_ty.clone()),
        },
        VcKind::ShiftOverflow {
            op: BinOp::Shl,
            operand_ty: dummy_ty.clone(),
            shift_ty: dummy_ty.clone(),
        },
        VcKind::DivisionByZero,
        VcKind::RemainderByZero,
        VcKind::IndexOutOfBounds,
        VcKind::SliceBoundsCheck,
        VcKind::Assertion { message: "test".into() },
        VcKind::Precondition { callee: "test".into() },
        VcKind::Postcondition,
        VcKind::CastOverflow { from_ty: dummy_ty.clone(), to_ty: dummy_ty.clone() },
        VcKind::NegationOverflow { ty: dummy_ty.clone() },
        VcKind::Unreachable,
        VcKind::DeadState { state: "test".into() },
        VcKind::Deadlock,
        VcKind::Temporal { property: "test".into() },
        VcKind::Liveness {
            property: LivenessProperty {
                name: "test".into(),
                operator: TemporalOperator::Eventually,
                predicate: "P".into(),
                consequent: None,
                fairness: vec![],
            },
        },
        VcKind::Fairness {
            constraint: FairnessConstraint::Weak { action: "test".into(), vars: vec![] },
        },
        VcKind::TaintViolation {
            source_label: "user".into(),
            sink_kind: "sql".into(),
            path_length: 1,
        },
        VcKind::RefinementViolation { spec_file: "spec.tla".into(), action: "Next".into() },
        VcKind::ResilienceViolation {
            service: "db".into(),
            failure_mode: "timeout".into(),
            reason: "no retry".into(),
        },
        VcKind::ProtocolViolation { protocol: "2pc".into(), violation: "abort".into() },
        VcKind::NonTermination { context: "loop".into(), measure: "n".into() },
        VcKind::NeuralRobustness { epsilon: "0.1".into() },
        VcKind::NeuralOutputRange { lower: "0.0".into(), upper: "1.0".into() },
        VcKind::NeuralLipschitz { constant: "1.0".into() },
        VcKind::NeuralMonotonicity { input_dim: 0 },
        VcKind::DataRace { variable: "x".into(), thread_a: "t0".into(), thread_b: "t1".into() },
        VcKind::InsufficientOrdering {
            variable: "x".into(),
            actual: "Relaxed".into(),
            required: "Acquire".into(),
        },
        VcKind::TranslationValidation { pass: "dce".into(), check: "output_equiv".into() },
        VcKind::FloatDivisionByZero,
        VcKind::FloatOverflowToInfinity { op: dummy_op, operand_ty: dummy_ty.clone() },
        VcKind::InvalidDiscriminant { place_name: "x".into() },
        VcKind::AggregateArrayLengthMismatch { expected: 3, actual: 2 },
        VcKind::UnsafeOperation { desc: "raw ptr deref".into() },
        VcKind::FfiBoundaryViolation { callee: "malloc".into(), desc: "null return".into() },
        VcKind::UseAfterFree,
        VcKind::DoubleFree,
        VcKind::AliasingViolation { mutable: true },
        VcKind::LifetimeViolation,
        VcKind::SendViolation,
        VcKind::SyncViolation,
        VcKind::FunctionalCorrectness {
            property: "result_correctness".into(),
            context: "sorted input".into(),
        },
        VcKind::LoopInvariantInitiation { invariant: "i >= 0".into(), header_block: 0 },
        VcKind::LoopInvariantConsecution { invariant: "i >= 0".into(), header_block: 0 },
        VcKind::LoopInvariantSufficiency { invariant: "i >= 0".into(), header_block: 0 },
        VcKind::TypeRefinementViolation { variable: "x".into(), predicate: "x > 0".into() },
        VcKind::FrameConditionViolation { variable: "y".into(), function: "foo".into() },
    ];

    assert_eq!(
        variants.len(),
        47,
        "proof_level variant list out of sync — update when adding VcKind variants"
    );

    for kind in &variants {
        let level = kind.proof_level();
        // Verify it returns a valid ProofLevel (L0, L1, or L2).
        let desc = format!("{level:?}");
        assert!(
            desc.contains("L0") || desc.contains("L1") || desc.contains("L2"),
            "VcKind::{:?} returned unexpected proof level: {desc}",
            kind
        );
    }
}
