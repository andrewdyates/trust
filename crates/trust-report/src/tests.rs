//! Tests for trust-report core functionality.
//!
//! Author: Andrew Yates <andrew@andrewdyates.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap; // tRust: BTreeMap for deterministic output (#827)

use trust_types::*;

use crate::crate_report::{
    build_crate_verification_report, build_crate_verification_report_with_policy,
    format_crate_verification_summary,
};
use crate::formatting::proof_evidence_label;
use crate::legacy::{build_report, format_summary};
use crate::report_builder::vc_kind_tag;
use crate::{
    SCHEMA_VERSION, TRUST_VERSION, build_json_report, build_json_report_from_annotations,
    build_json_report_with_policy, format_json_summary, write_json_report, write_ndjson,
    write_ndjson_report,
};

fn annotation_obligation(
    description: &str,
    kind: &str,
    status: AnnotationStatus,
    proof_level: ProofLevel,
    time_ms: u64,
    location: Option<SourceSpan>,
) -> ObligationAnnotation {
    ObligationAnnotation {
        description: description.to_string(),
        kind: kind.to_string(),
        proof_level,
        status,
        strength: matches!(status, AnnotationStatus::Proved).then_some(ProofStrength::smt_unsat()),
        solver: "z4".into(),
        time_ms,
        location,
        counterexample: matches!(status, AnnotationStatus::Failed)
            .then(|| Counterexample::new(vec![("x".to_string(), CounterexampleValue::Int(-1))])),
        fingerprint: [1, 2],
    }
}

fn annotation_summary(obligations: &[ObligationAnnotation]) -> AnnotationSummary {
    AnnotationSummary {
        total: obligations.len(),
        proved: obligations
            .iter()
            .filter(|obligation| obligation.status == AnnotationStatus::Proved)
            .count(),
        failed: obligations
            .iter()
            .filter(|obligation| obligation.status == AnnotationStatus::Failed)
            .count(),
        unknown: obligations
            .iter()
            .filter(|obligation| {
                matches!(obligation.status, AnnotationStatus::Unknown | AnnotationStatus::Timeout)
            })
            .count(),
        runtime_checked: obligations
            .iter()
            .filter(|obligation| obligation.status == AnnotationStatus::RuntimeChecked)
            .count(),
        max_level: obligations.iter().map(|obligation| obligation.proof_level).max(),
    }
}

fn proof_annotation(
    function_name: &str,
    function_path: &str,
    obligations: Vec<ObligationAnnotation>,
) -> ProofAnnotation {
    ProofAnnotation {
        function_name: function_name.to_string(),
        function_path: function_path.to_string(),
        summary: annotation_summary(&obligations),
        obligations,
        certificate: Some(ProofCertificateRef {
            prover: "z4".to_string(),
            vc_fingerprint: [7, 11],
            prover_version: "1.0.0".to_string(),
        }),
    }
}

/// Build a standard test fixture with mixed results for get_midpoint.
fn midpoint_results() -> Vec<(VerificationCondition, VerificationResult)> {
    vec![
        (
            VerificationCondition {
                kind: VcKind::ArithmeticOverflow {
                    op: BinOp::Add,
                    operand_tys: (Ty::usize(), Ty::usize()),
                },
                function: "get_midpoint".into(),
                location: SourceSpan {
                    file: "src/midpoint.rs".to_string(),
                    line_start: 5,
                    col_start: 5,
                    line_end: 5,
                    col_end: 10,
                },
                formula: Formula::Bool(true),
                contract_metadata: None,
            },
            VerificationResult::Failed {
                solver: "z4".into(),
                time_ms: 3,
                counterexample: Some(Counterexample::new(vec![
                    ("a".to_string(), CounterexampleValue::Uint(u64::MAX as u128)),
                    ("b".to_string(), CounterexampleValue::Uint(1)),
                ])),
            },
        ),
        (
            VerificationCondition {
                kind: VcKind::DivisionByZero,
                function: "get_midpoint".into(),
                location: SourceSpan {
                    file: "src/midpoint.rs".to_string(),
                    line_start: 5,
                    col_start: 18,
                    line_end: 5,
                    col_end: 23,
                },
                formula: Formula::Bool(false),
                contract_metadata: None,
            },
            VerificationResult::Proved {
                solver: "z4".into(),
                time_ms: 1,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: None,
                solver_warnings: None,
            },
        ),
    ]
}

/// Build test data with multiple functions and all outcome types.
fn multi_function_results() -> Vec<(VerificationCondition, VerificationResult)> {
    let mut results = midpoint_results();
    results.push((
        VerificationCondition {
            kind: VcKind::IndexOutOfBounds,
            function: "lookup".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        },
        VerificationResult::Unknown {
            solver: "z4".into(),
            time_ms: 50,
            reason: "nonlinear arithmetic".to_string(),
        },
    ));
    results.push((
        VerificationCondition {
            kind: VcKind::Postcondition,
            function: "compute".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        },
        VerificationResult::Timeout { solver: "z4".into(), timeout_ms: 5000 },
    ));
    results.push((
        VerificationCondition {
            kind: VcKind::ArithmeticOverflow {
                op: BinOp::Mul,
                operand_tys: (Ty::i32(), Ty::i32()),
            },
            function: "compute".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        },
        VerificationResult::Proved {
            solver: "z4".into(),
            time_ms: 2,
            strength: ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: None,
        },
    ));
    results
}

/// Build a report that contains a runtime-checked obligation.
fn runtime_checked_report() -> JsonProofReport {
    JsonProofReport {
        metadata: ReportMetadata {
            schema_version: SCHEMA_VERSION.to_string(),
            trust_version: TRUST_VERSION.to_string(),
            timestamp: "0".to_string(),
            total_time_ms: 11,
        },
        crate_name: "runtime_checked".to_string(),
        summary: CrateSummary {
            functions_analyzed: 1,
            functions_verified: 0,
            functions_runtime_checked: 1,
            functions_with_violations: 0,
            functions_inconclusive: 0,
            total_obligations: 1,
            total_proved: 0,
            total_runtime_checked: 1,
            total_failed: 0,
            total_unknown: 0,
            verdict: CrateVerdict::RuntimeChecked,
        },
        functions: vec![FunctionProofReport {
            function: "dynamic_check".into(),
            summary: FunctionSummary {
                total_obligations: 1,
                proved: 0,
                runtime_checked: 1,
                failed: 0,
                unknown: 0,
                total_time_ms: 11,
                max_proof_level: Some(ProofLevel::L0Safety),
                verdict: FunctionVerdict::RuntimeChecked,
            },
            obligations: vec![ObligationReport {
                description: "runtime safety check".to_string(),
                kind: "postcondition".to_string(),
                proof_level: ProofLevel::L0Safety,
                location: Some(SourceSpan {
                    file: "src/runtime.rs".to_string(),
                    line_start: 10,
                    col_start: 1,
                    line_end: 10,
                    col_end: 12,
                }),
                outcome: ObligationOutcome::RuntimeChecked {
                    note: Some("validated by runtime instrumentation".to_string()),
                },
                solver: "runtime".into(),
                time_ms: 11,
                evidence: None,
            }],
        }],
    }
}

// -----------------------------------------------------------------------
// Legacy API tests (backward compat)
// -----------------------------------------------------------------------

#[test]
fn test_build_and_format_report() {
    let results = midpoint_results();
    let report = build_report("midpoint", &results);
    assert_eq!(report.total_proved, 1);
    assert_eq!(report.total_failed, 1);
    assert_eq!(report.total_unknown, 0);
    assert_eq!(report.functions.len(), 1);
    assert_eq!(report.functions[0].function, "get_midpoint");

    let summary = format_summary(&report);
    assert!(summary.contains("PROVED"));
    assert!(summary.contains("FAILED"));
    assert!(summary.contains("counterexample"));

    let json = serde_json::to_string_pretty(&report).expect("serialize");
    assert!(json.contains("get_midpoint"));
}

// -----------------------------------------------------------------------
// JSON report construction tests
// -----------------------------------------------------------------------

#[test]
fn test_json_report_schema_version() {
    let report = build_json_report("test_crate", &[]);
    assert_eq!(report.metadata.schema_version, SCHEMA_VERSION);
    assert_eq!(report.metadata.trust_version, TRUST_VERSION);
}

#[test]
fn test_json_report_empty_crate() {
    let report = build_json_report("empty", &[]);
    assert_eq!(report.crate_name, "empty");
    assert_eq!(report.summary.functions_analyzed, 0);
    assert_eq!(report.summary.total_obligations, 0);
    assert_eq!(report.summary.verdict, CrateVerdict::NoObligations);
    assert!(report.functions.is_empty());
}

#[test]
fn test_json_report_single_function_mixed_results() {
    let results = midpoint_results();
    let report = build_json_report("midpoint", &results);

    assert_eq!(report.crate_name, "midpoint");
    assert_eq!(report.summary.functions_analyzed, 1);
    assert_eq!(report.summary.total_obligations, 2);
    assert_eq!(report.summary.total_proved, 1);
    assert_eq!(report.summary.total_failed, 1);
    assert_eq!(report.summary.total_unknown, 0);
    assert_eq!(report.summary.verdict, CrateVerdict::HasViolations);
    assert_eq!(report.summary.functions_with_violations, 1);

    let func = &report.functions[0];
    assert_eq!(func.function, "get_midpoint");
    assert_eq!(func.summary.verdict, FunctionVerdict::HasViolations);
    assert_eq!(func.obligations.len(), 2);
}

#[test]
fn test_json_report_obligation_detail() {
    let results = midpoint_results();
    let report = build_json_report("midpoint", &results);

    let func = &report.functions[0];

    // Check the failed obligation (overflow)
    let overflow = func
        .obligations
        .iter()
        .find(|o| o.kind == "arithmetic_overflow_add")
        .expect("should have overflow obligation");
    assert_eq!(overflow.description, "arithmetic overflow (Add)");
    assert_eq!(overflow.proof_level, ProofLevel::L0Safety);
    assert_eq!(overflow.solver, "z4");
    assert_eq!(overflow.time_ms, 3);
    assert!(matches!(&overflow.outcome, ObligationOutcome::Failed { counterexample: Some(_) }));

    // Check counterexample variables
    if let ObligationOutcome::Failed { counterexample: Some(cex) } = &overflow.outcome {
        assert_eq!(cex.variables.len(), 2);
        assert_eq!(cex.variables[0].name, "a");
        assert_eq!(cex.variables[0].value, "18446744073709551615");
        assert_eq!(cex.variables[0].value_type, "uint");
        assert_eq!(cex.variables[0].display, "18446744073709551615");
        assert_eq!(cex.variables[1].name, "b");
        assert_eq!(cex.variables[1].value, "1");
        assert_eq!(cex.variables[1].value_type, "uint");
    } else {
        panic!("expected failed with counterexample");
    }

    // Check the proved obligation (divzero)
    let divzero = func
        .obligations
        .iter()
        .find(|o| o.kind == "division_by_zero")
        .expect("should have divzero obligation");
    assert_eq!(divzero.solver, "z4");
    assert_eq!(divzero.time_ms, 1);
    match &divzero.outcome {
        ObligationOutcome::Proved { strength } => {
            assert_eq!(*strength, ProofStrength::smt_unsat());
        }
        other => panic!("expected Proved, got {other:?}"),
    }
}

#[test]
fn test_json_report_obligation_location() {
    let results = midpoint_results();
    let report = build_json_report("midpoint", &results);

    let func = &report.functions[0];
    let overflow = func
        .obligations
        .iter()
        .find(|o| o.kind == "arithmetic_overflow_add")
        .expect("should have overflow obligation");

    let loc = overflow.location.as_ref().expect("should have location");
    assert_eq!(loc.file, "src/midpoint.rs");
    assert_eq!(loc.line_start, 5);
    assert_eq!(loc.col_start, 5);
}

#[test]
fn test_json_report_empty_span_no_location() {
    let results = vec![(
        VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "test_fn".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
        },
        VerificationResult::Proved {
            solver: "z4".into(),
            time_ms: 1,
            strength: ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: None,
        },
    )];
    let report = build_json_report("test", &results);
    assert!(report.functions[0].obligations[0].location.is_none());
}

#[test]
fn test_json_report_multi_function() {
    let results = multi_function_results();
    let report = build_json_report("multi", &results);

    assert_eq!(report.summary.functions_analyzed, 3);
    assert_eq!(report.summary.total_obligations, 5);
    assert_eq!(report.summary.total_proved, 2);
    assert_eq!(report.summary.total_failed, 1);
    assert_eq!(report.summary.total_runtime_checked, 1);
    assert_eq!(report.summary.total_unknown, 1);
    assert_eq!(report.summary.verdict, CrateVerdict::HasViolations);

    // Functions sorted alphabetically
    assert_eq!(report.functions[0].function, "compute");
    assert_eq!(report.functions[1].function, "get_midpoint");
    assert_eq!(report.functions[2].function, "lookup");

    // compute: 1 proved + 1 timeout = inconclusive
    assert_eq!(report.functions[0].summary.verdict, FunctionVerdict::Inconclusive);

    // get_midpoint: 1 proved + 1 failed = violations
    assert_eq!(report.functions[1].summary.verdict, FunctionVerdict::HasViolations);

    // lookup: 1 unknown with a runtime fallback = runtime-checked
    assert_eq!(report.functions[2].summary.verdict, FunctionVerdict::RuntimeChecked);
}

#[test]
fn test_json_report_all_proved_verdict() {
    let results = vec![
        (
            VerificationCondition {
                kind: VcKind::DivisionByZero,
                function: "safe_div".into(),
                location: SourceSpan::default(),
                formula: Formula::Bool(false),
                contract_metadata: None,
            },
            VerificationResult::Proved {
                solver: "z4".into(),
                time_ms: 1,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: None,
                solver_warnings: None,
            },
        ),
        (
            VerificationCondition {
                kind: VcKind::ArithmeticOverflow {
                    op: BinOp::Add,
                    operand_tys: (Ty::u32(), Ty::u32()),
                },
                function: "safe_div".into(),
                location: SourceSpan::default(),
                formula: Formula::Bool(false),
                contract_metadata: None,
            },
            VerificationResult::Proved {
                solver: "z4".into(),
                time_ms: 2,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: None,
                solver_warnings: None,
            },
        ),
    ];
    let report = build_json_report("safe", &results);
    assert_eq!(report.summary.verdict, CrateVerdict::Verified);
    assert_eq!(report.functions[0].summary.verdict, FunctionVerdict::Verified);
}

#[test]
fn test_annotation_report_single_function() {
    let annotation = proof_annotation(
        "checked_add",
        "crate::math::checked_add",
        vec![
            annotation_obligation(
                "overflow check",
                "arithmetic_overflow_add",
                AnnotationStatus::Proved,
                ProofLevel::L0Safety,
                5,
                Some(SourceSpan {
                    file: "src/math.rs".to_string(),
                    line_start: 12,
                    col_start: 9,
                    line_end: 12,
                    col_end: 21,
                }),
            ),
            annotation_obligation(
                "postcondition",
                "postcondition",
                AnnotationStatus::Failed,
                ProofLevel::L1Functional,
                8,
                None,
            ),
        ],
    );

    let report = build_json_report_from_annotations("math", &[annotation]);

    assert_eq!(report.summary.functions_analyzed, 1);
    assert_eq!(report.summary.total_obligations, 2);
    assert_eq!(report.summary.total_proved, 1);
    assert_eq!(report.summary.total_failed, 1);
    assert_eq!(report.summary.verdict, CrateVerdict::HasViolations);

    let function = &report.functions[0];
    assert_eq!(function.function, "crate::math::checked_add");
    assert_eq!(function.summary.verdict, FunctionVerdict::HasViolations);
    assert_eq!(function.summary.total_time_ms, 13);
    assert_eq!(function.obligations.len(), 2);
    match &function.obligations[0].outcome {
        ObligationOutcome::Proved { strength } => {
            assert_eq!(*strength, ProofStrength::smt_unsat());
        }
        other => panic!("expected Proved, got {other:?}"),
    }
    assert!(matches!(
        function.obligations[1].outcome,
        ObligationOutcome::Failed { counterexample: Some(_) }
    ));
    assert_eq!(
        function.obligations[0].location.as_ref().map(|location| location.file.as_str()),
        Some("src/math.rs")
    );
}

#[test]
fn test_annotation_report_empty() {
    let report = build_json_report_from_annotations("empty", &[]);

    assert_eq!(report.summary.verdict, CrateVerdict::NoObligations);
    assert_eq!(report.summary.functions_analyzed, 0);
    assert_eq!(report.summary.total_obligations, 0);
    assert!(report.functions.is_empty());
}

#[test]
fn test_annotation_report_roundtrip() {
    let report = build_json_report_from_annotations(
        "roundtrip",
        &[proof_annotation(
            "checked_mul",
            "crate::math::checked_mul",
            vec![
                annotation_obligation(
                    "overflow check",
                    "arithmetic_overflow_mul",
                    AnnotationStatus::Proved,
                    ProofLevel::L0Safety,
                    3,
                    Some(SourceSpan {
                        file: "src/math.rs".to_string(),
                        line_start: 20,
                        col_start: 5,
                        line_end: 20,
                        col_end: 17,
                    }),
                ),
                annotation_obligation(
                    "contract",
                    "postcondition",
                    AnnotationStatus::Timeout,
                    ProofLevel::L1Functional,
                    25,
                    None,
                ),
            ],
        )],
    );

    let json = serde_json::to_string(&report).expect("serialize annotation report");
    let roundtrip: JsonProofReport =
        serde_json::from_str(&json).expect("deserialize annotation report");

    assert_eq!(roundtrip.crate_name, "roundtrip");
    assert_eq!(roundtrip.summary.total_obligations, 2);
    assert_eq!(roundtrip.functions.len(), 1);
    assert_eq!(roundtrip.functions[0].function, "crate::math::checked_mul");
    assert!(matches!(
        roundtrip.functions[0].obligations[1].outcome,
        ObligationOutcome::Timeout { timeout_ms: 25 }
    ));
}

#[test]
fn test_annotation_report_verdict_maps_correctly() {
    let verified_report = build_json_report_from_annotations(
        "verified",
        &[proof_annotation(
            "safe_div",
            "crate::math::safe_div",
            vec![
                annotation_obligation(
                    "div by zero",
                    "division_by_zero",
                    AnnotationStatus::Proved,
                    ProofLevel::L0Safety,
                    2,
                    None,
                ),
                annotation_obligation(
                    "postcondition",
                    "postcondition",
                    AnnotationStatus::Proved,
                    ProofLevel::L1Functional,
                    4,
                    None,
                ),
            ],
        )],
    );
    assert_eq!(verified_report.summary.verdict, CrateVerdict::Verified);
    assert_eq!(verified_report.functions[0].summary.verdict, FunctionVerdict::Verified);

    let failing_report = build_json_report_from_annotations(
        "failing",
        &[proof_annotation(
            "unsafe_div",
            "crate::math::unsafe_div",
            vec![
                annotation_obligation(
                    "div by zero",
                    "division_by_zero",
                    AnnotationStatus::Proved,
                    ProofLevel::L0Safety,
                    1,
                    None,
                ),
                annotation_obligation(
                    "postcondition",
                    "postcondition",
                    AnnotationStatus::Failed,
                    ProofLevel::L1Functional,
                    6,
                    None,
                ),
            ],
        )],
    );
    assert_eq!(failing_report.summary.verdict, CrateVerdict::HasViolations);
    assert_eq!(failing_report.functions[0].summary.verdict, FunctionVerdict::HasViolations);
}

#[test]
fn test_build_json_report_auto_policy_reclassifies_unknown_to_runtime_checked() {
    let results = vec![(
        VerificationCondition {
            kind: VcKind::IndexOutOfBounds,
            function: "lookup".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        },
        VerificationResult::Unknown {
            solver: "z4".into(),
            time_ms: 50,
            reason: "nonlinear arithmetic".to_string(),
        },
    )];

    let report =
        build_json_report_with_policy("runtime_auto", &results, RuntimeCheckPolicy::Auto, true);
    let obligation = &report.functions[0].obligations[0];

    assert!(matches!(
        &obligation.outcome,
        ObligationOutcome::RuntimeChecked { note: Some(note) }
            if note == "index out of bounds"
    ));
    assert_eq!(report.summary.total_runtime_checked, 1);
    assert_eq!(report.summary.total_unknown, 0);
    assert_eq!(report.functions[0].summary.verdict, FunctionVerdict::RuntimeChecked);
}

#[test]
fn test_build_json_report_force_static_produces_compile_error_verdict() {
    let results = vec![(
        VerificationCondition {
            kind: VcKind::ArithmeticOverflow {
                op: BinOp::Add,
                operand_tys: (Ty::u32(), Ty::u32()),
            },
            function: "checked_add".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        },
        VerificationResult::Unknown {
            solver: "z4".into(),
            time_ms: 12,
            reason: "solver returned unknown".to_string(),
        },
    )];

    let report = build_json_report_with_policy(
        "force_static",
        &results,
        RuntimeCheckPolicy::ForceStatic,
        true,
    );
    let obligation = &report.functions[0].obligations[0];

    assert!(matches!(
        &obligation.outcome,
        ObligationOutcome::Unknown { reason }
            if reason.contains("`#[trust(static)]` requires a static proof")
                && reason.contains("solver returned unknown")
    ));
    assert_eq!(report.summary.total_runtime_checked, 0);
    assert_eq!(report.summary.total_unknown, 1);
    assert_eq!(report.functions[0].summary.verdict, FunctionVerdict::Inconclusive);
}

// -----------------------------------------------------------------------
// JSON serialization tests
// -----------------------------------------------------------------------

#[test]
fn test_json_serialization_roundtrip() {
    let results = multi_function_results();
    let report = build_json_report("roundtrip", &results);

    let json = serde_json::to_string_pretty(&report).expect("serialize");
    let deserialized: JsonProofReport = serde_json::from_str(&json).expect("deserialize");

    assert_eq!(deserialized.crate_name, "roundtrip");
    assert_eq!(deserialized.metadata.schema_version, report.metadata.schema_version);
    assert_eq!(deserialized.summary.total_obligations, 5);
    assert_eq!(deserialized.functions.len(), 3);
}

#[test]
fn test_json_output_has_required_fields() {
    let results = midpoint_results();
    let report = build_json_report("fields_test", &results);
    let json_value: serde_json::Value = serde_json::to_value(&report).expect("to_value");

    // Top-level required fields
    assert!(json_value.get("metadata").is_some());
    assert!(json_value.get("crate_name").is_some());
    assert!(json_value.get("summary").is_some());
    assert!(json_value.get("functions").is_some());

    // Metadata fields
    let meta = &json_value["metadata"];
    assert!(meta.get("schema_version").is_some());
    assert!(meta.get("trust_version").is_some());
    assert!(meta.get("timestamp").is_some());
    assert!(meta.get("total_time_ms").is_some());

    // Summary fields
    let summary = &json_value["summary"];
    assert!(summary.get("functions_analyzed").is_some());
    assert!(summary.get("functions_verified").is_some());
    assert!(summary.get("functions_runtime_checked").is_some());
    assert!(summary.get("functions_with_violations").is_some());
    assert!(summary.get("functions_inconclusive").is_some());
    assert!(summary.get("total_obligations").is_some());
    assert!(summary.get("total_proved").is_some());
    assert!(summary.get("total_runtime_checked").is_some());
    assert!(summary.get("total_failed").is_some());
    assert!(summary.get("total_unknown").is_some());
    assert!(summary.get("verdict").is_some());

    // Function fields
    let func = &json_value["functions"][0];
    assert!(func.get("function").is_some());
    assert!(func.get("summary").is_some());
    assert!(func.get("obligations").is_some());

    // Obligation fields
    let ob = &func["obligations"][0];
    assert!(ob.get("description").is_some());
    assert!(ob.get("kind").is_some());
    assert!(ob.get("proof_level").is_some());
    assert!(ob.get("outcome").is_some());
    assert!(ob.get("solver").is_some());
    assert!(ob.get("time_ms").is_some());
}

#[test]
fn test_json_outcome_tagged_union() {
    // Verify that the outcome uses internally-tagged serde representation
    let results = midpoint_results();
    let report = build_json_report("tags", &results);
    let json_value: serde_json::Value = serde_json::to_value(&report).expect("to_value");

    // Find the failed obligation
    let func = &json_value["functions"][0];
    for ob in func["obligations"].as_array().unwrap() {
        let outcome = &ob["outcome"];
        let status = outcome["status"].as_str().unwrap();
        match status {
            "proved" => {
                assert!(outcome.get("strength").is_some());
            }
            "failed" => {
                // counterexample may or may not be present
            }
            "unknown" => {
                assert!(outcome.get("reason").is_some());
            }
            "timeout" => {
                assert!(outcome.get("timeout_ms").is_some());
            }
            "runtime_checked" => {
                assert!(outcome.get("note").is_some() || outcome.get("note").is_none());
            }
            other => panic!("unexpected status: {other}"),
        }
    }
}

#[test]
fn test_json_report_runtime_checked_status() {
    let report = runtime_checked_report();

    assert_eq!(report.summary.verdict, CrateVerdict::RuntimeChecked);
    assert_eq!(report.summary.total_runtime_checked, 1);
    assert_eq!(report.summary.functions_runtime_checked, 1);
    assert_eq!(report.functions[0].summary.verdict, FunctionVerdict::RuntimeChecked);
    assert_eq!(report.functions[0].summary.runtime_checked, 1);

    let json = serde_json::to_string_pretty(&report).expect("serialize runtime-checked");
    let parsed: JsonProofReport = serde_json::from_str(&json).expect("deserialize runtime-checked");
    assert_eq!(parsed.summary.total_runtime_checked, 1);
    assert_eq!(parsed.functions[0].summary.runtime_checked, 1);

    let value: serde_json::Value = serde_json::from_str(&json).expect("parse runtime-checked");
    let ob = &value["functions"][0]["obligations"][0];
    assert_eq!(ob["outcome"]["status"], "runtime_checked");
    assert_eq!(ob["outcome"]["note"].as_str(), Some("validated by runtime instrumentation"));

    let text = format_json_summary(&report);
    assert!(text.contains("runtime-checked"));
    assert!(text.contains("RUNTIME CHECKED"));
    assert!(text.contains("validated by runtime instrumentation"));
}

#[test]
fn test_json_counterexample_structure() {
    let results = midpoint_results();
    let report = build_json_report("cex", &results);
    let json_value: serde_json::Value = serde_json::to_value(&report).expect("to_value");

    let func = &json_value["functions"][0];
    let failed_ob = func["obligations"]
        .as_array()
        .unwrap()
        .iter()
        .find(|ob| ob["outcome"]["status"].as_str() == Some("failed"))
        .expect("should have a failed obligation");

    let cex = &failed_ob["outcome"]["counterexample"];
    assert!(cex.is_object());

    let vars = cex["variables"].as_array().unwrap();
    assert_eq!(vars.len(), 2);

    assert_eq!(vars[0]["name"].as_str().unwrap(), "a");
    assert!(vars[0].get("value").is_some());
    assert!(vars[0].get("value_type").is_some());
    assert_eq!(vars[0]["value_type"].as_str().unwrap(), "uint");
    assert!(vars[0].get("display").is_some());
}

#[test]
fn test_json_kind_tags_are_snake_case() {
    // Kind tags must be machine-parseable snake_case strings
    assert_eq!(vc_kind_tag(&VcKind::DivisionByZero), "division_by_zero");
    assert_eq!(vc_kind_tag(&VcKind::RemainderByZero), "remainder_by_zero");
    assert_eq!(vc_kind_tag(&VcKind::IndexOutOfBounds), "index_out_of_bounds");
    assert_eq!(vc_kind_tag(&VcKind::Postcondition), "postcondition");
    assert_eq!(vc_kind_tag(&VcKind::Unreachable), "unreachable");
    assert_eq!(
        vc_kind_tag(&VcKind::ArithmeticOverflow {
            op: BinOp::Add,
            operand_tys: (Ty::u32(), Ty::u32())
        }),
        "arithmetic_overflow_add"
    );
    assert_eq!(
        vc_kind_tag(&VcKind::ShiftOverflow {
            op: BinOp::Shl,
            operand_ty: Ty::u32(),
            shift_ty: Ty::u32()
        }),
        "shift_overflow_shl"
    );
}

// -----------------------------------------------------------------------
// NDJSON streaming tests
// -----------------------------------------------------------------------

#[test]
fn test_ndjson_output_format() {
    let results = midpoint_results();
    let report = build_json_report("ndjson_test", &results);

    let mut buf = Vec::new();
    write_ndjson(&report, &mut buf).expect("write ndjson");
    let output = String::from_utf8(buf).expect("utf8");

    let lines: Vec<&str> = output.trim_end().split('\n').collect();
    // header + 1 function + footer = 3 lines
    assert_eq!(lines.len(), 3, "expected 3 NDJSON lines, got {}", lines.len());

    // Each line must be valid JSON
    for (i, line) in lines.iter().enumerate() {
        let parsed: serde_json::Value =
            serde_json::from_str(line).unwrap_or_else(|e| panic!("line {i} not valid JSON: {e}"));
        assert!(parsed.get("record_type").is_some(), "line {i} missing record_type");
    }

    // Header
    let header: NdjsonHeader = serde_json::from_str(lines[0]).expect("parse header");
    assert_eq!(header.record_type, "header");
    assert_eq!(header.crate_name, "ndjson_test");

    // Function record
    let func: NdjsonFunctionRecord = serde_json::from_str(lines[1]).expect("parse function");
    assert_eq!(func.record_type, "function");
    assert_eq!(func.function.function, "get_midpoint");

    // Footer
    let footer: NdjsonFooter = serde_json::from_str(lines[2]).expect("parse footer");
    assert_eq!(footer.record_type, "footer");
    assert_eq!(footer.summary.total_proved, 1);
    assert_eq!(footer.summary.total_failed, 1);
}

#[test]
fn test_ndjson_multi_function() {
    let results = multi_function_results();
    let report = build_json_report("multi_ndjson", &results);

    let mut buf = Vec::new();
    write_ndjson(&report, &mut buf).expect("write ndjson");
    let output = String::from_utf8(buf).expect("utf8");

    let lines: Vec<&str> = output.trim_end().split('\n').collect();
    // header + 3 functions + footer = 5 lines
    assert_eq!(lines.len(), 5, "expected 5 NDJSON lines, got {}", lines.len());

    // Verify all function records
    let func_lines = &lines[1..4];
    for line in func_lines {
        let record: NdjsonFunctionRecord =
            serde_json::from_str(line).expect("parse function record");
        assert_eq!(record.record_type, "function");
        assert_eq!(record.crate_name, "multi_ndjson");
    }
}

#[test]
fn test_ndjson_empty_crate() {
    let report = build_json_report("empty", &[]);

    let mut buf = Vec::new();
    write_ndjson(&report, &mut buf).expect("write ndjson");
    let output = String::from_utf8(buf).expect("utf8");

    let lines: Vec<&str> = output.trim_end().split('\n').collect();
    // header + footer = 2 lines
    assert_eq!(lines.len(), 2);
}

// -----------------------------------------------------------------------
// Text formatting (derived from JSON) tests
// -----------------------------------------------------------------------

#[test]
fn test_json_summary_text_format() {
    let results = midpoint_results();
    let report = build_json_report("midpoint", &results);
    let text = format_json_summary(&report);

    assert!(text.contains("get_midpoint"));
    assert!(text.contains("[VIOLATIONS]"));
    assert!(text.contains("PROVED"));
    assert!(text.contains("SMT UNSAT"));
    assert!(text.contains("FAILED"));
    assert!(text.contains("counterexample"));
    assert!(text.contains("a = 18446744073709551615"));
    assert!(text.contains("max level: L0 safety"));
    assert!(text.contains("Verdict: HAS VIOLATIONS"));
}

#[test]
fn test_json_summary_all_proved() {
    let results = vec![(
        VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "safe_fn".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
        },
        VerificationResult::Proved {
            solver: "z4".into(),
            time_ms: 1,
            strength: ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: None,
        },
    )];
    let report = build_json_report("safe", &results);
    let text = format_json_summary(&report);

    assert!(text.contains("[VERIFIED]"));
    assert!(text.contains("SMT UNSAT"));
    assert!(text.contains("Verdict: VERIFIED"));
}

#[test]
fn test_json_summary_timeout() {
    let results = vec![(
        VerificationCondition {
            kind: VcKind::Postcondition,
            function: "slow_fn".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        },
        VerificationResult::Timeout { solver: "z4".into(), timeout_ms: 10000 },
    )];
    let report = build_json_report("slow", &results);
    let text = format_json_summary(&report);

    assert!(text.contains("TIMEOUT"));
    assert!(text.contains("10000ms"));
    assert!(text.contains("Verdict: INCONCLUSIVE"));
}

// -----------------------------------------------------------------------
// File I/O tests
// -----------------------------------------------------------------------

#[test]
fn test_write_json_report_file() {
    let results = midpoint_results();
    let report = build_json_report("file_test", &results);

    let dir = std::env::temp_dir().join("trust_report_test_json");
    let _ = std::fs::remove_dir_all(&dir);

    write_json_report(&report, &dir).expect("write json");

    let content = std::fs::read_to_string(dir.join("report.json")).expect("read json");
    let parsed: JsonProofReport = serde_json::from_str(&content).expect("parse json");
    assert_eq!(parsed.crate_name, "file_test");
    assert_eq!(parsed.functions.len(), 1);

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn test_write_ndjson_report_file() {
    let results = multi_function_results();
    let report = build_json_report("ndjson_file", &results);

    let dir = std::env::temp_dir().join("trust_report_test_ndjson");
    let _ = std::fs::remove_dir_all(&dir);

    write_ndjson_report(&report, &dir).expect("write ndjson");

    let content = std::fs::read_to_string(dir.join("report.ndjson")).expect("read ndjson");
    let lines: Vec<&str> = content.trim_end().split('\n').collect();
    assert_eq!(lines.len(), 5); // header + 3 functions + footer

    // Each line parseable
    for line in &lines {
        let _: serde_json::Value = serde_json::from_str(line).expect("valid json");
    }

    let _ = std::fs::remove_dir_all(&dir);
}

// -----------------------------------------------------------------------
// Proof level and kind coverage
// -----------------------------------------------------------------------

#[test]
fn test_obligation_proof_levels() {
    let results = vec![
        (
            VerificationCondition {
                kind: VcKind::DivisionByZero,
                function: "f".into(),
                location: SourceSpan::default(),
                formula: Formula::Bool(false),
                contract_metadata: None,
            },
            VerificationResult::Proved {
                solver: "z4".into(),
                time_ms: 1,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: None,
                solver_warnings: None,
            },
        ),
        (
            VerificationCondition {
                kind: VcKind::Postcondition,
                function: "f".into(),
                location: SourceSpan::default(),
                formula: Formula::Bool(false),
                contract_metadata: None,
            },
            VerificationResult::Proved {
                solver: "sunder".into(),
                time_ms: 10,
                strength: ProofStrength::deductive(),
                proof_certificate: None,
                solver_warnings: None,
            },
        ),
        (
            VerificationCondition {
                kind: VcKind::Deadlock,
                function: "f".into(),
                location: SourceSpan::default(),
                formula: Formula::Bool(false),
                contract_metadata: None,
            },
            VerificationResult::Proved {
                solver: "tla2".into(),
                time_ms: 100,
                strength: ProofStrength::inductive(),
                proof_certificate: None,
                solver_warnings: None,
            },
        ),
    ];

    let report = build_json_report("levels", &results);
    let func = &report.functions[0];

    // Max proof level should be L2Domain (deadlock)
    assert_eq!(func.summary.max_proof_level, Some(ProofLevel::L2Domain));

    // Check individual proof levels
    let levels: Vec<ProofLevel> = func.obligations.iter().map(|o| o.proof_level).collect();
    assert!(levels.contains(&ProofLevel::L0Safety));
    assert!(levels.contains(&ProofLevel::L1Functional));
    assert!(levels.contains(&ProofLevel::L2Domain));
}

#[test]
fn test_all_proof_strengths_serialize() {
    let strengths = vec![
        ProofStrength::smt_unsat(),
        ProofStrength::bounded(100),
        ProofStrength::inductive(),
        ProofStrength::deductive(),
        ProofStrength::constructive(),
    ];

    for strength in &strengths {
        let json = serde_json::to_string(strength).expect("serialize strength");
        let roundtrip: ProofStrength = serde_json::from_str(&json).expect("deserialize strength");
        assert_eq!(&roundtrip, strength);
    }
}

#[test]
fn test_function_summary_timing() {
    let results = multi_function_results();
    let report = build_json_report("timing", &results);

    // get_midpoint: 3ms + 1ms = 4ms
    let midpoint = report.functions.iter().find(|f| f.function == "get_midpoint").unwrap();
    assert_eq!(midpoint.summary.total_time_ms, 4);

    // compute: 5000ms + 2ms = 5002ms
    let compute = report.functions.iter().find(|f| f.function == "compute").unwrap();
    assert_eq!(compute.summary.total_time_ms, 5002);
}

// -----------------------------------------------------------------------
// Whole-crate verification report tests (#59)
// -----------------------------------------------------------------------

fn crate_verification_result_fixture() -> CrateVerificationResult {
    let results = multi_function_results();

    // Split results by function to build per-function entries.
    let mut func_map: BTreeMap<String, Vec<(VerificationCondition, VerificationResult)>> =
        BTreeMap::new();
    for (vc, result) in results {
        func_map.entry(vc.function.as_str().to_string()).or_default().push((vc, result));
    }

    let mut crate_result = CrateVerificationResult::new("multi_crate");
    for (func_name, func_results) in func_map {
        crate_result.add_function(FunctionVerificationResult {
            function_path: format!("crate::{func_name}"),
            function_name: func_name,
            results: func_results,
            from_notes: 0,
            with_assumptions: 0,
        });
    }
    crate_result
}

#[test]
fn test_build_crate_verification_report_produces_valid_report() {
    let crate_result = crate_verification_result_fixture();
    let report = build_crate_verification_report(&crate_result);

    assert_eq!(report.crate_name, "multi_crate");
    assert_eq!(report.summary.functions_analyzed, 3);
    assert_eq!(report.summary.total_obligations, 5);
    assert_eq!(report.summary.total_proved, 2);
    assert_eq!(report.summary.total_failed, 1);
    assert_eq!(report.summary.verdict, CrateVerdict::HasViolations);
}

#[test]
fn test_build_crate_verification_report_empty() {
    let crate_result = CrateVerificationResult::new("empty_crate");
    let report = build_crate_verification_report(&crate_result);

    assert_eq!(report.crate_name, "empty_crate");
    assert_eq!(report.summary.functions_analyzed, 0);
    assert_eq!(report.summary.verdict, CrateVerdict::NoObligations);
    assert!(report.functions.is_empty());
}

#[test]
fn test_build_crate_verification_report_with_policy() {
    let crate_result = crate_verification_result_fixture();
    let report = build_crate_verification_report_with_policy(
        &crate_result,
        RuntimeCheckPolicy::ForceStatic,
        true,
    );

    assert_eq!(report.crate_name, "multi_crate");
    // ForceStatic should not reclassify unknowns to runtime-checked
    assert_eq!(report.summary.total_runtime_checked, 0);
}

#[test]
fn test_format_crate_verification_summary_no_specs() {
    let crate_result = crate_verification_result_fixture();
    let report = build_crate_verification_report(&crate_result);
    let text = format_crate_verification_summary(&report, &crate_result);

    // Without spec composition, no composition lines should appear.
    assert!(!text.contains("Cross-function composition:"));
    assert!(text.contains("Verdict:"));
}

#[test]
fn test_format_crate_verification_summary_with_specs() {
    let mut crate_result = CrateVerificationResult::new("spec_crate");
    crate_result.add_function(FunctionVerificationResult {
        function_path: "crate::f".to_string(),
        function_name: "f".to_string(),
        results: vec![(
            VerificationCondition {
                kind: VcKind::DivisionByZero,
                function: "f".into(),
                location: SourceSpan::default(),
                formula: Formula::Bool(false),
                contract_metadata: None,
            },
            VerificationResult::Proved {
                solver: "z4".into(),
                time_ms: 1,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: None,
                solver_warnings: None,
            },
        )],
        from_notes: 3,
        with_assumptions: 2,
    });

    let report = build_crate_verification_report(&crate_result);
    let text = format_crate_verification_summary(&report, &crate_result);

    assert!(text.contains("Cross-function composition:"));
    assert!(text.contains("3 VCs satisfied from proved callee specs (free)"));
    assert!(text.contains("2 VCs sent to solver with callee assumptions"));
}

#[test]
fn test_crate_verification_report_serialization_roundtrip() {
    let crate_result = crate_verification_result_fixture();
    let report = build_crate_verification_report(&crate_result);

    let json = serde_json::to_string_pretty(&report).expect("serialize");
    let deserialized: JsonProofReport = serde_json::from_str(&json).expect("deserialize");

    assert_eq!(deserialized.crate_name, "multi_crate");
    assert_eq!(deserialized.summary.functions_analyzed, 3);
    assert_eq!(deserialized.summary.total_obligations, 5);
}

// -----------------------------------------------------------------------
// #382: ProofEvidence downstream usage tests
// -----------------------------------------------------------------------

#[test]
fn test_proof_evidence_label_smt() {
    let strength = ProofStrength::smt_unsat();
    let label = proof_evidence_label(&strength);
    assert!(label.contains("SMT UNSAT"), "expected SMT UNSAT in {label}");
    assert!(label.contains("smt-backed"), "expected smt-backed in {label}");
}

#[test]
fn test_proof_evidence_label_bounded() {
    let strength = ProofStrength::bounded(100);
    let label = proof_evidence_label(&strength);
    assert!(label.contains("BOUNDED"), "expected BOUNDED in {label}");
    assert!(label.contains("trusted"), "expected trusted assurance in {label}");
}

#[test]
fn test_proof_evidence_label_constructive() {
    let strength = ProofStrength::constructive();
    let label = proof_evidence_label(&strength);
    assert!(label.contains("CONSTRUCTIVE"), "expected CONSTRUCTIVE in {label}");
}

#[test]
fn test_proof_evidence_from_proof_strength_roundtrip() {
    // Verify the From<ProofStrength> for ProofEvidence conversion is used
    let strength = ProofStrength::deductive();
    let evidence: ProofEvidence = strength.into();
    assert_eq!(evidence.reasoning, ReasoningKind::Deductive);
    // Deductive has Sound assurance -> maps to SmtBacked
    assert_eq!(evidence.assurance, AssuranceLevel::SmtBacked);
}
