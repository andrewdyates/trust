// trust-types integration tests: serde roundtrip and model construction
//
// Exercises the public API of trust-types across all major type families:
// Formula, VerificationCondition, Ty, StateMachine, LivenessProperty,
// CrateVerificationResult, and ProofReport types.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::*;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn midpoint_function() -> VerifiableFunction {
    VerifiableFunction {
        name: "get_midpoint".to_string(),
        def_path: "midpoint::get_midpoint".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::usize(), name: None },
                LocalDecl { index: 1, ty: Ty::usize(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::usize(), Ty::Bool]), name: None },
                LocalDecl { index: 4, ty: Ty::usize(), name: None },
                LocalDecl { index: 5, ty: Ty::usize(), name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::CheckedBinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::field(3, 1)),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Add),
                        target: BlockId(1),
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::Use(Operand::Copy(Place::field(3, 0))),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(5),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Div,
                                Operand::Copy(Place::local(4)),
                                Operand::Constant(ConstValue::Uint(2, 64)),
                            ),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(5))),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 2,
            return_ty: Ty::usize(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

// ---------------------------------------------------------------------------
// VerifiableFunction roundtrip
// ---------------------------------------------------------------------------

#[test]
fn test_verifiable_function_serde_roundtrip() {
    let func = midpoint_function();
    let json = serde_json::to_string(&func).expect("serialize");
    let round: VerifiableFunction = serde_json::from_str(&json).expect("deserialize");
    assert_eq!(round.name, func.name);
    assert_eq!(round.def_path, func.def_path);
    assert_eq!(round.body.locals.len(), func.body.locals.len());
    assert_eq!(round.body.blocks.len(), func.body.blocks.len());
    assert_eq!(round.body.arg_count, func.body.arg_count);
}

#[test]
fn test_verifiable_function_with_contracts_roundtrip() {
    let mut func = midpoint_function();
    func.contracts = vec![
        Contract {
            kind: ContractKind::Requires,
            span: SourceSpan::default(),
            body: "a <= b".to_string(),
        },
        Contract {
            kind: ContractKind::Ensures,
            span: SourceSpan::default(),
            body: "result >= a && result <= b".to_string(),
        },
    ];
    func.preconditions = vec![Formula::Le(
        Box::new(Formula::Var("a".into(), Sort::BitVec(64))),
        Box::new(Formula::Var("b".into(), Sort::BitVec(64))),
    )];
    func.postconditions = vec![Formula::And(vec![
        Formula::Ge(
            Box::new(Formula::Var("result".into(), Sort::BitVec(64))),
            Box::new(Formula::Var("a".into(), Sort::BitVec(64))),
        ),
        Formula::Le(
            Box::new(Formula::Var("result".into(), Sort::BitVec(64))),
            Box::new(Formula::Var("b".into(), Sort::BitVec(64))),
        ),
    ])];

    let json = serde_json::to_string(&func).expect("serialize");
    let round: VerifiableFunction = serde_json::from_str(&json).expect("deserialize");
    assert_eq!(round.contracts.len(), 2);
    assert_eq!(round.preconditions.len(), 1);
    assert_eq!(round.postconditions.len(), 1);
    assert!(matches!(round.contracts[0].kind, ContractKind::Requires));
    assert!(matches!(round.contracts[1].kind, ContractKind::Ensures));
}

// ---------------------------------------------------------------------------
// Formula roundtrip — covers all major variants
// ---------------------------------------------------------------------------

#[test]
fn test_formula_literals_roundtrip() {
    let formulas = vec![
        Formula::Bool(true),
        Formula::Bool(false),
        Formula::Int(42),
        Formula::Int(-1),
        Formula::BitVec { value: 255, width: 8 },
    ];
    for formula in &formulas {
        let json = serde_json::to_string(formula).expect("serialize");
        let round: Formula = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(&round, formula);
    }
}

#[test]
fn test_formula_connectives_roundtrip() {
    let formula = Formula::Implies(
        Box::new(Formula::And(vec![
            Formula::Var("p".into(), Sort::Bool),
            Formula::Var("q".into(), Sort::Bool),
        ])),
        Box::new(Formula::Or(vec![
            Formula::Not(Box::new(Formula::Var("r".into(), Sort::Bool))),
            Formula::Var("s".into(), Sort::Bool),
        ])),
    );
    let json = serde_json::to_string(&formula).expect("serialize");
    let round: Formula = serde_json::from_str(&json).expect("deserialize");
    assert_eq!(round, formula);
}

#[test]
fn test_formula_bitvector_ops_roundtrip() {
    let a = Box::new(Formula::Var("x".into(), Sort::BitVec(32)));
    let b = Box::new(Formula::Var("y".into(), Sort::BitVec(32)));
    let formula = Formula::And(vec![
        Formula::BvAdd(a.clone(), b.clone(), 32),
        Formula::BvSub(a.clone(), b.clone(), 32),
        Formula::BvMul(a.clone(), b.clone(), 32),
        Formula::BvUDiv(a.clone(), b.clone(), 32),
        Formula::BvAnd(a.clone(), b.clone(), 32),
        Formula::BvOr(a.clone(), b.clone(), 32),
        Formula::BvXor(a.clone(), b.clone(), 32),
        Formula::BvShl(a.clone(), b.clone(), 32),
        Formula::BvULt(a.clone(), b.clone(), 32),
        Formula::BvSLe(a.clone(), b.clone(), 32),
    ]);
    let json = serde_json::to_string(&formula).expect("serialize");
    let round: Formula = serde_json::from_str(&json).expect("deserialize");
    assert_eq!(round, formula);
}

#[test]
fn test_formula_quantifiers_roundtrip() {
    let formula = Formula::Forall(
        vec![("i".into(), Sort::Int), ("j".into(), Sort::BitVec(64))],
        Box::new(Formula::Implies(
            Box::new(Formula::Lt(
                Box::new(Formula::Var("i".into(), Sort::Int)),
                Box::new(Formula::Var("j".into(), Sort::BitVec(64))),
            )),
            Box::new(Formula::Exists(
                vec![("k".into(), Sort::Int)],
                Box::new(Formula::And(vec![
                    Formula::Lt(
                        Box::new(Formula::Var("i".into(), Sort::Int)),
                        Box::new(Formula::Var("k".into(), Sort::Int)),
                    ),
                    Formula::Lt(
                        Box::new(Formula::Var("k".into(), Sort::Int)),
                        Box::new(Formula::Var("j".into(), Sort::BitVec(64))),
                    ),
                ])),
            )),
        )),
    );
    let json = serde_json::to_string(&formula).expect("serialize");
    let round: Formula = serde_json::from_str(&json).expect("deserialize");
    assert_eq!(round, formula);
}

#[test]
fn test_formula_array_ops_roundtrip() {
    let arr = Formula::Var("arr".into(), Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int)));
    let idx = Formula::Int(5);
    let val = Formula::Int(42);
    let formula = Formula::Eq(
        Box::new(Formula::Select(Box::new(arr.clone()), Box::new(idx.clone()))),
        Box::new(Formula::Select(
            Box::new(Formula::Store(Box::new(arr), Box::new(idx), Box::new(val))),
            Box::new(Formula::Int(5)),
        )),
    );
    let json = serde_json::to_string(&formula).expect("serialize");
    let round: Formula = serde_json::from_str(&json).expect("deserialize");
    assert_eq!(round, formula);
}

// ---------------------------------------------------------------------------
// Ty roundtrip — all variants
// ---------------------------------------------------------------------------

#[test]
fn test_ty_all_variants_roundtrip() {
    let types = vec![
        Ty::Bool,
        Ty::Int { width: 8, signed: true },
        Ty::Int { width: 64, signed: true },
        Ty::Int { width: 32, signed: false },
        Ty::Float { width: 64 },
        Ty::Unit,
        Ty::Never,
        Ty::Ref { mutable: false, inner: Box::new(Ty::Bool) },
        Ty::Ref { mutable: true, inner: Box::new(Ty::i32()) },
        Ty::Slice { elem: Box::new(Ty::u32()) },
        Ty::Array { elem: Box::new(Ty::Bool), len: 10 },
        Ty::Tuple(vec![Ty::i32(), Ty::Bool, Ty::usize()]),
        Ty::Adt {
            name: "MyStruct".into(),
            fields: vec![("x".into(), Ty::i32()), ("y".into(), Ty::Bool)],
        },
    ];
    for ty in &types {
        let json = serde_json::to_string(ty).expect("serialize");
        let round: Ty = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(&round, ty);
    }
}

#[test]
fn test_ty_helpers_comprehensive() {
    // Integer checks
    assert!(Ty::i32().is_integer());
    assert!(Ty::i32().is_signed());
    assert_eq!(Ty::i32().int_width(), Some(32));

    assert!(Ty::u32().is_integer());
    assert!(!Ty::u32().is_signed());
    assert_eq!(Ty::u32().int_width(), Some(32));

    assert!(Ty::usize().is_integer());
    assert!(!Ty::usize().is_signed());
    assert_eq!(Ty::usize().int_width(), Some(64));

    assert!(Ty::isize().is_integer());
    assert!(Ty::isize().is_signed());
    assert_eq!(Ty::isize().int_width(), Some(64));

    // Non-integer checks
    assert!(!Ty::Bool.is_integer());
    assert!(!Ty::Bool.is_signed());
    assert_eq!(Ty::Bool.int_width(), None);
    assert!(!Ty::Unit.is_integer());
    assert!(!(Ty::Float { width: 64 }).is_integer());
}

// ---------------------------------------------------------------------------
// Sort::from_ty
// ---------------------------------------------------------------------------

#[test]
fn test_sort_from_ty_comprehensive() {
    assert_eq!(Sort::from_ty(&Ty::Bool), Sort::Bool);
    assert_eq!(Sort::from_ty(&Ty::i32()), Sort::BitVec(32));
    assert_eq!(Sort::from_ty(&Ty::u32()), Sort::BitVec(32));
    assert_eq!(Sort::from_ty(&Ty::usize()), Sort::BitVec(64));
    assert_eq!(Sort::from_ty(&Ty::isize()), Sort::BitVec(64));
    assert_eq!(Sort::from_ty(&Ty::Float { width: 64 }), Sort::BitVec(64));
    // Fallback for non-primitive types
    assert_eq!(Sort::from_ty(&Ty::Unit), Sort::Int);
    assert_eq!(Sort::from_ty(&Ty::Tuple(vec![])), Sort::Int);
}

// ---------------------------------------------------------------------------
// VerificationCondition + VcKind roundtrip
// ---------------------------------------------------------------------------

#[test]
fn test_verification_condition_all_kinds_roundtrip() {
    let vc_kinds: Vec<VcKind> = vec![
        VcKind::ArithmeticOverflow { op: BinOp::Add, operand_tys: (Ty::i32(), Ty::i32()) },
        VcKind::ShiftOverflow { op: BinOp::Shl, operand_ty: Ty::u32(), shift_ty: Ty::u32() },
        VcKind::DivisionByZero,
        VcKind::RemainderByZero,
        VcKind::IndexOutOfBounds,
        VcKind::SliceBoundsCheck,
        VcKind::Assertion { message: "x > 0".into() },
        VcKind::Precondition { callee: "foo::bar".into() },
        VcKind::Postcondition,
        VcKind::CastOverflow { from_ty: Ty::i32(), to_ty: Ty::u32() },
        VcKind::NegationOverflow { ty: Ty::i32() },
        VcKind::Unreachable,
        VcKind::DeadState { state: "idle".into() },
        VcKind::Deadlock,
        VcKind::Temporal { property: "eventually done".into() },
        VcKind::NonTermination { context: "loop".into(), measure: "n".into() },
    ];

    for kind in vc_kinds {
        let vc = VerificationCondition {
            kind: kind.clone(),
            function: "test_fn".into(),
            location: SourceSpan {
                file: "test.rs".into(),
                line_start: 10,
                col_start: 4,
                line_end: 10,
                col_end: 20,
            },
            formula: Formula::Bool(false),
            contract_metadata: None,
        };
        let json = serde_json::to_string(&vc).expect("serialize");
        let round: VerificationCondition = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(round.function, "test_fn");
        // Verify description is non-empty for all kinds
        assert!(!kind.description().is_empty(), "description for {:?}", kind);
    }
}

// ---------------------------------------------------------------------------
// VerificationResult roundtrip
// ---------------------------------------------------------------------------

#[test]
fn test_verification_result_all_variants_roundtrip() {
    let results = vec![
        VerificationResult::Proved {
            solver: "z4".into(),
            time_ms: 5,
            strength: ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: None,
        },
        VerificationResult::Proved {
            solver: "lean5".into(),
            time_ms: 100,
            strength: ProofStrength::constructive(),
            proof_certificate: None,
            solver_warnings: None,
        },
        VerificationResult::Proved {
            solver: "zani".into(),
            time_ms: 50,
            strength: ProofStrength::bounded(100),
            proof_certificate: None,
            solver_warnings: None,
        },
        VerificationResult::Failed {
            solver: "z4".into(),
            time_ms: 7,
            counterexample: Some(Counterexample::new(vec![
                ("a".into(), CounterexampleValue::Uint(u64::MAX as u128)),
                ("b".into(), CounterexampleValue::Uint(1)),
            ])),
        },
        VerificationResult::Failed { solver: "z4".into(), time_ms: 3, counterexample: None },
        VerificationResult::Unknown {
            solver: "z4".into(),
            time_ms: 200,
            reason: "quantifier instantiation limit".into(),
        },
        VerificationResult::Timeout { solver: "z4".into(), timeout_ms: 5000 },
    ];

    for result in &results {
        let json = serde_json::to_string(result).expect("serialize");
        let round: VerificationResult = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(round.solver_name(), result.solver_name());
        assert_eq!(round.time_ms(), result.time_ms());
        assert_eq!(round.is_proved(), result.is_proved());
        assert_eq!(round.is_failed(), result.is_failed());
    }
}

// ---------------------------------------------------------------------------
// StateMachine roundtrip
// ---------------------------------------------------------------------------

#[test]
fn test_state_machine_roundtrip() {
    let sm = StateMachine {
        enum_name: "ConnectionState".into(),
        state_local: 1,
        states: vec![
            StateInfo { name: "Idle".into(), discriminant: 0 },
            StateInfo { name: "Connecting".into(), discriminant: 1 },
            StateInfo { name: "Connected".into(), discriminant: 2 },
            StateInfo { name: "Disconnecting".into(), discriminant: 3 },
        ],
        transitions: vec![
            Transition { from: 0, to: 1, source_block: BlockId(0), target_block: BlockId(1) },
            Transition { from: 1, to: 2, source_block: BlockId(1), target_block: BlockId(2) },
            Transition { from: 2, to: 3, source_block: BlockId(2), target_block: BlockId(3) },
            Transition { from: 3, to: 0, source_block: BlockId(3), target_block: BlockId(0) },
        ],
        initial_state: Some(0),
    };

    let json = serde_json::to_string(&sm).expect("serialize");
    let round: StateMachine = serde_json::from_str(&json).expect("deserialize");
    assert_eq!(round.state_count(), 4);
    assert_eq!(round.transition_count(), 4);
    assert_eq!(round.state_name(0), Some("Idle"));
    assert_eq!(round.state_name(2), Some("Connected"));
    assert_eq!(round.state_name(99), None);
    assert_eq!(round.initial_state, Some(0));
}

// ---------------------------------------------------------------------------
// LivenessProperty + FairnessConstraint roundtrip
// ---------------------------------------------------------------------------

#[test]
fn test_liveness_property_all_operators_roundtrip() {
    let properties = vec![
        LivenessProperty {
            name: "termination".into(),
            operator: TemporalOperator::Eventually,
            predicate: "done".into(),
            consequent: None,
            fairness: vec![],
        },
        LivenessProperty {
            name: "safety".into(),
            operator: TemporalOperator::Always,
            predicate: "no_error".into(),
            consequent: None,
            fairness: vec![],
        },
        LivenessProperty {
            name: "progress".into(),
            operator: TemporalOperator::AlwaysEventually,
            predicate: "served".into(),
            consequent: None,
            fairness: vec![FairnessConstraint::Weak {
                action: "schedule".into(),
                vars: vec!["tasks".into()],
            }],
        },
        LivenessProperty {
            name: "response".into(),
            operator: TemporalOperator::LeadsTo,
            predicate: "request".into(),
            consequent: Some("response".into()),
            fairness: vec![FairnessConstraint::Strong {
                action: "dispatch".into(),
                vars: vec!["queue".into(), "workers".into()],
            }],
        },
    ];

    for prop in &properties {
        let json = serde_json::to_string(prop).expect("serialize");
        let round: LivenessProperty = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(round.name, prop.name);
        assert_eq!(round.operator, prop.operator);
        assert_eq!(round.fairness.len(), prop.fairness.len());
        // Verify description and TLA generation are consistent
        assert!(!prop.description().is_empty());
        assert!(!prop.to_tla().is_empty());
    }
}

// ---------------------------------------------------------------------------
// CrateVerificationResult roundtrip + aggregation
// ---------------------------------------------------------------------------

#[test]
fn test_crate_verification_result_aggregation_roundtrip() {
    let mut crate_result = CrateVerificationResult::new("my_crate");

    let func1 = FunctionVerificationResult {
        function_path: "my_crate::safe_div".into(),
        function_name: "safe_div".into(),
        results: vec![(
            VerificationCondition {
                kind: VcKind::DivisionByZero,
                function: "safe_div".into(),
                location: SourceSpan::default(),
                formula: Formula::Bool(false),
                contract_metadata: None,
            },
            VerificationResult::Proved {
                solver: "z4".into(),
                time_ms: 5,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: None,
                solver_warnings: None,
            },
        )],
        from_notes: 1,
        with_assumptions: 0,
    };

    let func2 = FunctionVerificationResult {
        function_path: "my_crate::midpoint".into(),
        function_name: "midpoint".into(),
        results: vec![
            (
                VerificationCondition {
                    kind: VcKind::ArithmeticOverflow {
                        op: BinOp::Add,
                        operand_tys: (Ty::usize(), Ty::usize()),
                    },
                    function: "midpoint".into(),
                    location: SourceSpan::default(),
                    formula: Formula::Bool(true),
                    contract_metadata: None,
                },
                VerificationResult::Failed {
                    solver: "z4".into(),
                    time_ms: 8,
                    counterexample: None,
                },
            ),
            (
                VerificationCondition {
                    kind: VcKind::DivisionByZero,
                    function: "midpoint".into(),
                    location: SourceSpan::default(),
                    formula: Formula::Bool(false),
                    contract_metadata: None,
                },
                VerificationResult::Proved {
                    solver: "z4".into(),
                    time_ms: 3,
                    strength: ProofStrength::smt_unsat(),
                    proof_certificate: None,
                    solver_warnings: None,
                },
            ),
        ],
        from_notes: 0,
        with_assumptions: 1,
    };

    crate_result.add_function(func1);
    crate_result.add_function(func2);

    // Verify aggregation
    assert_eq!(crate_result.function_count(), 2);
    assert_eq!(crate_result.total_obligations(), 3);
    assert_eq!(crate_result.total_from_notes, 1);
    assert_eq!(crate_result.total_with_assumptions, 1);

    // Serde roundtrip
    let json = serde_json::to_string(&crate_result).expect("serialize");
    let round: CrateVerificationResult = serde_json::from_str(&json).expect("deserialize");
    assert_eq!(round.crate_name, "my_crate");
    assert_eq!(round.function_count(), 2);
    assert_eq!(round.total_obligations(), 3);
    assert_eq!(round.all_results().len(), 3);
}

// ---------------------------------------------------------------------------
// RuntimeDisposition classification
// ---------------------------------------------------------------------------

#[test]
fn test_runtime_disposition_classification_matrix() {
    // Test that the full classification matrix works end-to-end
    let overflow_vc =
        VcKind::ArithmeticOverflow { op: BinOp::Add, operand_tys: (Ty::i32(), Ty::i32()) };
    let postcondition_vc = VcKind::Postcondition;

    // Proved + Auto = Proved
    assert_eq!(
        classify_runtime_disposition(
            &overflow_vc,
            &VerificationResult::Proved {
                solver: "z4".into(),
                time_ms: 1,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: None,
                solver_warnings: None,
            },
            RuntimeCheckPolicy::Auto,
            true,
        ),
        RuntimeDisposition::Proved,
    );

    // Unknown + Auto + has_runtime_fallback = RuntimeChecked
    assert!(matches!(
        classify_runtime_disposition(
            &overflow_vc,
            &VerificationResult::Unknown {
                solver: "z4".into(),
                time_ms: 1,
                reason: "reason".into(),
            },
            RuntimeCheckPolicy::Auto,
            true,
        ),
        RuntimeDisposition::RuntimeChecked { .. },
    ));

    // Unknown + Auto + no_runtime_fallback = Unknown
    assert!(matches!(
        classify_runtime_disposition(
            &postcondition_vc,
            &VerificationResult::Unknown {
                solver: "z4".into(),
                time_ms: 1,
                reason: "reason".into(),
            },
            RuntimeCheckPolicy::Auto,
            true,
        ),
        RuntimeDisposition::Unknown { .. },
    ));

    // Unknown + ForceStatic = CompileError
    assert!(matches!(
        classify_runtime_disposition(
            &overflow_vc,
            &VerificationResult::Unknown {
                solver: "z4".into(),
                time_ms: 1,
                reason: "reason".into(),
            },
            RuntimeCheckPolicy::ForceStatic,
            true,
        ),
        RuntimeDisposition::CompileError { .. },
    ));
}

// ---------------------------------------------------------------------------
// content_hash stability
// ---------------------------------------------------------------------------

#[test]
fn test_content_hash_stable_across_serialization() {
    let func = midpoint_function();
    let hash_before = func.content_hash();

    // Serialize and deserialize
    let json = serde_json::to_string(&func).expect("serialize");
    let round: VerifiableFunction = serde_json::from_str(&json).expect("deserialize");
    let hash_after = round.content_hash();

    assert_eq!(hash_before, hash_after, "content hash must survive serde roundtrip");
}

// ---------------------------------------------------------------------------
// ProofReport roundtrip (legacy format)
// ---------------------------------------------------------------------------

#[test]
fn test_proof_report_legacy_roundtrip() {
    let report = ProofReport {
        crate_name: "my_crate".into(),
        functions: vec![FunctionReport {
            function: "my_crate::foo".into(),
            proved: vec![ProvedProperty {
                description: "division by zero".into(),
                solver: "z4".into(),
                time_ms: 5,
                strength: ProofStrength::smt_unsat(),
                evidence: Some(ProofStrength::smt_unsat().into()),
            }],
            failed: vec![FailedProperty {
                description: "overflow".into(),
                solver: "z4".into(),
                counterexample: Some(Counterexample::new(vec![(
                    "x".into(),
                    CounterexampleValue::Int(i64::MAX as i128),
                )])),
            }],
            unknown: vec![],
        }],
        total_proved: 1,
        total_failed: 1,
        total_unknown: 0,
    };

    let json = serde_json::to_string(&report).expect("serialize");
    let round: ProofReport = serde_json::from_str(&json).expect("deserialize");
    assert_eq!(round.crate_name, "my_crate");
    assert_eq!(round.functions.len(), 1);
    assert_eq!(round.total_proved, 1);
    assert_eq!(round.total_failed, 1);
    assert_eq!(round.functions[0].proved.len(), 1);
    assert_eq!(round.functions[0].failed.len(), 1);
}

// ---------------------------------------------------------------------------
// JsonProofReport roundtrip
// ---------------------------------------------------------------------------

#[test]
fn test_json_proof_report_roundtrip() {
    let report = JsonProofReport {
        metadata: ReportMetadata {
            schema_version: "0.1.0".into(),
            trust_version: "0.1.0".into(),
            timestamp: "2026-03-29T00:00:00Z".into(),
            total_time_ms: 42,
        },
        crate_name: "test_crate".into(),
        summary: CrateSummary {
            functions_analyzed: 2,
            functions_verified: 1,
            functions_runtime_checked: 0,
            functions_with_violations: 1,
            functions_inconclusive: 0,
            total_obligations: 3,
            total_proved: 2,
            total_runtime_checked: 0,
            total_failed: 1,
            total_unknown: 0,
            verdict: CrateVerdict::HasViolations,
        },
        functions: vec![FunctionProofReport {
            function: "test_crate::ok_fn".into(),
            summary: FunctionSummary {
                total_obligations: 1,
                proved: 1,
                runtime_checked: 0,
                failed: 0,
                unknown: 0,
                total_time_ms: 5,
                max_proof_level: Some(ProofLevel::L0Safety),
                verdict: FunctionVerdict::Verified,
            },
            obligations: vec![ObligationReport {
                description: "division by zero".into(),
                kind: "division_by_zero".into(),
                proof_level: ProofLevel::L0Safety,
                location: None,
                outcome: ObligationOutcome::Proved { strength: ProofStrength::smt_unsat() },
                solver: "z4".into(),
                time_ms: 5,
                evidence: None,
            }],
        }],
    };

    let json = serde_json::to_string_pretty(&report).expect("serialize");
    let round: JsonProofReport = serde_json::from_str(&json).expect("deserialize");
    assert_eq!(round.crate_name, "test_crate");
    assert_eq!(round.summary.verdict, CrateVerdict::HasViolations);
    assert_eq!(round.functions.len(), 1);
    assert_eq!(round.functions[0].summary.verdict, FunctionVerdict::Verified);
}

// ---------------------------------------------------------------------------
// VcKind proof_level consistency
// ---------------------------------------------------------------------------

#[test]
fn test_vc_kind_proof_level_consistency() {
    // L0 Safety kinds
    let l0_kinds = vec![
        VcKind::ArithmeticOverflow { op: BinOp::Add, operand_tys: (Ty::i32(), Ty::i32()) },
        VcKind::DivisionByZero,
        VcKind::RemainderByZero,
        VcKind::IndexOutOfBounds,
        VcKind::SliceBoundsCheck,
        VcKind::Assertion { message: "test".into() },
        VcKind::CastOverflow { from_ty: Ty::i32(), to_ty: Ty::u32() },
        VcKind::NegationOverflow { ty: Ty::i32() },
        VcKind::Unreachable,
    ];
    for kind in &l0_kinds {
        assert_eq!(kind.proof_level(), ProofLevel::L0Safety, "expected L0 for {:?}", kind);
    }

    // L1 Functional kinds
    let l1_kinds = vec![
        VcKind::Precondition { callee: "f".into() },
        VcKind::Postcondition,
        VcKind::NonTermination { context: "loop".into(), measure: "n".into() },
    ];
    for kind in &l1_kinds {
        assert_eq!(kind.proof_level(), ProofLevel::L1Functional, "expected L1 for {:?}", kind);
    }

    // L2 Domain kinds
    let l2_kinds = vec![
        VcKind::Deadlock,
        VcKind::DeadState { state: "s".into() },
        VcKind::Temporal { property: "p".into() },
    ];
    for kind in &l2_kinds {
        assert_eq!(kind.proof_level(), ProofLevel::L2Domain, "expected L2 for {:?}", kind);
    }
}
