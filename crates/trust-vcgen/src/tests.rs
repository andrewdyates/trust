use super::*;
use std::path::PathBuf;
use trust_types::{Operand, Place, Sort, SourceSpan, VcKind};

/// Build the midpoint function MIR.
pub fn midpoint_function() -> VerifiableFunction {
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

fn fixture_dir() -> PathBuf {
    let manifest = env!("CARGO_MANIFEST_DIR");
    PathBuf::from(manifest).join("../trust-integration-tests/fixtures/real_mir")
}

fn load_fixture(name: &str) -> VerifiableFunction {
    let path = fixture_dir().join(format!("{name}.json"));
    let json = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("failed to read fixture {}: {e}", path.display()));
    serde_json::from_str(&json)
        .unwrap_or_else(|e| panic!("failed to parse fixture {}: {e}", path.display()))
}

#[test]
fn test_generate_vcs_midpoint() {
    let func = midpoint_function();
    let vcs = generate_vcs(&func);

    // tRust #953: `generate_vcs` emits safety VCs (overflow, divzero) so that
    // callers which invoke it directly (e.g., `real_z4_verification`,
    // `m5_e2e_loop`) receive real SMT formulas. The midpoint body has one
    // `CheckedBinaryOp(Add)` + `Assert(Overflow(Add))` pair in bb0 and a
    // constant-divisor `Div(_, 2)` in bb1. The constant divisor is skipped,
    // so we expect exactly one `ArithmeticOverflow` VC.
    let overflow_vcs: Vec<_> =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { .. })).collect();
    assert_eq!(
        overflow_vcs.len(),
        1,
        "midpoint has one CheckedBinaryOp(Add) → one overflow VC, got {}",
        overflow_vcs.len()
    );
    assert!(
        !vcs.iter().any(|vc| matches!(vc.kind, VcKind::DivisionByZero)),
        "constant divisor `2` must not produce a DivisionByZero VC"
    );
}

#[test]
fn test_division_vc_carries_same_block_defs_for_temp_divisor() {
    let span = SourceSpan::default();
    let func = VerifiableFunction {
        name: "div_with_temp".to_string(),
        def_path: "test::div_with_temp".to_string(),
        span: span.clone(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("tmp".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(1))),
                        span: span.clone(),
                    },
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Div,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: span.clone(),
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::i32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let vcs = generate_vcs(&func);
    let div_vc = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::DivisionByZero))
        .expect("temp divisor should still emit a DivisionByZero VC");

    assert!(
        contains_eq_int_formula(&div_vc.formula, 1),
        "same-block temp definitions must be conjoined into the Div VC, got {:?}",
        div_vc.formula
    );
}

fn contains_eq_int_formula(f: &Formula, value: i128) -> bool {
    match f {
        Formula::Eq(lhs, rhs) => matches!(
            (&**lhs, &**rhs),
            (Formula::Var(_, _), Formula::Int(v)) | (Formula::Int(v), Formula::Var(_, _))
                if *v == value
        ),
        Formula::And(clauses) | Formula::Or(clauses) => {
            clauses.iter().any(|clause| contains_eq_int_formula(clause, value))
        }
        Formula::Not(inner) => contains_eq_int_formula(inner, value),
        Formula::Implies(lhs, rhs) => {
            contains_eq_int_formula(lhs, value) || contains_eq_int_formula(rhs, value)
        }
        _ => false,
    }
}

#[test]
fn test_operand_ty_resolution() {
    let func = midpoint_function();

    assert_eq!(operand_ty(&func, &Operand::Copy(Place::local(1))), Some(Ty::usize()));
    assert_eq!(operand_ty(&func, &Operand::Copy(Place::field(3, 1))), Some(Ty::Bool));
    assert_eq!(operand_ty(&func, &Operand::Copy(Place::field(3, 0))), Some(Ty::usize()));
    assert_eq!(
        operand_ty(&func, &Operand::Constant(ConstValue::Uint(2, 64))),
        Some(Ty::Int { width: 64, signed: false })
    );
}

#[test]
fn test_place_to_var_name() {
    let func = midpoint_function();

    assert_eq!(place_to_var_name(&func, &Place::local(1)), "a");
    assert_eq!(place_to_var_name(&func, &Place::local(2)), "b");
    assert_eq!(place_to_var_name(&func, &Place::local(0)), "_0");
    assert_eq!(place_to_var_name(&func, &Place::field(3, 1)), "_3.1");
}

// tRust: Tests for verification level filtering (#42).

/// Helper: build a VC with the given kind and function name.
fn make_vc(kind: VcKind) -> VerificationCondition {
    VerificationCondition {
        kind,
        function: "test_fn".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    }
}

#[test]
fn test_filter_vcs_by_level_l0_keeps_only_safety() {
    let vcs = vec![
        make_vc(VcKind::DivisionByZero),
        make_vc(VcKind::Postcondition),
        make_vc(VcKind::Deadlock),
        make_vc(VcKind::ArithmeticOverflow {
            op: BinOp::Add,
            operand_tys: (Ty::usize(), Ty::usize()),
        }),
    ];

    let filtered = filter_vcs_by_level(vcs, ProofLevel::L0Safety);
    assert_eq!(filtered.len(), 2, "L0 should keep only safety VCs");
    assert_eq!(filtered[0].kind.proof_level(), ProofLevel::L0Safety);
    assert_eq!(filtered[1].kind.proof_level(), ProofLevel::L0Safety);
}

#[test]
fn test_filter_vcs_by_level_l1_keeps_safety_and_functional() {
    let vcs = vec![
        make_vc(VcKind::DivisionByZero),
        make_vc(VcKind::Postcondition),
        make_vc(VcKind::Deadlock),
        make_vc(VcKind::Precondition { callee: "foo".to_string() }),
    ];

    let filtered = filter_vcs_by_level(vcs, ProofLevel::L1Functional);
    assert_eq!(filtered.len(), 3, "L1 should keep safety + functional VCs");
    for vc in &filtered {
        assert!(vc.kind.proof_level() <= ProofLevel::L1Functional, "all VCs should be at most L1");
    }
}

#[test]
fn test_filter_vcs_by_level_l2_keeps_all() {
    let vcs = vec![
        make_vc(VcKind::DivisionByZero),
        make_vc(VcKind::Postcondition),
        make_vc(VcKind::Deadlock),
        make_vc(VcKind::Temporal { property: "liveness".to_string() }),
    ];

    let filtered = filter_vcs_by_level(vcs, ProofLevel::L2Domain);
    assert_eq!(filtered.len(), 4, "L2 should keep all VCs");
}

#[test]
fn test_filter_vcs_by_level_empty_input() {
    let filtered = filter_vcs_by_level(vec![], ProofLevel::L0Safety);
    assert!(filtered.is_empty(), "filtering empty vec should return empty vec");
}

#[test]
fn test_proof_level_ordering() {
    assert!(ProofLevel::L0Safety < ProofLevel::L1Functional);
    assert!(ProofLevel::L1Functional < ProofLevel::L2Domain);
    assert!(ProofLevel::L0Safety < ProofLevel::L2Domain);
}

// tRust #21: Guard condition extraction and VC threading tests.

/// Build a function with SwitchInt branching into blocks with arithmetic.
///
/// ```
/// fn guarded_div(flag: bool, x: u32, y: u32) -> u32 {
///     if flag {        // SwitchInt on _1 (flag)
///         x / y        // bb1: div by zero VC should have guard: flag == 1
///     } else {
///         0            // bb2: no VCs
///     }
/// }
/// ```
fn guarded_div_function() -> VerifiableFunction {
    VerifiableFunction {
        name: "guarded_div".to_string(),
        def_path: "test::guarded_div".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::Bool, name: Some("flag".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("x".into()) },
                LocalDecl { index: 3, ty: Ty::u32(), name: Some("y".into()) },
                LocalDecl { index: 4, ty: Ty::u32(), name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(1)),
                        targets: vec![(1, BlockId(1))],
                        otherwise: BlockId(2),
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Div,
                                Operand::Copy(Place::local(2)),
                                Operand::Copy(Place::local(3)),
                            ),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(4))),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Return,
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 32))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 3,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn test_guarded_div_vc_has_guard_assumption() {
    // tRust #953: DivisionByZero VCs are again emitted by `generate_vcs`.
    // `guarded_div_function` has a `Div(a, b)` with a variable divisor `b`,
    // so exactly one DivisionByZero VC is expected.
    let func = guarded_div_function();
    let vcs = generate_vcs(&func);

    let div_vcs: Vec<_> =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::DivisionByZero)).collect();
    assert_eq!(div_vcs.len(), 1, "one Div(_, var) → one DivisionByZero VC, got {}", div_vcs.len());
}

#[test]
fn test_discover_clauses_reports_switch_int() {
    let func = guarded_div_function();
    let clauses = discover_clauses(&func);

    assert_eq!(clauses.len(), 2, "SwitchInt with 1 target + otherwise = 2 clauses");
    assert!(clauses.iter().any(|c| matches!(c.target, ClauseTarget::Block(BlockId(1)))
        && matches!(&c.guard, GuardCondition::SwitchIntMatch { value: 1, .. })));
    assert!(clauses.iter().any(|c| matches!(c.target, ClauseTarget::Block(BlockId(2)))
        && matches!(&c.guard, GuardCondition::SwitchIntOtherwise { .. })));
}

#[test]
fn test_build_path_map_shows_accumulated_guards() {
    let func = guarded_div_function();
    let path_map = build_path_map(&func);

    assert_eq!(path_map.len(), 3, "3 blocks should all be reachable");

    let bb0 = path_map.iter().find(|e| e.block == BlockId(0)).expect("bb0");
    assert!(bb0.guards.is_empty(), "entry block has no guards");

    let bb1 = path_map.iter().find(|e| e.block == BlockId(1)).expect("bb1");
    assert_eq!(bb1.guards.len(), 1);
    assert!(matches!(&bb1.guards[0], GuardCondition::SwitchIntMatch { value: 1, .. }));

    let bb2 = path_map.iter().find(|e| e.block == BlockId(2)).expect("bb2");
    assert_eq!(bb2.guards.len(), 1);
    assert!(matches!(&bb2.guards[0], GuardCondition::SwitchIntOtherwise { .. }));
}

#[test]
fn test_discovered_clauses_json_serialization() {
    let func = guarded_div_function();
    let clauses = discover_clauses(&func);

    let json = serde_json::to_string(&clauses).expect("serialize clauses");
    let round: Vec<DiscoveredClause> = serde_json::from_str(&json).expect("deserialize clauses");
    assert_eq!(round.len(), clauses.len());
}

#[test]
fn test_path_map_json_serialization() {
    let func = guarded_div_function();
    let path_map = build_path_map(&func);

    let json = serde_json::to_string(&path_map).expect("serialize path map");
    let round: Vec<PathMapEntry> = serde_json::from_str(&json).expect("deserialize path map");
    assert_eq!(round.len(), path_map.len());
}

#[test]
fn test_midpoint_bb1_guarded_by_assert() {
    let func = midpoint_function();
    let path_map = build_path_map(&func);

    let bb1 = path_map.iter().find(|e| e.block == BlockId(1)).expect("bb1");
    assert_eq!(bb1.guards.len(), 1, "bb1 should have 1 guard from the Assert");
    assert!(matches!(&bb1.guards[0], GuardCondition::AssertHolds { expected: false, .. }));
}

/// Build a function with nested guards (SwitchInt -> Assert -> block with VCs).
fn nested_guard_function() -> VerifiableFunction {
    VerifiableFunction {
        name: "nested".to_string(),
        def_path: "test::nested".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::Bool, name: Some("flag".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("x".into()) },
                LocalDecl { index: 3, ty: Ty::u32(), name: Some("y".into()) },
                LocalDecl { index: 4, ty: Ty::Bool, name: Some("check".into()) },
                LocalDecl { index: 5, ty: Ty::u32(), name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(1)),
                        targets: vec![(1, BlockId(1))],
                        otherwise: BlockId(3),
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::local(4)),
                        expected: true,
                        msg: AssertMessage::Custom("check must hold".into()),
                        target: BlockId(2),
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(5),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Div,
                            Operand::Copy(Place::local(2)),
                            Operand::Copy(Place::local(3)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 32))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 4,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn test_nested_guards_accumulate() {
    let func = nested_guard_function();
    let path_map = build_path_map(&func);

    let bb2 = path_map.iter().find(|e| e.block == BlockId(2)).expect("bb2");
    assert_eq!(bb2.guards.len(), 2, "bb2 should have 2 accumulated guards");
    assert!(matches!(&bb2.guards[0], GuardCondition::SwitchIntMatch { value: 1, .. }));
    assert!(matches!(&bb2.guards[1], GuardCondition::AssertHolds { expected: true, .. }));
}

#[test]
fn test_nested_guards_in_vc_formula() {
    // tRust #953: DivisionByZero VCs are again emitted by `generate_vcs`.
    // `nested_guard_function` has one `Div(x, y)` with a variable divisor,
    // so exactly one DivisionByZero VC is expected.
    let func = nested_guard_function();
    let vcs = generate_vcs(&func);

    let div_vcs: Vec<_> =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::DivisionByZero)).collect();
    assert_eq!(div_vcs.len(), 1, "one Div(_, var) → one DivisionByZero VC, got {}", div_vcs.len());
}

/// Build a function with 3-way match (enum variant SwitchInt).
fn match_exhaustive_function() -> VerifiableFunction {
    VerifiableFunction {
        name: "match_fn".to_string(),
        def_path: "test::match_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Adt {
                        name: "Status".into(),
                        fields: vec![("discriminant".into(), Ty::u32())],
                    },
                    name: Some("status".into()),
                },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("x".into()) },
                LocalDecl { index: 3, ty: Ty::u32(), name: Some("y".into()) },
                LocalDecl { index: 4, ty: Ty::u32(), name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(1)),
                        targets: vec![(0, BlockId(1)), (1, BlockId(2))],
                        otherwise: BlockId(3),
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Div,
                            Operand::Copy(Place::local(2)),
                            Operand::Copy(Place::local(3)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
                BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Unreachable },
            ],
            arg_count: 3,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn test_match_exhaustive_guards() {
    let func = match_exhaustive_function();
    let clauses = discover_clauses(&func);

    assert_eq!(clauses.len(), 3);

    let path_map = build_path_map(&func);

    let bb1 = path_map.iter().find(|e| e.block == BlockId(1)).expect("bb1");
    assert_eq!(bb1.guards.len(), 1);
    assert!(matches!(&bb1.guards[0], GuardCondition::SwitchIntMatch { value: 0, .. }));

    let bb2 = path_map.iter().find(|e| e.block == BlockId(2)).expect("bb2");
    assert_eq!(bb2.guards.len(), 1);
    assert!(matches!(&bb2.guards[0], GuardCondition::SwitchIntMatch { value: 1, .. }));

    let bb3 = path_map.iter().find(|e| e.block == BlockId(3)).expect("bb3");
    assert_eq!(bb3.guards.len(), 1);
    assert!(matches!(
        &bb3.guards[0],
        GuardCondition::SwitchIntOtherwise { excluded_values, .. }
            if excluded_values == &vec![0, 1]
    ));
}

#[test]
fn test_match_div_vc_has_variant_guard() {
    // tRust #953: DivisionByZero VCs are again emitted by `generate_vcs`.
    // `match_exhaustive_function` has one `Div(x, y)` with a variable divisor
    // guarded by a SwitchInt match arm, so exactly one DivisionByZero VC is
    // expected.
    let func = match_exhaustive_function();
    let vcs = generate_vcs(&func);

    let div_vcs: Vec<_> =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::DivisionByZero)).collect();
    assert_eq!(div_vcs.len(), 1, "one Div(_, var) → one DivisionByZero VC, got {}", div_vcs.len());
}

// -----------------------------------------------------------------------
// tRust #214: Comprehensive arithmetic VC coverage tests
// -----------------------------------------------------------------------

/// Helper: build a function with a single BinOp on two variable operands.
fn make_binop_func(op: BinOp, ty: Ty) -> VerifiableFunction {
    VerifiableFunction {
        name: format!("arith_{op:?}"),
        def_path: format!("test::arith_{op:?}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: ty.clone(), name: None },
                LocalDecl { index: 1, ty: ty.clone(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: ty.clone(), name: Some("b".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::BinaryOp(
                        op,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

// tRust #792: overflow, divzero, shifts, casts, and float_ops checks are now
// handled by zani-lib via the MIR router pipeline. The following tests verify
// that trust-vcgen no longer produces these VcKinds.

#[test]
fn test_vc_coverage_add_no_overflow_vc() {
    let func = make_binop_func(BinOp::Add, Ty::u32());
    let vcs = generate_vcs(&func);
    assert!(
        !vcs.iter().any(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { .. })),
        "ArithmeticOverflow VCs now handled by zani-lib"
    );
}

#[test]
fn test_vc_coverage_sub_no_overflow_vc() {
    let func = make_binop_func(BinOp::Sub, Ty::u32());
    let vcs = generate_vcs(&func);
    assert!(
        !vcs.iter().any(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { .. })),
        "ArithmeticOverflow VCs now handled by zani-lib"
    );
}

#[test]
fn test_vc_coverage_mul_no_overflow_vc() {
    let func = make_binop_func(BinOp::Mul, Ty::u32());
    let vcs = generate_vcs(&func);
    assert!(
        !vcs.iter().any(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { .. })),
        "ArithmeticOverflow VCs now handled by zani-lib"
    );
}

#[test]
fn test_vc_coverage_div_no_divzero_vc() {
    // tRust #953: DivisionByZero VCs are emitted again for `Div(_, var)`.
    let func = make_binop_func(BinOp::Div, Ty::u32());
    let vcs = generate_vcs(&func);
    assert!(
        vcs.iter().any(|vc| matches!(vc.kind, VcKind::DivisionByZero)),
        "Div(_, var) must emit DivisionByZero VC"
    );
}

#[test]
fn test_vc_coverage_rem_no_remzero_vc() {
    // tRust #953: RemainderByZero VCs are emitted again for `Rem(_, var)`.
    let func = make_binop_func(BinOp::Rem, Ty::u32());
    let vcs = generate_vcs(&func);
    assert!(
        vcs.iter().any(|vc| matches!(vc.kind, VcKind::RemainderByZero)),
        "Rem(_, var) must emit RemainderByZero VC"
    );
}

#[test]
fn test_vc_coverage_signed_div_no_overflow_vc() {
    // tRust #953: Signed `Div(_, var)` emits DivisionByZero. Overflow for
    // the signed `i32::MIN / -1` case is still handled by zani-lib via
    // CheckedBinaryOp — trust-vcgen's `generate_vcs` does not materialise
    // an ArithmeticOverflow VC for a bare `BinaryOp::Div`.
    let func = make_binop_func(BinOp::Div, Ty::i32());
    let vcs = generate_vcs(&func);
    assert!(
        vcs.iter().any(|vc| matches!(vc.kind, VcKind::DivisionByZero)),
        "signed Div(_, var) must emit DivisionByZero VC"
    );
    assert!(
        !vcs.iter().any(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { .. })),
        "bare BinaryOp::Div must not emit ArithmeticOverflow VC"
    );
}

#[test]
fn test_vc_coverage_signed_rem_no_overflow_vc() {
    // tRust #953: Signed `Rem(_, var)` emits RemainderByZero. Overflow for
    // the signed edge case is still out-of-scope for bare `BinaryOp::Rem`.
    let func = make_binop_func(BinOp::Rem, Ty::i32());
    let vcs = generate_vcs(&func);
    assert!(
        vcs.iter().any(|vc| matches!(vc.kind, VcKind::RemainderByZero)),
        "signed Rem(_, var) must emit RemainderByZero VC"
    );
    assert!(
        !vcs.iter().any(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { .. })),
        "bare BinaryOp::Rem must not emit ArithmeticOverflow VC"
    );
}

#[test]
fn test_vc_coverage_shl_no_shift_overflow_vc() {
    let func = make_binop_func(BinOp::Shl, Ty::u32());
    let vcs = generate_vcs(&func);
    assert!(
        !vcs.iter().any(|vc| matches!(vc.kind, VcKind::ShiftOverflow { .. })),
        "ShiftOverflow VCs now handled by zani-lib"
    );
}

#[test]
fn test_vc_coverage_shr_no_shift_overflow_vc() {
    let func = make_binop_func(BinOp::Shr, Ty::u32());
    let vcs = generate_vcs(&func);
    assert!(
        !vcs.iter().any(|vc| matches!(vc.kind, VcKind::ShiftOverflow { .. })),
        "ShiftOverflow VCs now handled by zani-lib"
    );
}
#[cfg(not(feature = "pipeline-v2"))]
#[test]
fn test_vc_coverage_neg_generates_negation_overflow() {
    // Build a function with UnaryOp::Neg on a signed variable
    let func = VerifiableFunction {
        name: "arith_neg".to_string(),
        def_path: "test::arith_neg".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::UnaryOp(trust_types::UnOp::Neg, Operand::Copy(Place::local(1))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::i32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    let vcs = generate_vcs(&func);
    assert!(
        vcs.iter().any(|vc| matches!(vc.kind, VcKind::NegationOverflow { .. })),
        "Neg on signed integers must generate NegationOverflow VC"
    );
}

#[test]
fn test_vc_coverage_bitwise_ops_no_vcs() {
    // BitAnd, BitOr, BitXor should NOT generate any arithmetic VCs
    for op in [BinOp::BitAnd, BinOp::BitOr, BinOp::BitXor] {
        let func = make_binop_func(op, Ty::u32());
        let vcs = generate_vcs(&func);
        let arith_vcs: Vec<_> = vcs
            .iter()
            .filter(|vc| {
                matches!(
                    vc.kind,
                    VcKind::ArithmeticOverflow { .. }
                        | VcKind::DivisionByZero
                        | VcKind::RemainderByZero
                        | VcKind::ShiftOverflow { .. }
                        | VcKind::NegationOverflow { .. }
                )
            })
            .collect();
        assert!(
            arith_vcs.is_empty(),
            "Bitwise op {op:?} should not generate any arithmetic VCs, got {}",
            arith_vcs.len()
        );
    }
}

#[test]
fn test_vc_coverage_comparison_ops_no_vcs() {
    // Eq, Ne, Lt, Le, Gt, Ge should NOT generate any arithmetic VCs
    for op in [BinOp::Eq, BinOp::Ne, BinOp::Lt, BinOp::Le, BinOp::Gt, BinOp::Ge] {
        let func = make_binop_func(op, Ty::u32());
        let vcs = generate_vcs(&func);
        let arith_vcs: Vec<_> = vcs
            .iter()
            .filter(|vc| {
                matches!(
                    vc.kind,
                    VcKind::ArithmeticOverflow { .. }
                        | VcKind::DivisionByZero
                        | VcKind::RemainderByZero
                        | VcKind::ShiftOverflow { .. }
                        | VcKind::NegationOverflow { .. }
                )
            })
            .collect();
        assert!(
            arith_vcs.is_empty(),
            "Comparison op {op:?} should not generate any arithmetic VCs, got {}",
            arith_vcs.len()
        );
    }
}

// tRust: Tests for #409 (operand wildcard) and #406 (float constants).

#[test]
fn test_operand_to_formula_float_produces_bitvec_constant() {
    // #406: Float constants should lower to their IEEE-754 bit pattern.
    let func = midpoint_function();
    let float_op = Operand::Constant(ConstValue::Float(3.125));
    let formula = operand_to_formula(&func, &float_op);
    match formula {
        Formula::BitVec { value, width } => {
            assert_eq!(width, 64, "float constants should lower to 64-bit bitvectors");
            assert_eq!(
                value,
                i128::from(3.125f64.to_bits()),
                "float constants should preserve their IEEE-754 bit pattern"
            );
        }
        other => panic!("expected Formula::BitVec for float constant, got: {other:?}"),
    }
}

#[test]
fn test_operand_ty_float_constant() {
    // #406: Float constant type should resolve to Float, not Unit.
    let func = midpoint_function();
    let float_op = Operand::Constant(ConstValue::Float(2.875));
    let ty = operand_ty(&func, &float_op);
    assert_eq!(ty, Some(Ty::Float { width: 64 }), "float constant should have Float type");
}

#[test]
fn test_operand_to_formula_unit_not_true() {
    // #409: Unit operand should produce Formula::Int(0), NOT Formula::Bool(true).
    // This validates that the wildcard fallback returning Bool(true) is gone.
    let func = midpoint_function();
    let unit_op = Operand::Constant(ConstValue::Unit);
    let formula = operand_to_formula(&func, &unit_op);
    assert_eq!(formula, Formula::Int(0), "Unit operand should produce Int(0), not Bool(true)");
}

#[test]
fn test_generate_vcs_with_discharge_returns_split() {
    // tRust #357, #428: Verify that generate_vcs_with_discharge produces
    // both solver VCs and discharged results without panicking.
    let func = midpoint_function();
    let (solver_vcs, discharged) = generate_vcs_with_discharge(&func);

    // Total should equal what generate_vcs returns.
    let all_vcs = generate_vcs(&func);
    assert_eq!(
        solver_vcs.len() + discharged.len(),
        all_vcs.len(),
        "discharge split must preserve total VC count"
    );

    // All discharged results should be Proved.
    for (_vc, result) in &discharged {
        assert!(result.is_proved(), "discharged VCs must be Proved");
    }
}

// -----------------------------------------------------------------------
// tRust #361: VC generator integrity tests
// -----------------------------------------------------------------------

#[test]
fn test_float_div_by_variable_generates_vc_through_pipeline() {
    let ty = Ty::Float { width: 64 };
    let func = VerifiableFunction {
        name: "float_div_pipeline".to_string(),
        def_path: "test::float_div_pipeline".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: ty.clone(), name: None },
                LocalDecl { index: 1, ty: ty.clone(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: ty.clone(), name: Some("b".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Div,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let vcs = generate_vcs(&func);
    let float_vcs: Vec<_> =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::FloatDivisionByZero)).collect();
    assert!(
        !vcs.iter().any(|vc| matches!(vc.kind, VcKind::DivisionByZero)),
        "float Div must not fall back to integer DivisionByZero"
    );
    assert_eq!(float_vcs.len(), 1, "float Div(_, var) must emit one FloatDivisionByZero VC");
    assert_eq!(
        float_vcs[0].formula,
        Formula::Eq(
            Box::new(Formula::Var("b".into(), Sort::BitVec(64))),
            Box::new(Formula::BitVec { value: 0, width: 64 }),
        ),
        "float Div VC should compare the divisor bit-pattern against +0.0/-0.0"
    );
}

#[test]
fn test_float_add_no_overflow_vc_through_pipeline() {
    // Float overflow is still routed through the native backend, not emitted by
    // the in-tree pipeline-v2 generator.
    let ty = Ty::Float { width: 64 };
    let func = VerifiableFunction {
        name: "float_add_pipeline".to_string(),
        def_path: "test::float_add_pipeline".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: ty.clone(), name: None },
                LocalDecl { index: 1, ty: ty.clone(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: ty.clone(), name: Some("b".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Add,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let vcs = generate_vcs(&func);
    assert!(
        !vcs.iter().any(|vc| matches!(vc.kind, VcKind::FloatOverflowToInfinity { .. })),
        "plain float Add without range guards must not emit a placeholder FloatOverflowToInfinity VC"
    );
}

fn formula_contains(formula: &Formula, predicate: &impl Fn(&Formula) -> bool) -> bool {
    if predicate(formula) {
        return true;
    }
    formula.children().into_iter().any(|child| formula_contains(child, predicate))
}

#[test]
fn test_float_div_safe_path_threads_zero_guard_definition() {
    let span = SourceSpan::default();
    let ty = Ty::Float { width: 64 };
    let func = VerifiableFunction {
        name: "float_divide_safe".to_string(),
        def_path: "test::float_divide_safe".to_string(),
        span: span.clone(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: ty.clone(), name: None },
                LocalDecl { index: 1, ty: ty.clone(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: ty.clone(), name: Some("y".into()) },
                LocalDecl { index: 3, ty: Ty::Bool, name: Some("is_zero".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Eq,
                            Operand::Copy(Place::local(2)),
                            Operand::Constant(ConstValue::Float(0.0)),
                        ),
                        span: span.clone(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(3)),
                        targets: vec![(0, BlockId(2))],
                        otherwise: BlockId(1),
                        span: span.clone(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Float(0.0))),
                        span: span.clone(),
                    }],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Div,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: span.clone(),
                    }],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let vcs = generate_vcs(&func);
    let vc = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::FloatDivisionByZero))
        .expect("guarded float Div should still produce a FloatDivisionByZero VC");

    assert!(
        formula_contains(&vc.formula, &|node| matches!(
            node,
            Formula::Not(inner)
                if matches!(&**inner, Formula::Var(name, Sort::Bool) if name == "is_zero")
        )),
        "safe float-div VC should carry the false-branch guard, got {:?}",
        vc.formula
    );
    assert!(
        formula_contains(&vc.formula, &|node| matches!(
            node,
            Formula::Eq(lhs, rhs)
                if matches!(&**lhs, Formula::Var(name, Sort::Bool) if name == "is_zero")
                    && matches!(
                        &**rhs,
                        Formula::Eq(inner_lhs, inner_rhs)
                            if matches!(&**inner_lhs, Formula::Var(name, Sort::BitVec(64)) if name == "y")
                                && matches!(
                                    &**inner_rhs,
                                    Formula::BitVec { value: 0, width: 64 }
                                )
                    )
        )),
        "safe float-div VC should propagate `is_zero = (y == 0.0)`, got {:?}",
        vc.formula
    );
}

#[test]
fn test_float_overflow_safe_path_generates_guarded_obligation() {
    let span = SourceSpan::default();
    let ty = Ty::Float { width: 64 };
    let safe_limit = ConstValue::Float(1.0e300);
    let func = VerifiableFunction {
        name: "float_add_safe".to_string(),
        def_path: "test::float_add_safe".to_string(),
        span: span.clone(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: ty.clone(), name: None },
                LocalDecl { index: 1, ty: ty.clone(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: ty.clone(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: Ty::Bool, name: Some("a_too_large".into()) },
                LocalDecl { index: 4, ty: ty.clone(), name: Some("abs_a".into()) },
                LocalDecl { index: 5, ty: Ty::Bool, name: Some("b_too_large".into()) },
                LocalDecl { index: 6, ty: ty.clone(), name: Some("abs_b".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        func: "core::f64::<impl f64>::abs".to_string(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(4),
                        target: Some(BlockId(1)),
                        span: span.clone(),
                        atomic: None,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Gt,
                            Operand::Copy(Place::local(4)),
                            Operand::Constant(safe_limit.clone()),
                        ),
                        span: span.clone(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(3)),
                        targets: vec![(0, BlockId(2))],
                        otherwise: BlockId(4),
                        span: span.clone(),
                    },
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        func: "core::f64::<impl f64>::abs".to_string(),
                        args: vec![Operand::Copy(Place::local(2))],
                        dest: Place::local(6),
                        target: Some(BlockId(3)),
                        span: span.clone(),
                        atomic: None,
                    },
                },
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![Statement::Assign {
                        place: Place::local(5),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Gt,
                            Operand::Copy(Place::local(6)),
                            Operand::Constant(safe_limit),
                        ),
                        span: span.clone(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(5)),
                        targets: vec![(0, BlockId(5))],
                        otherwise: BlockId(4),
                        span: span.clone(),
                    },
                },
                BasicBlock {
                    id: BlockId(4),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Float(0.0))),
                        span: span.clone(),
                    }],
                    terminator: Terminator::Goto(BlockId(6)),
                },
                BasicBlock {
                    id: BlockId(5),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: span.clone(),
                    }],
                    terminator: Terminator::Goto(BlockId(6)),
                },
                BasicBlock { id: BlockId(6), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let vcs = generate_vcs(&func);
    let vc = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::FloatOverflowToInfinity { op: BinOp::Add, .. }))
        .expect("guarded float Add should generate a FloatOverflowToInfinity VC");

    assert!(
        formula_contains(&vc.formula, &|node| matches!(
            node,
            Formula::Or(disjuncts)
                if disjuncts.len() == 2
                    && disjuncts.iter().any(|item| matches!(item, Formula::Var(name, Sort::Bool) if name == "a_too_large"))
                    && disjuncts.iter().any(|item| matches!(item, Formula::Var(name, Sort::Bool) if name == "b_too_large"))
        )),
        "safe float-overflow VC should require one of the range guards to fail, got {:?}",
        vc.formula
    );
    assert!(
        formula_contains(&vc.formula, &|node| matches!(
            node,
            Formula::Not(inner)
                if matches!(&**inner, Formula::Var(name, Sort::Bool) if name == "a_too_large")
        )),
        "safe float-overflow VC should carry the first false-branch guard, got {:?}",
        vc.formula
    );
    assert!(
        formula_contains(&vc.formula, &|node| matches!(
            node,
            Formula::Not(inner)
                if matches!(&**inner, Formula::Var(name, Sort::Bool) if name == "b_too_large")
        )),
        "safe float-overflow VC should carry the second false-branch guard, got {:?}",
        vc.formula
    );
}

#[test]
fn test_begin_panic_call_generates_guarded_assertion_vc() {
    let span = SourceSpan::default();
    let func = VerifiableFunction {
        name: "panic_assertion".to_string(),
        def_path: "test::panic_assertion".to_string(),
        span: span.clone(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: Ty::Bool, name: Some("ok".into()) },
                LocalDecl { index: 3, ty: Ty::Unit, name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Ge,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Int(0)),
                        ),
                        span: span.clone(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(2)),
                        targets: vec![(0, BlockId(1))],
                        otherwise: BlockId(2),
                        span: span.clone(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        func: "std::rt::begin_panic::<&str>".to_string(),
                        args: vec![],
                        dest: Place::local(3),
                        target: None,
                        span: span.clone(),
                        atomic: None,
                    },
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                        span: span.clone(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 1,
            return_ty: Ty::i32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let vcs = generate_vcs(&func);
    let assert_vc = vcs
        .iter()
        .find(|vc| matches!(&vc.kind, VcKind::Assertion { message } if message.contains("begin_panic")))
        .expect("begin_panic should generate an Assertion VC");

    assert!(
        matches!(
            &assert_vc.formula,
            Formula::And(clauses)
                if clauses.iter().any(|clause| matches!(
                    clause,
                    Formula::Not(inner)
                        if matches!(&**inner, Formula::Var(name, Sort::Bool) if name == "ok")
                ))
        ),
        "Assertion VC should be guarded by the false branch reaching begin_panic, got {:?}",
        assert_vc.formula
    );
}

#[test]
fn test_unreachable_display_call_generates_guarded_unreachable_vc() {
    let span = SourceSpan::default();
    let func = VerifiableFunction {
        name: "panic_unreachable".to_string(),
        def_path: "test::panic_unreachable".to_string(),
        span: span.clone(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::Bool, name: Some("flag".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(1)),
                        targets: vec![(1, BlockId(1))],
                        otherwise: BlockId(2),
                        span: span.clone(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        func: "core::panicking::unreachable_display::<&str>".to_string(),
                        args: vec![],
                        dest: Place::local(0),
                        target: None,
                        span: span.clone(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let vcs = generate_vcs(&func);
    let unreach_vc = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::Unreachable))
        .expect("unreachable_display should generate an Unreachable VC");

    assert!(
        matches!(
            &unreach_vc.formula,
            Formula::And(clauses)
                if clauses.iter().any(|clause| matches!(
                    clause,
                    Formula::Var(name, Sort::Bool) if name == "flag"
                ))
        ),
        "Unreachable VC should be guarded by the true branch reaching unreachable_display, got {:?}",
        unreach_vc.formula
    );
}

#[test]
fn test_cmp_binop_produces_no_arithmetic_vcs() {
    // #361: BinOp::Cmp (three-way comparison) is always safe — no VCs.
    let func = make_binop_func(BinOp::Cmp, Ty::i32());
    let vcs = generate_vcs(&func);
    let arith_vcs: Vec<_> = vcs
        .iter()
        .filter(|vc| {
            matches!(
                vc.kind,
                VcKind::ArithmeticOverflow { .. }
                    | VcKind::DivisionByZero
                    | VcKind::RemainderByZero
                    | VcKind::ShiftOverflow { .. }
                    | VcKind::NegationOverflow { .. }
            )
        })
        .collect();
    assert!(
        arith_vcs.is_empty(),
        "BinOp::Cmp should not generate any arithmetic VCs, got {}",
        arith_vcs.len()
    );
}

#[test]
fn test_integer_ops_produce_no_float_vcs() {
    // #361: Integer operations must NOT produce float VCs.
    for op in [BinOp::Add, BinOp::Sub, BinOp::Mul, BinOp::Div] {
        let func = make_binop_func(op, Ty::u32());
        let vcs = generate_vcs(&func);
        assert!(
            !vcs.iter().any(|vc| matches!(
                vc.kind,
                VcKind::FloatDivisionByZero | VcKind::FloatOverflowToInfinity { .. }
            )),
            "integer op {op:?} must not produce float VCs"
        );
    }
}

#[test]
fn test_operand_to_formula_unknown_const_does_not_panic() {
    // #361: Unknown ConstValue variants should produce a symbolic variable,
    // not panic. We test this by verifying the fallback path works for
    // known variants that previously used unreachable!.
    let func = midpoint_function();

    // All known variants should still work correctly
    assert_eq!(
        operand_to_formula(&func, &Operand::Constant(ConstValue::Bool(true))),
        Formula::Bool(true)
    );
    assert_eq!(
        operand_to_formula(&func, &Operand::Constant(ConstValue::Int(42))),
        Formula::Int(42)
    );
    assert_eq!(
        operand_to_formula(&func, &Operand::Constant(ConstValue::Uint(7, 32))),
        Formula::Int(7)
    );
    assert_eq!(operand_to_formula(&func, &Operand::Constant(ConstValue::Unit)), Formula::Int(0));
}

#[test]
fn test_float_ops_integer_isolation() {
    // tRust #953: Integer Div emits a DivisionByZero VC but never produces
    // a float-typed VC. This test guards the integer/float isolation.
    let func = make_binop_func(BinOp::Div, Ty::i32());
    let vcs = generate_vcs(&func);
    let float_vcs: Vec<_> = vcs
        .iter()
        .filter(|vc| {
            matches!(vc.kind, VcKind::FloatDivisionByZero | VcKind::FloatOverflowToInfinity { .. })
        })
        .collect();
    assert!(float_vcs.is_empty(), "integer Div must not produce float VCs, got {float_vcs:?}");
    assert!(
        vcs.iter().any(|vc| matches!(vc.kind, VcKind::DivisionByZero)),
        "integer Div(_, var) must emit DivisionByZero VC"
    );
}

// -----------------------------------------------------------------------
// tRust #609: Atomic ordering legality VCs in generate_vcs() pipeline
// -----------------------------------------------------------------------

/// Build a function with a Call terminator carrying an illegal atomic load
/// using Release ordering (violates L1: loads cannot release).
fn atomic_load_release_function() -> VerifiableFunction {
    VerifiableFunction {
        name: "atomic_load_release".to_string(),
        def_path: "test::atomic_load_release".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("target".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Call {
                    func: "core::intrinsics::atomic_load_release".to_string(),
                    args: vec![Operand::Copy(Place::local(1))],
                    dest: Place::local(0),
                    target: None,
                    span: SourceSpan::default(),
                    atomic: Some(AtomicOperation {
                        place: Place::local(1),
                        dest: Some(Place::local(0)),
                        op_kind: AtomicOpKind::Load,
                        ordering: AtomicOrdering::Release, // L1 violation
                        failure_ordering: None,
                        span: SourceSpan::default(),
                    }),
                },
            }],
            arg_count: 1,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn test_atomic_legality_load_release_generates_vc() {
    // #609: Load with Release ordering violates L1.
    let func = atomic_load_release_function();
    let vcs = generate_vcs(&func);

    let ordering_vcs: Vec<_> =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::InsufficientOrdering { .. })).collect();
    assert_eq!(
        ordering_vcs.len(),
        1,
        "load with Release ordering should produce exactly 1 InsufficientOrdering VC, got {}",
        ordering_vcs.len(),
    );
    assert_eq!(ordering_vcs[0].function, "atomic_load_release");
}

#[test]
fn test_atomic_legality_no_atomics_no_new_vcs() {
    // #609: Functions without atomic operations should produce no ordering VCs.
    let func = midpoint_function();
    let vcs = generate_vcs(&func);

    let ordering_vcs: Vec<_> =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::InsufficientOrdering { .. })).collect();
    assert!(
        ordering_vcs.is_empty(),
        "non-atomic function should produce no InsufficientOrdering VCs"
    );
}

#[test]
fn test_atomic_legality_legal_load_no_vc() {
    // #609: Load with Acquire ordering is legal — no InsufficientOrdering VC.
    let func = VerifiableFunction {
        name: "atomic_load_acquire".to_string(),
        def_path: "test::atomic_load_acquire".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("target".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Call {
                    func: "core::intrinsics::atomic_load_acquire".to_string(),
                    args: vec![Operand::Copy(Place::local(1))],
                    dest: Place::local(0),
                    target: None,
                    span: SourceSpan::default(),
                    atomic: Some(AtomicOperation {
                        place: Place::local(1),
                        dest: Some(Place::local(0)),
                        op_kind: AtomicOpKind::Load,
                        ordering: AtomicOrdering::Acquire, // legal
                        failure_ordering: None,
                        span: SourceSpan::default(),
                    }),
                },
            }],
            arg_count: 1,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let vcs = generate_vcs(&func);
    let ordering_vcs: Vec<_> =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::InsufficientOrdering { .. })).collect();
    assert!(ordering_vcs.is_empty(), "legal atomic load should produce no ordering VCs");
}

// -----------------------------------------------------------------------
// tRust #621: Assert-passed semantic guard propagation across blocks
// -----------------------------------------------------------------------

/// Build a 3-block safe midpoint: `lo + (hi - lo) / 2`
///
/// ```text
/// bb0: _3 = CheckedSub(hi, lo); Assert(!_3.1, overflow) -> bb1
/// bb1: _4 = _3.0; _5 = Div(_4, 2); goto bb2
/// bb2: _6 = CheckedAdd(lo, _5); Assert(!_6.1, overflow) -> bb3
/// bb3: return _6.0
/// ```
///
/// The Assert in bb0 passing means `hi >= lo` (unsigned no-overflow on sub).
/// The Assert in bb2 checking CheckedAdd(lo, _5) should benefit from the
/// semantic guard: knowing `hi >= lo` constrains `_5 = (hi - lo) / 2` and
/// makes the Add overflow impossible.
fn safe_midpoint_function() -> VerifiableFunction {
    VerifiableFunction {
        name: "safe_midpoint".to_string(),
        def_path: "test::safe_midpoint".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::usize(), name: None }, // _0: return
                LocalDecl { index: 1, ty: Ty::usize(), name: Some("lo".into()) }, // _1
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("hi".into()) }, // _2
                // _3: (usize, bool) from CheckedSub
                LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::usize(), Ty::Bool]), name: None },
                LocalDecl { index: 4, ty: Ty::usize(), name: None }, // _4: sub result
                LocalDecl { index: 5, ty: Ty::usize(), name: None }, // _5: _4 / 2
                // _6: (usize, bool) from CheckedAdd
                LocalDecl { index: 6, ty: Ty::Tuple(vec![Ty::usize(), Ty::Bool]), name: None },
                LocalDecl { index: 7, ty: Ty::usize(), name: None }, // _7: add result
            ],
            blocks: vec![
                // bb0: _3 = CheckedSub(hi, lo); assert(!_3.1) -> bb1
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::CheckedBinaryOp(
                            BinOp::Sub,
                            Operand::Copy(Place::local(2)), // hi
                            Operand::Copy(Place::local(1)), // lo
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::field(3, 1)),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Sub),
                        target: BlockId(1),
                        span: SourceSpan::default(),
                    },
                },
                // bb1: _4 = _3.0; _5 = _4 / 2; goto bb2
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
                    ],
                    terminator: Terminator::Goto(BlockId(2)),
                },
                // bb2: _6 = CheckedAdd(lo, _5); assert(!_6.1) -> bb3
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(6),
                        rvalue: Rvalue::CheckedBinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(1)), // lo
                            Operand::Copy(Place::local(5)), // (hi - lo) / 2
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::field(6, 1)),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Add),
                        target: BlockId(3),
                        span: SourceSpan::default(),
                    },
                },
                // bb3: _7 = _6.0; _0 = _7; return
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(7),
                            rvalue: Rvalue::Use(Operand::Copy(Place::field(6, 0))),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(7))),
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

/// Build a CFG with a join block whose successor must be reprocessed after
/// the join's path assumptions are weakened.
fn semantic_guard_join_reenqueue_function() -> VerifiableFunction {
    VerifiableFunction {
        name: "semantic_guard_join_reenqueue".to_string(),
        def_path: "test::semantic_guard_join_reenqueue".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None }, // _0: return
                LocalDecl { index: 1, ty: Ty::Bool, name: Some("flag".into()) }, // _1
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("x".into()) }, // _2
                LocalDecl { index: 3, ty: Ty::u32(), name: Some("y".into()) }, // _3
                LocalDecl { index: 4, ty: Ty::u32(), name: Some("tmp".into()) }, // _4
                LocalDecl { index: 5, ty: Ty::u32(), name: Some("joined".into()) }, // _5
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(1)),
                        targets: vec![(1, BlockId(1))],
                        otherwise: BlockId(2),
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(3))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![Statement::Assign {
                        place: Place::local(5),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(4))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(4)),
                },
                BasicBlock {
                    id: BlockId(4),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(5))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 3,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn test_safe_midpoint_sub_guard_propagates_to_add() {
    // tRust #953: `generate_vcs` emits ArithmeticOverflow VCs again.
    // `safe_midpoint_function` has two `CheckedBinaryOp` + `Assert(Overflow)`
    // pairs (a Sub in bb0 and an Add in bb2), so exactly two overflow VCs
    // are expected. The second VC's formula should incorporate the semantic
    // guard from bb0's passing Assert (i.e., `hi >= lo`) via
    // `build_semantic_guard_map`.
    let func = safe_midpoint_function();
    let vcs = generate_vcs(&func);

    let overflow_vcs: Vec<_> =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { .. })).collect();
    assert_eq!(
        overflow_vcs.len(),
        2,
        "safe_midpoint has two CheckedBinaryOp overflow pairs, got {}",
        overflow_vcs.len()
    );

    // The Add overflow VC (bb2) must contain the Sub's semantic guard —
    // specifically a `Le` formula from the `hi >= lo` range constraint.
    let add_overflow_formula = overflow_vcs
        .iter()
        .find_map(|vc| match &vc.kind {
            VcKind::ArithmeticOverflow { op: BinOp::Add, .. } => Some(&vc.formula),
            _ => None,
        })
        .expect("expected an Add overflow VC");
    assert!(
        contains_le_formula(add_overflow_formula),
        "Add overflow VC must carry the propagated Sub semantic guard (Le node), got {add_overflow_formula:?}"
    );
}

/// Recursively check if a formula contains a `Formula::Le` node.
fn contains_le_formula(f: &Formula) -> bool {
    match f {
        Formula::Le(_, _) => true,
        Formula::And(clauses) => clauses.iter().any(contains_le_formula),
        Formula::Or(clauses) => clauses.iter().any(contains_le_formula),
        Formula::Not(inner) => contains_le_formula(inner),
        Formula::Implies(lhs, rhs) => contains_le_formula(lhs) || contains_le_formula(rhs),
        _ => false,
    }
}

// tRust #792: build_semantic_guard_map is gated behind not(pipeline-v2).
#[cfg(not(feature = "pipeline-v2"))]
#[test]
fn test_safe_midpoint_semantic_guard_map_populated() {
    // #621: Verify build_semantic_guard_map finds the Sub's semantic guard
    // and propagates it to bb1 and bb2.
    let func = safe_midpoint_function();
    let guard_map = build_semantic_guard_map(&func);

    // bb0 has the CheckedSub + Assert pattern.
    // bb1 is the assert-passed target, so it should have the semantic guard.
    // bb2 is reached from bb1 via Goto, so the guard propagates there too.
    assert!(
        guard_map.contains_key(&BlockId(1)),
        "bb1 (assert-passed target) should have semantic guards"
    );
    assert!(
        guard_map.contains_key(&BlockId(2)),
        "bb2 (reachable from bb1) should have semantic guards from bb0's assert"
    );

    // bb1 gets 4 from bb0: range constraint, result definition (_3.0 = hi - lo),
    // lhs input range (hi in [0, max]), rhs input range (lo in [0, max])
    // bb2 gets 4 from bb0 + 2 dataflow defs from bb1 (_4 = _3.0, _5 = _4 / 2) = 6
    let bb1_guards = guard_map.get(&BlockId(1)).unwrap();
    let bb2_guards = guard_map.get(&BlockId(2)).unwrap();
    assert_eq!(bb1_guards.len(), 4, "bb1 should have 4 assumptions from bb0. Got: {bb1_guards:?}");
    assert_eq!(
        bb2_guards.len(),
        6,
        "bb2 should have 6 assumptions: bb0's 4 + bb1's 2 defs. Got: {bb2_guards:?}"
    );
}

#[cfg(not(feature = "pipeline-v2"))]
#[test]
fn test_safe_midpoint_sub_vc_has_no_semantic_guard() {
    // #621: The Sub overflow VC (in bb0) should NOT have semantic guards,
    // since it's the entry block and no prior asserts have passed.
    let func = safe_midpoint_function();
    let guard_map = build_semantic_guard_map(&func);

    // bb0 is the entry block — no semantic guards should be accumulated.
    assert!(!guard_map.contains_key(&BlockId(0)), "entry block bb0 should have no semantic guards");
}

#[cfg(not(feature = "pipeline-v2"))]
#[test]
fn test_semantic_guard_map_reenqueues_successors_after_join_weakening() {
    let func = semantic_guard_join_reenqueue_function();
    let guard_map = build_semantic_guard_map(&func);

    assert_eq!(
        guard_map.get(&BlockId(3)),
        Some(&vec![Formula::Bool(true)]),
        "join block should weaken to Bool(true) after seeing conflicting incoming defs"
    );

    assert_eq!(
        guard_map.get(&BlockId(4)),
        Some(&vec![Formula::Bool(true)]),
        "successor should be revisited and weakened instead of retaining the first path's stronger defs"
    );
}

#[test]
fn test_atomic_legality_fence_relaxed_generates_vc() {
    // #609: Fence with Relaxed ordering violates L5.
    let func = VerifiableFunction {
        name: "relaxed_fence".to_string(),
        def_path: "test::relaxed_fence".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Call {
                    func: "core::intrinsics::atomic_fence_relaxed".to_string(),
                    args: vec![],
                    dest: Place::local(0),
                    target: None,
                    span: SourceSpan::default(),
                    atomic: Some(AtomicOperation {
                        place: Place::local(0),
                        dest: None,
                        op_kind: AtomicOpKind::Fence,
                        ordering: AtomicOrdering::Relaxed, // L5 violation
                        failure_ordering: None,
                        span: SourceSpan::default(),
                    }),
                },
            }],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let vcs = generate_vcs(&func);
    let ordering_vcs: Vec<_> =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::InsufficientOrdering { .. })).collect();
    assert_eq!(
        ordering_vcs.len(),
        1,
        "fence with Relaxed ordering should produce exactly 1 InsufficientOrdering VC"
    );
}

// -----------------------------------------------------------------------
// Real MIR fixture tests (#941)
// -----------------------------------------------------------------------

#[test]
fn test_real_mir_generate_vcs_safe_divide() {
    // tRust #953: DivisionByZero VCs are emitted again. `safe_divide` divides
    // by a variable parameter, so `generate_vcs` must produce at least one
    // DivisionByZero VC.
    let func = load_fixture("test_functions__safe_divide");
    let vcs = generate_vcs(&func);
    assert!(
        vcs.iter().any(|vc| matches!(vc.kind, VcKind::DivisionByZero)),
        "safe_divide(var, var) must emit DivisionByZero VC"
    );
}

#[test]
fn test_real_mir_generate_vcs_checked_add() {
    // CheckedAdd should deserialize from a real MIR fixture and run through vcgen.
    let func = load_fixture("test_functions__checked_add");
    let vcs = generate_vcs(&func);
    let _ = vcs;
}

#[test]
fn test_real_mir_generate_vcs_sum_to_loop() {
    // tRust #953: sum_to exercises CheckedBinaryOp asserts. `generate_vcs`
    // must emit at least one ArithmeticOverflow VC for the loop body.
    let func = load_fixture("test_functions__sum_to");
    let vcs = generate_vcs(&func);
    assert!(
        vcs.iter().any(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { .. })),
        "sum_to loop must emit at least one ArithmeticOverflow VC"
    );
}

#[test]
fn test_real_mir_generate_vcs_increment() {
    // tRust #953: ArithmeticOverflow VCs are emitted again. `increment` has
    // at least one CheckedBinaryOp + Assert(Overflow) pair, so at least one
    // ArithmeticOverflow VC is expected.
    let func = load_fixture("test_functions__increment");
    let vcs = generate_vcs(&func);
    assert!(
        vcs.iter().any(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { .. })),
        "increment must emit at least one ArithmeticOverflow VC"
    );
}

#[test]
fn test_real_mir_generate_vcs_wrapping_mul() {
    let func = load_fixture("test_functions__wrapping_mul");
    let vcs = generate_vcs(&func);
    let _ = vcs;
}

#[test]
fn test_real_mir_generate_vcs_all_fixtures() {
    let dir = fixture_dir();
    let mut count = 0;
    for entry in std::fs::read_dir(&dir).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();
        if path.extension().map_or(true, |ext| ext != "json") {
            continue;
        }
        let json = std::fs::read_to_string(&path).unwrap();
        if let Ok(func) = serde_json::from_str::<VerifiableFunction>(&json) {
            let _vcs = generate_vcs(&func);
            count += 1;
        }
    }
    assert!(count >= 10, "expected at least 10 fixtures, found {count}");
}
