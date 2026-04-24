// trust-integration-tests/tests/vc_encoding_soundness.rs: Soundness tests for
// v2 fallback VC encoding in MirRouter (#942)
//
// Validates that `trust_router::build_v1_vcs` emits the expected VC kinds and
// divisor-zero formulas from hand-constructed MIR-shaped functions.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#![allow(rustc::default_hash_types, rustc::potential_query_instability)]

use trust_router::build_v1_vcs;
use trust_types::{
    AssertMessage, BasicBlock, BinOp, BlockId, ConstValue, Formula, LocalDecl, Operand, Place,
    Rvalue, Sort, SourceSpan, Statement, Terminator, Ty, VcKind, VerifiableBody,
    VerifiableFunction,
};

fn int_ty() -> Ty {
    Ty::Int { width: 32, signed: true }
}

fn local(index: usize, name: Option<&str>, ty: Ty) -> LocalDecl {
    LocalDecl { index, ty, name: name.map(str::to_string) }
}

fn place(local: usize) -> Place {
    Place { local, projections: vec![] }
}

fn copy(local: usize) -> Operand {
    Operand::Copy(place(local))
}

fn block(id: usize, stmts: Vec<Statement>, terminator: Terminator) -> BasicBlock {
    BasicBlock { id: BlockId(id), stmts, terminator }
}

fn make_function(
    name: &str,
    locals: Vec<LocalDecl>,
    blocks: Vec<BasicBlock>,
) -> VerifiableFunction {
    VerifiableFunction {
        name: name.to_string(),
        def_path: format!("test::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody { locals, blocks, arg_count: 0, return_ty: Ty::usize() },
        contracts: Vec::new(),
        preconditions: Vec::new(),
        postconditions: Vec::new(),
        spec: Default::default(),
    }
}

fn binary_stmt(op: BinOp, divisor: Operand) -> Statement {
    Statement::Assign {
        place: place(3),
        rvalue: Rvalue::BinaryOp(op, copy(1), divisor),
        span: SourceSpan::default(),
    }
}

fn arithmetic_locals(divisor_name: &str) -> Vec<LocalDecl> {
    vec![
        local(0, None, Ty::usize()),
        local(1, Some("a"), int_ty()),
        local(2, Some(divisor_name), int_ty()),
        local(3, None, int_ty()),
    ]
}

#[test]
fn test_div_by_zero_from_assert_terminator() {
    let func = make_function(
        "div_by_zero_assert",
        vec![local(0, None, Ty::usize())],
        vec![block(
            0,
            vec![],
            Terminator::Assert {
                cond: Operand::Constant(ConstValue::Bool(true)),
                expected: true,
                msg: AssertMessage::DivisionByZero,
                target: BlockId(0),
                span: SourceSpan::default(),
            },
        )],
    );

    let vcs = build_v1_vcs(&func);
    assert_eq!(vcs.len(), 1);
    assert!(matches!(vcs[0].kind, VcKind::DivisionByZero));
}

#[test]
fn test_div_by_zero_from_div_rvalue() {
    let func = make_function(
        "div_by_zero_rvalue",
        arithmetic_locals("b"),
        vec![block(
            0,
            vec![Statement::Assign {
                place: place(3),
                rvalue: Rvalue::BinaryOp(
                    BinOp::Div,
                    copy(1),
                    Operand::Copy(Place { local: 2, projections: vec![] }),
                ),
                span: SourceSpan::default(),
            }],
            Terminator::Return,
        )],
    );

    let vcs = build_v1_vcs(&func);
    assert_eq!(vcs.len(), 1);
    assert!(matches!(vcs[0].kind, VcKind::DivisionByZero));
    assert_eq!(
        vcs[0].formula,
        Formula::Eq(Box::new(Formula::Var("b".to_string(), Sort::Int)), Box::new(Formula::Int(0)),)
    );
}

#[test]
fn test_div_by_zero_constant_nonzero_divisor() {
    let func = make_function(
        "div_by_nonzero_const",
        arithmetic_locals("b"),
        vec![block(
            0,
            vec![binary_stmt(BinOp::Div, Operand::Constant(ConstValue::Int(5)))],
            Terminator::Return,
        )],
    );

    let vcs = build_v1_vcs(&func);
    assert_eq!(vcs.len(), 1);
    assert!(matches!(vcs[0].kind, VcKind::DivisionByZero));
    assert_eq!(vcs[0].formula, Formula::Bool(false));
}

#[test]
fn test_div_by_zero_constant_zero_divisor() {
    let func = make_function(
        "div_by_zero_const",
        arithmetic_locals("b"),
        vec![block(
            0,
            vec![binary_stmt(BinOp::Div, Operand::Constant(ConstValue::Int(0)))],
            Terminator::Return,
        )],
    );

    let vcs = build_v1_vcs(&func);
    assert_eq!(vcs.len(), 1);
    assert!(matches!(vcs[0].kind, VcKind::DivisionByZero));
    assert_eq!(vcs[0].formula, Formula::Bool(true));
}

#[test]
fn test_remainder_by_zero_vc() {
    let func = make_function(
        "remainder_by_zero_rvalue",
        arithmetic_locals("b"),
        vec![block(0, vec![binary_stmt(BinOp::Rem, copy(2))], Terminator::Return)],
    );

    let vcs = build_v1_vcs(&func);
    assert_eq!(vcs.len(), 1);
    assert!(matches!(vcs[0].kind, VcKind::RemainderByZero));
}

#[test]
fn test_overflow_assert_produces_overflow_vc() {
    let func = make_function(
        "overflow_assert",
        vec![local(0, None, Ty::usize())],
        vec![block(
            0,
            vec![],
            Terminator::Assert {
                cond: Operand::Constant(ConstValue::Bool(true)),
                expected: true,
                msg: AssertMessage::Overflow(BinOp::Add),
                target: BlockId(0),
                span: SourceSpan::default(),
            },
        )],
    );

    let vcs = build_v1_vcs(&func);
    assert_eq!(vcs.len(), 1);
    assert!(matches!(vcs[0].kind, VcKind::ArithmeticOverflow { op: BinOp::Add, .. }));
}

#[test]
fn test_bounds_check_assert_produces_index_vc() {
    let func = make_function(
        "bounds_check_assert",
        vec![local(0, None, Ty::usize())],
        vec![block(
            0,
            vec![],
            Terminator::Assert {
                cond: Operand::Constant(ConstValue::Bool(true)),
                expected: true,
                msg: AssertMessage::BoundsCheck,
                target: BlockId(0),
                span: SourceSpan::default(),
            },
        )],
    );

    let vcs = build_v1_vcs(&func);
    assert_eq!(vcs.len(), 1);
    assert!(matches!(vcs[0].kind, VcKind::IndexOutOfBounds));
}

#[test]
fn test_negation_overflow_assert() {
    let func = make_function(
        "overflow_neg_assert",
        vec![local(0, None, Ty::usize())],
        vec![block(
            0,
            vec![],
            Terminator::Assert {
                cond: Operand::Constant(ConstValue::Bool(true)),
                expected: true,
                msg: AssertMessage::OverflowNeg,
                target: BlockId(0),
                span: SourceSpan::default(),
            },
        )],
    );

    let vcs = build_v1_vcs(&func);
    assert_eq!(vcs.len(), 1);
    assert!(matches!(
        vcs[0].kind,
        VcKind::NegationOverflow { ty: Ty::Int { width: 32, signed: true } }
    ));
}

#[test]
fn test_guard_deduplication_skips_guarded_blocks() {
    let func = make_function(
        "guarded_division",
        arithmetic_locals("b"),
        vec![
            block(
                0,
                vec![],
                Terminator::Assert {
                    cond: Operand::Constant(ConstValue::Bool(true)),
                    expected: true,
                    msg: AssertMessage::DivisionByZero,
                    target: BlockId(1),
                    span: SourceSpan::default(),
                },
            ),
            block(1, vec![binary_stmt(BinOp::Div, copy(2))], Terminator::Return),
        ],
    );

    let vcs = build_v1_vcs(&func);
    assert_eq!(vcs.len(), 1);
    assert!(matches!(vcs[0].kind, VcKind::DivisionByZero));
    assert_eq!(vcs[0].formula, Formula::Bool(false));
}

#[test]
fn test_symbolic_operand_formula() {
    let func = make_function(
        "symbolic_divisor",
        arithmetic_locals("b"),
        vec![block(
            0,
            vec![binary_stmt(BinOp::Div, Operand::Symbolic(Formula::Var("x".into(), Sort::Int)))],
            Terminator::Return,
        )],
    );

    let vcs = build_v1_vcs(&func);
    assert_eq!(vcs.len(), 1);
    assert!(matches!(vcs[0].kind, VcKind::DivisionByZero));
    assert_eq!(
        vcs[0].formula,
        Formula::Eq(Box::new(Formula::Var("x".to_string(), Sort::Int)), Box::new(Formula::Int(0)),)
    );
}
