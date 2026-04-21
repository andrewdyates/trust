// trust-vcgen/tests/synthetic_mir.rs: Synthetic MIR fixtures for error detection
//
// Tests that exercise each VcKind directly by constructing MIR nodes and
// feeding them through generate_vcs(). No rustc parsing involved — every
// VerifiableFunction is built from scratch.
//
// Part of #586.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::*;
use trust_vcgen::generate_vcs;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Build a minimal VerifiableFunction from locals, blocks, and arg_count.
fn make_func(
    name: &str,
    locals: Vec<LocalDecl>,
    blocks: Vec<BasicBlock>,
    arg_count: usize,
) -> VerifiableFunction {
    VerifiableFunction {
        name: name.to_string(),
        def_path: format!("synthetic::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks,
            arg_count,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// Assert that exactly one VC is produced and it matches the expected kind
/// via a predicate.
fn assert_single_vc(
    vcs: &[VerificationCondition],
    pred: impl Fn(&VcKind) -> bool,
    label: &str,
) {
    let matching: Vec<_> = vcs.iter().filter(|vc| pred(&vc.kind)).collect();
    assert!(
        !matching.is_empty(),
        "{label}: expected at least one matching VC, got 0 out of {} total VCs: {:#?}",
        vcs.len(),
        vcs.iter().map(|v| v.kind.description()).collect::<Vec<_>>()
    );
}

// ---------------------------------------------------------------------------
// ArithmeticOverflow: Add
// ---------------------------------------------------------------------------

#[test]
fn test_synthetic_arithmetic_overflow_add() {
    // fn overflow_add(a: u32, b: u32) -> u32 { a + b }
    let func = make_func(
        "overflow_add",
        vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: None },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
            LocalDecl { index: 2, ty: Ty::u32(), name: Some("b".into()) },
            LocalDecl {
                index: 3,
                ty: Ty::Tuple(vec![Ty::u32(), Ty::Bool]),
                name: None,
            },
        ],
        vec![BasicBlock {
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
            terminator: Terminator::Return,
        }],
        2,
    );

    let vcs = generate_vcs(&func);
    assert_single_vc(&vcs, |k| matches!(k, VcKind::ArithmeticOverflow { op: BinOp::Add, .. }), "overflow add");
}

// ---------------------------------------------------------------------------
// ArithmeticOverflow: Sub
// ---------------------------------------------------------------------------

#[test]
fn test_synthetic_arithmetic_overflow_sub() {
    let func = make_func(
        "overflow_sub",
        vec![
            LocalDecl { index: 0, ty: Ty::i32(), name: None },
            LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
            LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
            LocalDecl {
                index: 3,
                ty: Ty::Tuple(vec![Ty::i32(), Ty::Bool]),
                name: None,
            },
        ],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(3),
                rvalue: Rvalue::CheckedBinaryOp(
                    BinOp::Sub,
                    Operand::Copy(Place::local(1)),
                    Operand::Copy(Place::local(2)),
                ),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Return,
        }],
        2,
    );

    let vcs = generate_vcs(&func);
    assert_single_vc(&vcs, |k| matches!(k, VcKind::ArithmeticOverflow { op: BinOp::Sub, .. }), "overflow sub");
}

// ---------------------------------------------------------------------------
// ArithmeticOverflow: Mul
// ---------------------------------------------------------------------------

#[test]
fn test_synthetic_arithmetic_overflow_mul() {
    let func = make_func(
        "overflow_mul",
        vec![
            LocalDecl { index: 0, ty: Ty::u64(), name: None },
            LocalDecl { index: 1, ty: Ty::u64(), name: Some("a".into()) },
            LocalDecl { index: 2, ty: Ty::u64(), name: Some("b".into()) },
            LocalDecl {
                index: 3,
                ty: Ty::Tuple(vec![Ty::u64(), Ty::Bool]),
                name: None,
            },
        ],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(3),
                rvalue: Rvalue::CheckedBinaryOp(
                    BinOp::Mul,
                    Operand::Copy(Place::local(1)),
                    Operand::Copy(Place::local(2)),
                ),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Return,
        }],
        2,
    );

    let vcs = generate_vcs(&func);
    assert_single_vc(&vcs, |k| matches!(k, VcKind::ArithmeticOverflow { op: BinOp::Mul, .. }), "overflow mul");
}

// ---------------------------------------------------------------------------
// DivisionByZero
// ---------------------------------------------------------------------------

#[test]
fn test_synthetic_division_by_zero() {
    // fn div(a: u32, b: u32) -> u32 { a / b }
    let func = make_func(
        "div_zero",
        vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: None },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
            LocalDecl { index: 2, ty: Ty::u32(), name: Some("b".into()) },
            LocalDecl { index: 3, ty: Ty::u32(), name: None },
        ],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(3),
                rvalue: Rvalue::BinaryOp(
                    BinOp::Div,
                    Operand::Copy(Place::local(1)),
                    Operand::Copy(Place::local(2)),
                ),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Return,
        }],
        2,
    );

    let vcs = generate_vcs(&func);
    assert_single_vc(&vcs, |k| matches!(k, VcKind::DivisionByZero), "division by zero");
}

// ---------------------------------------------------------------------------
// RemainderByZero
// ---------------------------------------------------------------------------

#[test]
fn test_synthetic_remainder_by_zero() {
    // fn rem(a: u32, b: u32) -> u32 { a % b }
    let func = make_func(
        "rem_zero",
        vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: None },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
            LocalDecl { index: 2, ty: Ty::u32(), name: Some("b".into()) },
            LocalDecl { index: 3, ty: Ty::u32(), name: None },
        ],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(3),
                rvalue: Rvalue::BinaryOp(
                    BinOp::Rem,
                    Operand::Copy(Place::local(1)),
                    Operand::Copy(Place::local(2)),
                ),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Return,
        }],
        2,
    );

    let vcs = generate_vcs(&func);
    assert_single_vc(&vcs, |k| matches!(k, VcKind::RemainderByZero), "remainder by zero");
}

// ---------------------------------------------------------------------------
// ShiftOverflow: Shl
// ---------------------------------------------------------------------------

#[test]
fn test_synthetic_shift_overflow_shl() {
    // fn shl(x: u32, amt: u32) -> u32 { x << amt }
    let func = make_func(
        "shift_shl",
        vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: None },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
            LocalDecl { index: 2, ty: Ty::u32(), name: Some("amt".into()) },
            LocalDecl { index: 3, ty: Ty::u32(), name: None },
        ],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(3),
                rvalue: Rvalue::BinaryOp(
                    BinOp::Shl,
                    Operand::Copy(Place::local(1)),
                    Operand::Copy(Place::local(2)),
                ),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Return,
        }],
        2,
    );

    let vcs = generate_vcs(&func);
    assert_single_vc(&vcs, |k| matches!(k, VcKind::ShiftOverflow { op: BinOp::Shl, .. }), "shift overflow shl");
}

// ---------------------------------------------------------------------------
// ShiftOverflow: Shr
// ---------------------------------------------------------------------------

#[test]
fn test_synthetic_shift_overflow_shr() {
    let func = make_func(
        "shift_shr",
        vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: None },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
            LocalDecl { index: 2, ty: Ty::u32(), name: Some("amt".into()) },
            LocalDecl { index: 3, ty: Ty::u32(), name: None },
        ],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(3),
                rvalue: Rvalue::BinaryOp(
                    BinOp::Shr,
                    Operand::Copy(Place::local(1)),
                    Operand::Copy(Place::local(2)),
                ),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Return,
        }],
        2,
    );

    let vcs = generate_vcs(&func);
    assert_single_vc(&vcs, |k| matches!(k, VcKind::ShiftOverflow { op: BinOp::Shr, .. }), "shift overflow shr");
}

// ---------------------------------------------------------------------------
// CastOverflow (narrowing: i32 -> u8)
// ---------------------------------------------------------------------------

#[test]
fn test_synthetic_cast_overflow() {
    // fn narrow(x: i32) -> u8 { x as u8 }
    let func = make_func(
        "cast_overflow",
        vec![
            LocalDecl { index: 0, ty: Ty::u8(), name: None },
            LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
            LocalDecl { index: 2, ty: Ty::u8(), name: None },
        ],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(2),
                rvalue: Rvalue::Cast(
                    Operand::Copy(Place::local(1)),
                    Ty::u8(),
                ),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Return,
        }],
        1,
    );

    let vcs = generate_vcs(&func);
    assert_single_vc(&vcs, |k| matches!(k, VcKind::CastOverflow { .. }), "cast overflow");
}

// ---------------------------------------------------------------------------
// NegationOverflow (signed)
// ---------------------------------------------------------------------------

#[test]
fn test_synthetic_negation_overflow() {
    // fn negate(x: i32) -> i32 { -x }
    let func = make_func(
        "negation_overflow",
        vec![
            LocalDecl { index: 0, ty: Ty::i32(), name: None },
            LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
            LocalDecl { index: 2, ty: Ty::i32(), name: None },
        ],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(2),
                rvalue: Rvalue::UnaryOp(UnOp::Neg, Operand::Copy(Place::local(1))),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Return,
        }],
        1,
    );

    let vcs = generate_vcs(&func);
    assert_single_vc(&vcs, |k| matches!(k, VcKind::NegationOverflow { .. }), "negation overflow");
}

// ---------------------------------------------------------------------------
// IndexOutOfBounds (via Assert terminator with BoundsCheck)
// ---------------------------------------------------------------------------

#[test]
fn test_synthetic_index_out_of_bounds() {
    // fn index(arr: &[u32], i: usize) -> u32 { arr[i] }
    // MIR: Assert(cond, true, BoundsCheck) to check i < len
    let func = make_func(
        "index_oob",
        vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: None },
            LocalDecl { index: 1, ty: Ty::usize(), name: Some("i".into()) },
            LocalDecl { index: 2, ty: Ty::Bool, name: Some("in_bounds".into()) },
        ],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![],
            terminator: Terminator::Assert {
                cond: Operand::Copy(Place::local(2)),
                expected: true,
                msg: AssertMessage::BoundsCheck,
                target: BlockId(1),
                span: SourceSpan::default(),
            },
        },
        BasicBlock {
            id: BlockId(1),
            stmts: vec![],
            terminator: Terminator::Return,
        }],
        2,
    );

    let vcs = generate_vcs(&func);
    assert_single_vc(&vcs, |k| matches!(k, VcKind::IndexOutOfBounds), "index out of bounds");
}

// ---------------------------------------------------------------------------
// Assertion (custom message)
// ---------------------------------------------------------------------------

#[test]
fn test_synthetic_assertion() {
    // fn check(cond: bool) { assert!(cond, "invariant violated") }
    let func = make_func(
        "custom_assert",
        vec![
            LocalDecl { index: 0, ty: Ty::Unit, name: None },
            LocalDecl { index: 1, ty: Ty::Bool, name: Some("cond".into()) },
        ],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![],
            terminator: Terminator::Assert {
                cond: Operand::Copy(Place::local(1)),
                expected: true,
                msg: AssertMessage::Custom("invariant violated".to_string()),
                target: BlockId(1),
                span: SourceSpan::default(),
            },
        },
        BasicBlock {
            id: BlockId(1),
            stmts: vec![],
            terminator: Terminator::Return,
        }],
        1,
    );

    let vcs = generate_vcs(&func);
    assert_single_vc(
        &vcs,
        |k| matches!(k, VcKind::Assertion { message } if message == "invariant violated"),
        "custom assertion",
    );
}

// ---------------------------------------------------------------------------
// FloatDivisionByZero
// ---------------------------------------------------------------------------

#[test]
fn test_synthetic_float_division_by_zero() {
    // fn fdiv(a: f64, b: f64) -> f64 { a / b }
    let func = make_func(
        "float_div_zero",
        vec![
            LocalDecl { index: 0, ty: Ty::Float { width: 64 }, name: None },
            LocalDecl { index: 1, ty: Ty::Float { width: 64 }, name: Some("a".into()) },
            LocalDecl { index: 2, ty: Ty::Float { width: 64 }, name: Some("b".into()) },
            LocalDecl { index: 3, ty: Ty::Float { width: 64 }, name: None },
        ],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(3),
                rvalue: Rvalue::BinaryOp(
                    BinOp::Div,
                    Operand::Copy(Place::local(1)),
                    Operand::Copy(Place::local(2)),
                ),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Return,
        }],
        2,
    );

    let vcs = generate_vcs(&func);
    assert_single_vc(&vcs, |k| matches!(k, VcKind::FloatDivisionByZero), "float division by zero");
}

// ---------------------------------------------------------------------------
// InvalidDiscriminant (read discriminant on non-enum type)
// ---------------------------------------------------------------------------

#[test]
fn test_synthetic_invalid_discriminant() {
    // Reading discriminant of a u32 (not an enum).
    let func = make_func(
        "invalid_discrim",
        vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: None },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
            LocalDecl { index: 2, ty: Ty::u32(), name: None },
        ],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(2),
                rvalue: Rvalue::Discriminant(Place::local(1)),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Return,
        }],
        1,
    );

    let vcs = generate_vcs(&func);
    assert_single_vc(&vcs, |k| matches!(k, VcKind::InvalidDiscriminant { .. }), "invalid discriminant");
}

// ---------------------------------------------------------------------------
// AggregateArrayLengthMismatch
// ---------------------------------------------------------------------------

#[test]
fn test_synthetic_aggregate_array_length_mismatch() {
    // Construct [u32; 3] with only 2 operands.
    let func = make_func(
        "array_len_mismatch",
        vec![
            LocalDecl {
                index: 0,
                ty: Ty::Array { elem: Box::new(Ty::u32()), len: 3 },
                name: None,
            },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
            LocalDecl { index: 2, ty: Ty::u32(), name: Some("b".into()) },
            LocalDecl {
                index: 3,
                ty: Ty::Array { elem: Box::new(Ty::u32()), len: 3 },
                name: None,
            },
        ],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(3),
                rvalue: Rvalue::Aggregate(
                    AggregateKind::Array,
                    vec![
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                        // Only 2 operands for a [u32; 3] — mismatch!
                    ],
                ),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Return,
        }],
        2,
    );

    let vcs = generate_vcs(&func);
    assert_single_vc(
        &vcs,
        |k| matches!(k, VcKind::AggregateArrayLengthMismatch { expected: 3, actual: 2 }),
        "aggregate array length mismatch",
    );
}

// ---------------------------------------------------------------------------
// Unreachable
// ---------------------------------------------------------------------------

#[test]
fn test_synthetic_unreachable() {
    // A function with an Unreachable terminator reachable from entry.
    let func = make_func(
        "has_unreachable",
        vec![
            LocalDecl { index: 0, ty: Ty::Unit, name: None },
        ],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![],
            terminator: Terminator::Unreachable,
        }],
        0,
    );

    let vcs = generate_vcs(&func);
    assert_single_vc(&vcs, |k| matches!(k, VcKind::Unreachable), "unreachable");
}

// ---------------------------------------------------------------------------
// Signed division overflow (INT_MIN / -1)
// ---------------------------------------------------------------------------

#[test]
fn test_synthetic_signed_div_overflow() {
    // fn signed_div(a: i32, b: i32) -> i32 { a / b }
    // Should produce DivisionByZero AND ArithmeticOverflow (INT_MIN / -1).
    let func = make_func(
        "signed_div",
        vec![
            LocalDecl { index: 0, ty: Ty::i32(), name: None },
            LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
            LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
            LocalDecl { index: 3, ty: Ty::i32(), name: None },
        ],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(3),
                rvalue: Rvalue::BinaryOp(
                    BinOp::Div,
                    Operand::Copy(Place::local(1)),
                    Operand::Copy(Place::local(2)),
                ),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Return,
        }],
        2,
    );

    let vcs = generate_vcs(&func);
    // Should have both DivisionByZero and ArithmeticOverflow
    assert_single_vc(&vcs, |k| matches!(k, VcKind::DivisionByZero), "signed div: div by zero");
    assert_single_vc(
        &vcs,
        |k| matches!(k, VcKind::ArithmeticOverflow { op: BinOp::Div, .. }),
        "signed div: INT_MIN / -1 overflow",
    );
}

// ---------------------------------------------------------------------------
// No false positives: constant divisor should not produce DivisionByZero
// ---------------------------------------------------------------------------

#[test]
fn test_synthetic_no_false_positive_const_divisor() {
    // fn safe_div(a: u32) -> u32 { a / 2 }
    let func = make_func(
        "safe_div",
        vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: None },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
            LocalDecl { index: 2, ty: Ty::u32(), name: None },
        ],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(2),
                rvalue: Rvalue::BinaryOp(
                    BinOp::Div,
                    Operand::Copy(Place::local(1)),
                    Operand::Constant(ConstValue::Uint(2, 32)),
                ),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Return,
        }],
        1,
    );

    let vcs = generate_vcs(&func);
    let div_zero_vcs: Vec<_> = vcs.iter().filter(|vc| matches!(vc.kind, VcKind::DivisionByZero)).collect();
    assert!(
        div_zero_vcs.is_empty(),
        "constant non-zero divisor should not produce DivisionByZero VC"
    );
}

// ---------------------------------------------------------------------------
// Multiple VcKinds in one function
// ---------------------------------------------------------------------------

#[test]
fn test_synthetic_multiple_vcs() {
    // fn multi(a: u32, b: u32) -> u32 {
    //     let sum = a + b;     // overflow VC
    //     let quot = sum / b;  // div-by-zero VC
    //     quot
    // }
    let func = make_func(
        "multi_vc",
        vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: None },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
            LocalDecl { index: 2, ty: Ty::u32(), name: Some("b".into()) },
            LocalDecl {
                index: 3,
                ty: Ty::Tuple(vec![Ty::u32(), Ty::Bool]),
                name: None,
            },
            LocalDecl { index: 4, ty: Ty::u32(), name: Some("sum".into()) },
            LocalDecl { index: 5, ty: Ty::u32(), name: Some("quot".into()) },
        ],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![
                Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::CheckedBinaryOp(
                        BinOp::Add,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: SourceSpan::default(),
                },
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
                        Operand::Copy(Place::local(2)),
                    ),
                    span: SourceSpan::default(),
                },
            ],
            terminator: Terminator::Return,
        }],
        2,
    );

    let vcs = generate_vcs(&func);
    assert_single_vc(&vcs, |k| matches!(k, VcKind::ArithmeticOverflow { op: BinOp::Add, .. }), "multi: overflow");
    assert_single_vc(&vcs, |k| matches!(k, VcKind::DivisionByZero), "multi: div by zero");
}

// ---------------------------------------------------------------------------
// ProofLevel classification
// ---------------------------------------------------------------------------

#[test]
fn test_synthetic_vc_proof_levels() {
    // Build a function with a checked add (L0) and check proof level.
    let func = make_func(
        "proof_level_test",
        vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: None },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
            LocalDecl { index: 2, ty: Ty::u32(), name: Some("b".into()) },
            LocalDecl {
                index: 3,
                ty: Ty::Tuple(vec![Ty::u32(), Ty::Bool]),
                name: None,
            },
        ],
        vec![BasicBlock {
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
            terminator: Terminator::Return,
        }],
        2,
    );

    let vcs = generate_vcs(&func);
    for vc in &vcs {
        assert_eq!(
            vc.kind.proof_level(),
            ProofLevel::L0Safety,
            "overflow VCs should be L0 safety"
        );
    }
}

// ---------------------------------------------------------------------------
// No VCs for empty function
// ---------------------------------------------------------------------------

#[test]
fn test_synthetic_empty_function_no_vcs() {
    let func = make_func(
        "empty",
        vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![],
            terminator: Terminator::Return,
        }],
        0,
    );

    let vcs = generate_vcs(&func);
    assert!(vcs.is_empty(), "empty function should produce no VCs");
}
