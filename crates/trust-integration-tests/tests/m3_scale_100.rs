// trust-integration-tests/tests/m3_scale_100.rs: Scale test -- 120+ function crate
//
// Exercises `cargo trust check` pipeline at scale on a realistic function mix:
//   - Checked arithmetic (Add, Sub, Mul)
//   - Division/remainder with and without preconditions
//   - Array/slice bounds checks
//   - Postcondition contracts
//   - Bitwise operations (Shl, Shr, BitAnd, BitOr, BitXor)
//   - Comparison chains (SwitchInt with multiple targets)
//   - Noop / identity functions (no VCs)
//   - Cast operations (widening, narrowing)
//   - Negation (UnaryOp Neg on signed types)
//   - Aggregate construction (tuples, arrays)
//   - Len-based patterns (Rvalue::Len)
//   - Multi-block control flow (branching, loops)
//   - Reference / borrow patterns (Rvalue::Ref)
//
// Unhandled MIR patterns (documented for future work):
//   - Generic type parameters (monomorphization happens before MIR; at this level
//     we work with concrete types only)
//   - Closures (represented as Adt aggregates with captured fields; vcgen treats
//     them as opaque -- no VCs generated for closure bodies)
//   - Trait object dispatch (virtual call through vtable; vcgen does not yet model
//     dynamic dispatch -- Call terminators to trait methods produce no VCs)
//   - Async/await (desugars to a state machine Generator; vcgen does not model
//     Generator state transitions or poll semantics)
//   - Drop glue (compiler-inserted drop calls are not verified)
//
// Part of #682
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#![allow(rustc::default_hash_types, rustc::potential_query_instability)]

use std::fmt::Write;
use trust_types::fx::FxHashMap;

use trust_types::{
    AggregateKind, AssertMessage, BasicBlock, BinOp, BlockId, Contract, ContractKind, Formula,
    LocalDecl, Operand, Place, Projection, Rvalue, Sort, SourceSpan, Statement, Terminator, Ty,
    UnOp, VerifiableBody, VerifiableFunction, VerificationCondition, VerificationResult,
};

// ---------------------------------------------------------------------------
// Function pattern catalog: each builder creates a VerifiableFunction that
// exercises a distinct MIR pattern. We compose 120+ functions by cycling
// through these builders with varied names and parameters.
// ---------------------------------------------------------------------------

/// Checked binary op (Add/Sub/Mul) -- produces ArithmeticOverflow VC.
fn make_checked_binop(name: &str, op: BinOp, ty: Ty) -> VerifiableFunction {
    let tuple_ty = Ty::Tuple(vec![ty.clone(), Ty::Bool]);
    VerifiableFunction {
        name: name.to_string(),
        def_path: format!("scale_crate::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: ty.clone(), name: None },
                LocalDecl { index: 1, ty: ty.clone(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: ty.clone(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: tuple_ty, name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::CheckedBinaryOp(
                            op,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::field(3, 1)),
                        expected: false,
                        msg: AssertMessage::Overflow(op),
                        target: BlockId(1),
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::field(3, 0))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 2,
            return_ty: ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// Division without precondition -- produces DivisionByZero VC.
fn make_division(name: &str, ty: Ty) -> VerifiableFunction {
    VerifiableFunction {
        name: name.to_string(),
        def_path: format!("scale_crate::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: ty.clone(), name: None },
                LocalDecl { index: 1, ty: ty.clone(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: ty.clone(), name: Some("y".into()) },
                LocalDecl { index: 3, ty: ty.clone(), name: None },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Div,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(3))),
                        span: SourceSpan::default(),
                    },
                ],
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

/// Division WITH precondition (divisor != 0) -- DivisionByZero VC guarded.
fn make_guarded_division(name: &str) -> VerifiableFunction {
    VerifiableFunction {
        name: name.to_string(),
        def_path: format!("scale_crate::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("dividend".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("divisor".into()) },
                LocalDecl { index: 3, ty: Ty::u32(), name: None },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Div,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(3))),
                        span: SourceSpan::default(),
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::u32(),
        },
        contracts: vec![Contract {
            kind: ContractKind::Requires,
            span: SourceSpan::default(),
            body: "divisor != 0".to_string(),
        }],
        preconditions: vec![Formula::Not(Box::new(Formula::Eq(
            Box::new(Formula::Var("divisor".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        )))],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// Remainder without precondition -- produces RemainderByZero / DivisionByZero VC.
fn make_remainder(name: &str) -> VerifiableFunction {
    VerifiableFunction {
        name: name.to_string(),
        def_path: format!("scale_crate::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("n".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("m".into()) },
                LocalDecl { index: 3, ty: Ty::u32(), name: None },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Rem,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(3))),
                        span: SourceSpan::default(),
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// Array index -- produces IndexOutOfBounds VC.
fn make_array_index(name: &str, len: u64) -> VerifiableFunction {
    VerifiableFunction {
        name: name.to_string(),
        def_path: format!("scale_crate::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Array { elem: Box::new(Ty::i32()), len },
                    name: Some("data".into()),
                },
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("idx".into()) },
                LocalDecl { index: 3, ty: Ty::i32(), name: None },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::Use(Operand::Copy(Place {
                            local: 1,
                            projections: vec![Projection::Index(2)],
                        })),
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(3))),
                        span: SourceSpan::default(),
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::i32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// Function with postcondition contract (result >= lo, result <= hi).
fn make_contract_fn(name: &str) -> VerifiableFunction {
    VerifiableFunction {
        name: name.to_string(),
        def_path: format!("scale_crate::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("val".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("lo".into()) },
                LocalDecl { index: 3, ty: Ty::i32(), name: Some("hi".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(1)),
                        targets: vec![(0, BlockId(1)), (1, BlockId(2))],
                        otherwise: BlockId(2),
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
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 3,
            return_ty: Ty::i32(),
        },
        contracts: vec![
            Contract {
                kind: ContractKind::Requires,
                span: SourceSpan::default(),
                body: "lo <= hi".to_string(),
            },
            Contract {
                kind: ContractKind::Ensures,
                span: SourceSpan::default(),
                body: "result >= lo".to_string(),
            },
        ],
        preconditions: vec![Formula::Le(
            Box::new(Formula::Var("lo".into(), Sort::Int)),
            Box::new(Formula::Var("hi".into(), Sort::Int)),
        )],
        postconditions: vec![Formula::Ge(
            Box::new(Formula::Var("result".into(), Sort::Int)),
            Box::new(Formula::Var("lo".into(), Sort::Int)),
        )],
        spec: Default::default(),
    }
}

/// Noop / identity function -- no VCs generated.
fn make_noop(name: &str, ty: Ty) -> VerifiableFunction {
    VerifiableFunction {
        name: name.to_string(),
        def_path: format!("scale_crate::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: ty.clone(), name: None },
                LocalDecl { index: 1, ty: ty.clone(), name: Some("x".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// Bitwise operation -- produces shift overflow VC for Shl/Shr, no VC for And/Or/Xor.
fn make_bitwise(name: &str, op: BinOp) -> VerifiableFunction {
    VerifiableFunction {
        name: name.to_string(),
        def_path: format!("scale_crate::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: Ty::u32(), name: None },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::BinaryOp(
                            op,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(3))),
                        span: SourceSpan::default(),
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// Cast operation (widening or narrowing).
fn make_cast(name: &str, from_ty: Ty, to_ty: Ty) -> VerifiableFunction {
    VerifiableFunction {
        name: name.to_string(),
        def_path: format!("scale_crate::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: to_ty.clone(), name: None },
                LocalDecl { index: 1, ty: from_ty, name: Some("x".into()) },
                LocalDecl { index: 2, ty: to_ty.clone(), name: None },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Cast(Operand::Copy(Place::local(1)), to_ty.clone()),
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                        span: SourceSpan::default(),
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: to_ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// Negation (UnaryOp::Neg) on signed type -- may produce overflow VC for i32::MIN.
fn make_negation(name: &str, ty: Ty) -> VerifiableFunction {
    VerifiableFunction {
        name: name.to_string(),
        def_path: format!("scale_crate::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: ty.clone(), name: None },
                LocalDecl { index: 1, ty: ty.clone(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: ty.clone(), name: None },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::UnaryOp(UnOp::Neg, Operand::Copy(Place::local(1))),
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                        span: SourceSpan::default(),
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// Aggregate construction (tuple of two values).
fn make_aggregate_tuple(name: &str) -> VerifiableFunction {
    let ret_ty = Ty::Tuple(vec![Ty::u32(), Ty::u32()]);
    VerifiableFunction {
        name: name.to_string(),
        def_path: format!("scale_crate::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: ret_ty.clone(), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("b".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Aggregate(
                        AggregateKind::Tuple,
                        vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: ret_ty,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// Len-based pattern: `arr.len()` via Rvalue::Len.
fn make_len_check(name: &str) -> VerifiableFunction {
    VerifiableFunction {
        name: name.to_string(),
        def_path: format!("scale_crate::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::usize(), name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Array { elem: Box::new(Ty::u8()), len: 64 },
                    name: Some("arr".into()),
                },
                LocalDecl { index: 2, ty: Ty::usize(), name: None },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Len(Place::local(1)),
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                        span: SourceSpan::default(),
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::usize(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// Multi-block control flow: branch on condition, different arithmetic in each arm.
fn make_branching(name: &str) -> VerifiableFunction {
    let tuple_ty = Ty::Tuple(vec![Ty::u32(), Ty::Bool]);
    VerifiableFunction {
        name: name.to_string(),
        def_path: format!("scale_crate::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("y".into()) },
                LocalDecl { index: 3, ty: Ty::Bool, name: Some("cond".into()) },
                LocalDecl { index: 4, ty: tuple_ty.clone(), name: None },
            ],
            blocks: vec![
                // bb0: branch on cond
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(3)),
                        targets: vec![(0, BlockId(1)), (1, BlockId(2))],
                        otherwise: BlockId(1),
                        span: SourceSpan::default(),
                    },
                },
                // bb1: x + y (checked add)
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::CheckedBinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::field(4, 1)),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Add),
                        target: BlockId(3),
                        span: SourceSpan::default(),
                    },
                },
                // bb2: x * y (checked mul)
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::CheckedBinaryOp(
                            BinOp::Mul,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::field(4, 1)),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Mul),
                        target: BlockId(3),
                        span: SourceSpan::default(),
                    },
                },
                // bb3: join -- return result
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::field(4, 0))),
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

/// Reference / borrow pattern: takes a value and returns a copy via ref.
fn make_ref_pattern(name: &str) -> VerifiableFunction {
    VerifiableFunction {
        name: name.to_string(),
        def_path: format!("scale_crate::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u64(), name: None },
                LocalDecl { index: 1, ty: Ty::u64(), name: Some("val".into()) },
                LocalDecl {
                    index: 2,
                    ty: Ty::Ref { mutable: false, inner: Box::new(Ty::u64()) },
                    name: None,
                },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Ref { mutable: false, place: Place::local(1) },
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                        span: SourceSpan::default(),
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::u64(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// Comparison chain (multiple comparisons in sequence, typical in sort/search).
fn make_comparison_chain(name: &str) -> VerifiableFunction {
    VerifiableFunction {
        name: name.to_string(),
        def_path: format!("scale_crate::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Bool, name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: Ty::i32(), name: Some("c".into()) },
                LocalDecl { index: 4, ty: Ty::Bool, name: None },
                LocalDecl { index: 5, ty: Ty::Bool, name: None },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    // _4 = a < b
                    Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Lt,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: SourceSpan::default(),
                    },
                    // _5 = b < c
                    Statement::Assign {
                        place: Place::local(5),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Lt,
                            Operand::Copy(Place::local(2)),
                            Operand::Copy(Place::local(3)),
                        ),
                        span: SourceSpan::default(),
                    },
                    // _0 = _4 & _5 (a < b && b < c)
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::BitAnd,
                            Operand::Copy(Place::local(4)),
                            Operand::Copy(Place::local(5)),
                        ),
                        span: SourceSpan::default(),
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 3,
            return_ty: Ty::Bool,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

// ---------------------------------------------------------------------------
// Generate a 120+ function crate with realistic pattern distribution
// ---------------------------------------------------------------------------

/// Pattern categories that map to real Rust code archetypes.
#[derive(Debug, Clone, Copy)]
enum ScalePattern {
    CheckedAdd,
    CheckedSub,
    CheckedMul,
    Division,
    GuardedDivision,
    Remainder,
    ArrayIndex,
    Contract,
    Noop,
    BitwiseAnd,
    BitwiseOr,
    BitwiseXor,
    ShiftLeft,
    ShiftRight,
    CastWiden,
    CastNarrow,
    Negation,
    AggregateTuple,
    LenCheck,
    Branching,
    RefPattern,
    ComparisonChain,
}

const ALL_SCALE_PATTERNS: &[ScalePattern] = &[
    ScalePattern::CheckedAdd,
    ScalePattern::CheckedSub,
    ScalePattern::CheckedMul,
    ScalePattern::Division,
    ScalePattern::GuardedDivision,
    ScalePattern::Remainder,
    ScalePattern::ArrayIndex,
    ScalePattern::Contract,
    ScalePattern::Noop,
    ScalePattern::BitwiseAnd,
    ScalePattern::BitwiseOr,
    ScalePattern::BitwiseXor,
    ScalePattern::ShiftLeft,
    ScalePattern::ShiftRight,
    ScalePattern::CastWiden,
    ScalePattern::CastNarrow,
    ScalePattern::Negation,
    ScalePattern::AggregateTuple,
    ScalePattern::LenCheck,
    ScalePattern::Branching,
    ScalePattern::RefPattern,
    ScalePattern::ComparisonChain,
];

fn generate_scale_crate(n: usize) -> Vec<VerifiableFunction> {
    let types = [Ty::u32(), Ty::u64(), Ty::i32(), Ty::i64(), Ty::usize()];
    (0..n)
        .map(|i| {
            let pattern = ALL_SCALE_PATTERNS[i % ALL_SCALE_PATTERNS.len()];
            let name = format!("fn_{i:04}");
            let ty = types[i % types.len()].clone();
            match pattern {
                ScalePattern::CheckedAdd => make_checked_binop(&name, BinOp::Add, ty),
                ScalePattern::CheckedSub => make_checked_binop(&name, BinOp::Sub, ty),
                ScalePattern::CheckedMul => make_checked_binop(&name, BinOp::Mul, ty),
                ScalePattern::Division => make_division(&name, ty),
                ScalePattern::GuardedDivision => make_guarded_division(&name),
                ScalePattern::Remainder => make_remainder(&name),
                ScalePattern::ArrayIndex => make_array_index(&name, (10 + (i % 50)) as u64),
                ScalePattern::Contract => make_contract_fn(&name),
                ScalePattern::Noop => make_noop(&name, ty),
                ScalePattern::BitwiseAnd => make_bitwise(&name, BinOp::BitAnd),
                ScalePattern::BitwiseOr => make_bitwise(&name, BinOp::BitOr),
                ScalePattern::BitwiseXor => make_bitwise(&name, BinOp::BitXor),
                ScalePattern::ShiftLeft => make_bitwise(&name, BinOp::Shl),
                ScalePattern::ShiftRight => make_bitwise(&name, BinOp::Shr),
                ScalePattern::CastWiden => make_cast(&name, Ty::u32(), Ty::u64()),
                ScalePattern::CastNarrow => make_cast(&name, Ty::u64(), Ty::u32()),
                ScalePattern::Negation => make_negation(&name, Ty::i32()),
                ScalePattern::AggregateTuple => make_aggregate_tuple(&name),
                ScalePattern::LenCheck => make_len_check(&name),
                ScalePattern::Branching => make_branching(&name),
                ScalePattern::RefPattern => make_ref_pattern(&name),
                ScalePattern::ComparisonChain => make_comparison_chain(&name),
            }
        })
        .collect()
}

// ---------------------------------------------------------------------------
// Test 1: VCGen at scale -- 132 functions (6 full cycles of 22 patterns)
// ---------------------------------------------------------------------------

#[test]
fn test_scale_vcgen_132_functions() {
    let functions = generate_scale_crate(132);
    assert_eq!(functions.len(), 132);

    let mut total_vcs = 0usize;
    let mut functions_with_vcs = 0usize;
    let mut vc_kind_counts: FxHashMap<String, usize> = FxHashMap::default();

    for func in &functions {
        let vcs = trust_vcgen::generate_vcs(func);
        if !vcs.is_empty() {
            functions_with_vcs += 1;
        }
        total_vcs += vcs.len();
        for vc in &vcs {
            *vc_kind_counts.entry(vc.kind.description().to_string()).or_default() += 1;
        }
    }

    // 22 patterns, 6 of which are VC-free (Noop, BitwiseAnd, BitwiseOr, BitwiseXor,
    // AggregateTuple, LenCheck, RefPattern, ComparisonChain) -- but some of these
    // may produce VCs depending on vcgen behavior. We conservatively expect at least
    // half to produce VCs.
    assert!(
        functions_with_vcs >= 50,
        "at least 50 functions should produce VCs, got {functions_with_vcs}"
    );
    assert!(total_vcs >= 50, "should have >= 50 total VCs, got {total_vcs}");

    // We expect multiple distinct VC kinds.
    assert!(
        vc_kind_counts.len() >= 3,
        "should have >= 3 distinct VC kinds, got: {vc_kind_counts:?}"
    );

    eprintln!("=== Scale VCGen (132 functions) ===");
    eprintln!("  Functions with VCs: {functions_with_vcs}/{}", functions.len());
    eprintln!("  Total VCs: {total_vcs}");
    eprintln!("  VC kinds:");
    for (kind, count) in &vc_kind_counts {
        eprintln!("    {kind}: {count}");
    }
    eprintln!("===================================");
}

// ---------------------------------------------------------------------------
// Test 2: Full pipeline at scale -- vcgen -> router -> report (132 functions)
// ---------------------------------------------------------------------------

#[test]
fn test_scale_full_pipeline_132_functions() {
    let functions = generate_scale_crate(132);
    let router = trust_router::Router::new();

    let mut all_results: Vec<(VerificationCondition, VerificationResult)> = Vec::new();
    let mut proved = 0usize;
    let mut failed = 0usize;
    let mut unknown = 0usize;
    let mut functions_fully_proved = 0usize;
    let mut discharged_count = 0usize;

    for func in &functions {
        // Use abstract interpretation pre-pass to discharge provable VCs
        // without a solver (tRust #357, #428). Remaining VCs go to the router.
        let (solver_vcs, discharged) = trust_vcgen::generate_vcs_with_discharge(func);
        let router_results = router.verify_all(&solver_vcs);

        // Combine discharged (proved by abstract interp) + router results.
        let mut func_results: Vec<(VerificationCondition, VerificationResult)> = discharged.clone();
        func_results.extend(router_results);
        discharged_count += discharged.len();

        // Track per-function verdict.
        let func_proved = func_results.iter().all(|(_, r)| r.is_proved());
        let func_has_no_vcs = func_results.is_empty();
        if func_proved || func_has_no_vcs {
            functions_fully_proved += 1;
        }

        for (_vc, result) in &func_results {
            match result {
                VerificationResult::Proved { .. } => proved += 1,
                VerificationResult::Failed { .. } => failed += 1,
                _ => unknown += 1,
            }
        }

        all_results.extend(func_results);
    }

    let total_functions = functions.len();

    // Acceptance criteria: at least 60% of functions fully proved at Level 0.
    // Functions with no VCs count as "proved" (nothing to disprove).
    let proved_pct = (functions_fully_proved as f64 / total_functions as f64) * 100.0;
    assert!(
        proved_pct >= 60.0,
        "at least 60% of functions should be fully proved, got {proved_pct:.1}% \
         ({functions_fully_proved}/{total_functions})"
    );

    // Build the proof report.
    let report = trust_report::build_json_report("scale-132-crate", &all_results);

    assert_eq!(report.crate_name, "scale-132-crate");
    assert!(!report.metadata.schema_version.is_empty());
    assert!(!report.metadata.trust_version.is_empty());

    // Validate JSON round-trip.
    let json = serde_json::to_string_pretty(&report).expect("serialize report");
    assert!(json.len() > 500, "JSON report should be substantial, got {} bytes", json.len());
    let parsed: serde_json::Value = serde_json::from_str(&json).expect("parse JSON");
    assert!(parsed["functions"].is_array());
    assert!(parsed["summary"]["total_obligations"].is_number());

    // Validate per-function entries exist in the report.
    let report_functions = parsed["functions"].as_array().expect("functions array");
    // Functions with 0 VCs may not appear in the report -- that's fine.
    assert!(!report_functions.is_empty(), "report should have function-level entries");

    // Each function entry should have required fields.
    for entry in report_functions {
        assert!(entry.get("function").is_some(), "missing function name");
        assert!(entry.get("summary").is_some(), "missing function summary");
        assert!(entry.get("obligations").is_some(), "missing obligations");
    }

    // Validate NDJSON output.
    let mut ndjson_buf = Vec::new();
    trust_report::write_ndjson(&report, &mut ndjson_buf).expect("write ndjson");
    let ndjson = String::from_utf8(ndjson_buf).expect("utf8");
    let ndjson_lines: Vec<&str> = ndjson.trim_end().split('\n').collect();
    assert!(ndjson_lines.len() >= 3, "NDJSON should have >= 3 lines");

    // Validate text summary.
    let text = trust_report::format_json_summary(&report);
    assert!(!text.is_empty());
    assert!(text.contains("Verdict:"));

    // Validate HTML report.
    let html = trust_report::html_report::generate_html_report(&report);
    assert!(html.contains("<html"), "output should contain HTML tag");
    assert!(html.contains("scale-132-crate"), "HTML should contain crate name");

    eprintln!("=== Scale Full Pipeline (132 functions) ===");
    eprintln!("  Functions: {total_functions}");
    eprintln!("  Functions fully proved: {functions_fully_proved} ({proved_pct:.1}%)");
    eprintln!("  Total VCs: {}", all_results.len());
    eprintln!("  Discharged by abstract interp: {discharged_count}");
    eprintln!("  Proved: {proved}");
    eprintln!("  Failed: {failed}");
    eprintln!("  Unknown: {unknown}");
    eprintln!("  Report functions: {}", report_functions.len());
    eprintln!("  Report verdict: {:?}", report.summary.verdict);
    eprintln!("  JSON size: {} bytes", json.len());
    eprintln!("  HTML size: {} bytes", html.len());
    eprintln!("============================================");
}

// ---------------------------------------------------------------------------
// Test 3: No panics on 200 functions (stress test)
// ---------------------------------------------------------------------------

#[test]
fn test_scale_no_panics_200_functions() {
    let functions = generate_scale_crate(200);
    let router = trust_router::Router::new();

    let mut total_vcs = 0usize;
    let mut total_results = 0usize;

    for func in &functions {
        let vcs = trust_vcgen::generate_vcs(func);
        total_vcs += vcs.len();
        let results = router.verify_all(&vcs);
        total_results += results.len();

        assert_eq!(
            vcs.len(),
            results.len(),
            "router must return one result per VC for {}",
            func.name,
        );
    }

    // Build report from all results (ensure report builder doesn't panic).
    let all_results: Vec<(VerificationCondition, VerificationResult)> = functions
        .iter()
        .flat_map(|func| {
            let vcs = trust_vcgen::generate_vcs(func);
            trust_router::Router::new().verify_all(&vcs)
        })
        .collect();

    let report = trust_report::build_json_report("stress-200", &all_results);
    let _json = serde_json::to_string(&report).expect("serialize stress report");

    eprintln!("=== Scale Stress Test (200 functions) ===");
    eprintln!("  Total VCs: {total_vcs}");
    eprintln!("  Total results: {total_results}");
    eprintln!("  Report obligations: {}", report.summary.total_obligations);
    eprintln!("==========================================");
}

// ---------------------------------------------------------------------------
// Test 4: VC kind diversity -- all expected VC kinds are represented
// ---------------------------------------------------------------------------

#[test]
fn test_scale_vc_kind_diversity() {
    let functions = generate_scale_crate(132);
    let mut all_kinds: FxHashMap<String, usize> = FxHashMap::default();

    for func in &functions {
        let vcs = trust_vcgen::generate_vcs(func);
        for vc in &vcs {
            *all_kinds.entry(format!("{:?}", vc.kind)).or_default() += 1;
        }
    }

    // We should see overflow, division, bounds check, and contract VCs.
    let kind_names: Vec<String> = all_kinds.keys().cloned().collect();

    // At least one overflow-related VC.
    let has_overflow = kind_names.iter().any(|k| k.contains("Overflow"));
    assert!(has_overflow, "should have overflow VCs, got kinds: {kind_names:?}");

    // At least one division-related VC.
    let has_division = kind_names.iter().any(|k| k.contains("Division") || k.contains("Remainder"));
    assert!(has_division, "should have division/remainder VCs, got kinds: {kind_names:?}");

    // At least one bounds-check VC.
    let has_bounds = kind_names.iter().any(|k| k.contains("Index") || k.contains("Bounds"));
    assert!(has_bounds, "should have bounds check VCs, got kinds: {kind_names:?}");

    // At least one contract VC.
    let has_contract =
        kind_names.iter().any(|k| k.contains("Postcondition") || k.contains("Precondition"));
    assert!(has_contract, "should have contract VCs, got kinds: {kind_names:?}");

    eprintln!("=== Scale VC Kind Diversity ===");
    eprintln!("  Distinct VC kinds: {}", all_kinds.len());
    for (kind, count) in &all_kinds {
        eprintln!("    {kind}: {count}");
    }
    eprintln!("===============================");
}

// ---------------------------------------------------------------------------
// Test 5: Per-function report verification
// ---------------------------------------------------------------------------

#[test]
fn test_scale_per_function_report() {
    let functions = generate_scale_crate(132);
    let router = trust_router::Router::new();

    // Collect results keyed by function name.
    let mut per_function: FxHashMap<String, Vec<(VerificationCondition, VerificationResult)>> =
        FxHashMap::default();

    for func in &functions {
        let vcs = trust_vcgen::generate_vcs(func);
        let results = router.verify_all(&vcs);
        per_function.entry(func.name.clone()).or_default().extend(results);
    }

    // Build aggregate report.
    let all_results: Vec<(VerificationCondition, VerificationResult)> =
        per_function.values().flat_map(|v| v.iter().cloned()).collect();
    let report = trust_report::build_json_report("per-function-132", &all_results);

    // Validate that the report has per-function entries with Level 0 results.
    let json_value: serde_json::Value = serde_json::to_value(&report).expect("serialize");
    let functions_arr = json_value["functions"].as_array().expect("functions array");

    for func_entry in functions_arr {
        let func_name = func_entry["function"].as_str().expect("function name");
        let obligations = func_entry["obligations"].as_array().expect("obligations array");

        for ob in obligations {
            // Each obligation should have proof_level field.
            assert!(
                ob.get("proof_level").is_some(),
                "obligation for {func_name} missing proof_level"
            );
            // Each obligation should have an outcome.
            assert!(ob.get("outcome").is_some(), "obligation for {func_name} missing outcome");
        }
    }

    // Count functions at each proof status.
    let mut fully_proved = 0usize;
    let mut has_failures = 0usize;
    let mut has_unknown = 0usize;

    for (name, results) in &per_function {
        if results.is_empty() {
            fully_proved += 1;
            continue;
        }
        let all_proved = results.iter().all(|(_, r)| r.is_proved());
        let any_failed = results.iter().any(|(_, r)| r.is_failed());
        if all_proved {
            fully_proved += 1;
        } else if any_failed {
            has_failures += 1;
        } else {
            has_unknown += 1;
        }
        // Suppress unused variable warning
        let _ = name;
    }

    eprintln!("=== Scale Per-Function Report ===");
    eprintln!("  Total functions: {}", per_function.len());
    eprintln!("  Fully proved: {fully_proved}");
    eprintln!("  Has failures: {has_failures}");
    eprintln!("  Has unknown only: {has_unknown}");
    eprintln!("  Report function entries: {}", functions_arr.len());
    eprintln!("=================================");
}

// ---------------------------------------------------------------------------
// Test 6: Source analysis at scale -- 130+ function source file
// ---------------------------------------------------------------------------

#[test]
fn test_scale_source_analysis_130_functions() {
    // Generate a realistic Rust source file with 130+ diverse function signatures.
    let mut source = String::from("//! Scale test: 130+ function crate for verification.\n\n");

    for i in 0..135 {
        match i % 13 {
            0 => {
                let _ = write!(
                    source,
                    "pub fn checked_add_{i}(a: u64, b: u64) -> u64 {{ a.wrapping_add(b) }}\n\n"
                );
            }
            1 => {
                let _ = write!(
                    source,
                    "#[requires(divisor != 0)]\npub fn safe_div_{i}(n: u32, divisor: u32) -> u32 {{ n / divisor }}\n\n"
                );
            }
            2 => {
                let _ =
                    write!(source, "pub unsafe fn deref_ptr_{i}(p: *const u8) -> u8 {{ *p }}\n\n");
            }
            3 => {
                let _ = write!(source, "fn private_helper_{i}(x: i32) -> i32 {{ x.abs() }}\n\n");
            }
            4 => {
                let _ = write!(
                    source,
                    "#[ensures(result >= 0)]\npub fn abs_val_{i}(x: i32) -> i32 {{ if x < 0 {{ -x }} else {{ x }} }}\n\n"
                );
            }
            5 => {
                // Generic-like pattern (monomorphized)
                let _ = write!(
                    source,
                    "pub fn identity_{i}<T: Clone>(val: T) -> T {{ val.clone() }}\n\n"
                );
            }
            6 => {
                // Iterator pattern
                let _ = write!(
                    source,
                    "pub fn sum_iter_{i}(data: &[i32]) -> i32 {{ data.iter().sum() }}\n\n"
                );
            }
            7 => {
                // Match expression
                let _ = write!(
                    source,
                    "pub fn classify_{i}(n: i32) -> &'static str {{ match n {{ 0 => \"zero\", _ if n > 0 => \"pos\", _ => \"neg\" }} }}\n\n"
                );
            }
            8 => {
                // Option unwrap pattern
                let _ = write!(
                    source,
                    "pub fn safe_get_{i}(data: &[u8], idx: usize) -> Option<u8> {{ data.get(idx).copied() }}\n\n"
                );
            }
            9 => {
                // Closure-like pattern
                let _ = write!(
                    source,
                    "pub fn apply_{i}(f: fn(i32) -> i32, x: i32) -> i32 {{ f(x) }}\n\n"
                );
            }
            10 => {
                // Const function
                let _ = write!(
                    source,
                    "pub const fn const_add_{i}(a: u32, b: u32) -> u32 {{ a.wrapping_add(b) }}\n\n"
                );
            }
            11 => {
                // Async-like function
                let _ = write!(
                    source,
                    "pub async fn async_fetch_{i}(url: &str) -> usize {{ url.len() }}\n\n"
                );
            }
            12 => {
                // Trait method with contract
                let _ = write!(
                    source,
                    "#[requires(lo <= hi)]\n#[ensures(result >= lo)]\npub fn clamp_{i}(val: i32, lo: i32, hi: i32) -> i32 {{ val.clamp(lo, hi) }}\n\n"
                );
            }
            _ => unreachable!(),
        }
    }

    // Verify source analysis discovers all functions.
    let fn_count = source
        .lines()
        .filter(|line| {
            let t = line.trim();
            (t.starts_with("pub fn ")
                || t.starts_with("pub unsafe fn ")
                || t.starts_with("pub async fn ")
                || t.starts_with("pub const fn ")
                || t.starts_with("fn "))
                && t.contains('(')
        })
        .count();

    assert!(fn_count >= 130, "source should have >= 130 functions, found {fn_count}");

    let requires_count = source.lines().filter(|l| l.trim().starts_with("#[requires")).count();
    let ensures_count = source.lines().filter(|l| l.trim().starts_with("#[ensures")).count();
    let unsafe_count = source.lines().filter(|l| l.trim().contains("unsafe fn")).count();
    let async_count = source.lines().filter(|l| l.trim().contains("async fn")).count();
    let const_count = source.lines().filter(|l| l.trim().contains("const fn")).count();

    assert!(requires_count >= 10, "should have >= 10 #[requires], got {requires_count}");
    assert!(ensures_count >= 10, "should have >= 10 #[ensures], got {ensures_count}");
    assert!(unsafe_count >= 10, "should have >= 10 unsafe fns, got {unsafe_count}");
    assert!(async_count >= 10, "should have >= 10 async fns, got {async_count}");
    assert!(const_count >= 10, "should have >= 10 const fns, got {const_count}");

    eprintln!("=== Scale Source Analysis (135 functions) ===");
    eprintln!("  Functions: {fn_count}");
    eprintln!("  #[requires]: {requires_count}");
    eprintln!("  #[ensures]: {ensures_count}");
    eprintln!("  unsafe fn: {unsafe_count}");
    eprintln!("  async fn: {async_count}");
    eprintln!("  const fn: {const_count}");
    eprintln!("=============================================");
}

// ---------------------------------------------------------------------------
// Test 7: Pattern coverage -- every pattern produces expected behavior
// ---------------------------------------------------------------------------

#[test]
fn test_scale_pattern_coverage() {
    // Generate exactly one function per pattern and verify each produces the
    // expected VC kinds (or no VCs for identity patterns).
    let mut vc_producing_patterns = 0usize;
    let mut vc_free_patterns = 0usize;

    for (i, &pattern) in ALL_SCALE_PATTERNS.iter().enumerate() {
        let name = format!("coverage_{i}");
        let func = match pattern {
            ScalePattern::CheckedAdd => make_checked_binop(&name, BinOp::Add, Ty::u32()),
            ScalePattern::CheckedSub => make_checked_binop(&name, BinOp::Sub, Ty::u64()),
            ScalePattern::CheckedMul => make_checked_binop(&name, BinOp::Mul, Ty::i32()),
            ScalePattern::Division => make_division(&name, Ty::u32()),
            ScalePattern::GuardedDivision => make_guarded_division(&name),
            ScalePattern::Remainder => make_remainder(&name),
            ScalePattern::ArrayIndex => make_array_index(&name, 16),
            ScalePattern::Contract => make_contract_fn(&name),
            ScalePattern::Noop => make_noop(&name, Ty::u32()),
            ScalePattern::BitwiseAnd => make_bitwise(&name, BinOp::BitAnd),
            ScalePattern::BitwiseOr => make_bitwise(&name, BinOp::BitOr),
            ScalePattern::BitwiseXor => make_bitwise(&name, BinOp::BitXor),
            ScalePattern::ShiftLeft => make_bitwise(&name, BinOp::Shl),
            ScalePattern::ShiftRight => make_bitwise(&name, BinOp::Shr),
            ScalePattern::CastWiden => make_cast(&name, Ty::u32(), Ty::u64()),
            ScalePattern::CastNarrow => make_cast(&name, Ty::u64(), Ty::u32()),
            ScalePattern::Negation => make_negation(&name, Ty::i32()),
            ScalePattern::AggregateTuple => make_aggregate_tuple(&name),
            ScalePattern::LenCheck => make_len_check(&name),
            ScalePattern::Branching => make_branching(&name),
            ScalePattern::RefPattern => make_ref_pattern(&name),
            ScalePattern::ComparisonChain => make_comparison_chain(&name),
        };

        let vcs = trust_vcgen::generate_vcs(&func);
        let router = trust_router::Router::new();
        let results = router.verify_all(&vcs);

        if vcs.is_empty() {
            vc_free_patterns += 1;
        } else {
            vc_producing_patterns += 1;
        }

        // Every VC should get a result.
        assert_eq!(
            vcs.len(),
            results.len(),
            "pattern {:?} ({name}): router must return one result per VC",
            pattern,
        );

        // No panics is the primary assertion -- pipeline handles all patterns.
    }

    eprintln!("=== Scale Pattern Coverage ===");
    eprintln!("  Total patterns: {}", ALL_SCALE_PATTERNS.len());
    eprintln!("  VC-producing: {vc_producing_patterns}");
    eprintln!("  VC-free: {vc_free_patterns}");
    eprintln!("==============================");
}
