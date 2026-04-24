//! Tests for trust-tmir-bridge.
//!
//! Author: Andrew Yates <andrew@andrewdyates.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use tmir::inst::{BinOp as TmirBinOp, ICmpOp, Inst, OverflowOp};
use tmir::ty::Ty as TmirTy;

use trust_types::{
    BasicBlock as TrustBlock, BinOp, BlockId, ConstValue, Contract, ContractKind, LocalDecl,
    Operand, Place, Rvalue, SourceSpan, Statement, Terminator, Ty, UnOp, VerifiableBody,
    VerifiableFunction,
};

use crate::lower::{BinOpMapping, BridgeError, lower_to_tmir, map_binop, map_type, map_unop};

// ---------------------------------------------------------------------------
// Type mapping tests
// ---------------------------------------------------------------------------

#[test]
fn test_map_type_bool() {
    assert_eq!(map_type(&Ty::Bool).unwrap(), TmirTy::Bool);
}

#[test]
fn test_map_type_integers() {
    assert_eq!(map_type(&Ty::i8()).unwrap(), TmirTy::I8);
    assert_eq!(map_type(&Ty::u8()).unwrap(), TmirTy::I8);
    assert_eq!(map_type(&Ty::i16()).unwrap(), TmirTy::I16);
    assert_eq!(map_type(&Ty::u16()).unwrap(), TmirTy::I16);
    assert_eq!(map_type(&Ty::i32()).unwrap(), TmirTy::I32);
    assert_eq!(map_type(&Ty::u32()).unwrap(), TmirTy::I32);
    assert_eq!(map_type(&Ty::i64()).unwrap(), TmirTy::I64);
    assert_eq!(map_type(&Ty::u64()).unwrap(), TmirTy::I64);
    assert_eq!(map_type(&Ty::i128()).unwrap(), TmirTy::I128);
    assert_eq!(map_type(&Ty::u128()).unwrap(), TmirTy::I128);
}

#[test]
fn test_map_type_signed_unsigned_same() {
    // tMIR does not distinguish signed/unsigned; same width maps to same type.
    assert_eq!(map_type(&Ty::i32()).unwrap(), map_type(&Ty::u32()).unwrap());
    assert_eq!(map_type(&Ty::i64()).unwrap(), map_type(&Ty::u64()).unwrap());
}

#[test]
fn test_map_type_floats() {
    assert_eq!(map_type(&Ty::f32_ty()).unwrap(), TmirTy::F32);
    assert_eq!(map_type(&Ty::f64_ty()).unwrap(), TmirTy::F64);
}

#[test]
fn test_map_type_unit_and_never() {
    assert_eq!(map_type(&Ty::Unit).unwrap(), TmirTy::Void);
    assert_eq!(map_type(&Ty::Never).unwrap(), TmirTy::Void);
}

#[test]
fn test_map_type_pointers() {
    assert_eq!(
        map_type(&Ty::Ref { mutable: false, inner: Box::new(Ty::i32()) }).unwrap(),
        TmirTy::Ptr
    );
    assert_eq!(
        map_type(&Ty::Ref { mutable: true, inner: Box::new(Ty::i32()) }).unwrap(),
        TmirTy::Ptr
    );
    assert_eq!(
        map_type(&Ty::RawPtr { mutable: false, pointee: Box::new(Ty::i32()) }).unwrap(),
        TmirTy::Ptr
    );
    assert_eq!(map_type(&Ty::Slice { elem: Box::new(Ty::u8()) }).unwrap(), TmirTy::Ptr);
}

#[test]
fn test_map_type_bv() {
    assert_eq!(map_type(&Ty::Bv(32)).unwrap(), TmirTy::I32);
    assert_eq!(map_type(&Ty::Bv(64)).unwrap(), TmirTy::I64);
    assert!(map_type(&Ty::Bv(7)).is_err());
}

// ---------------------------------------------------------------------------
// BinOp mapping tests
// ---------------------------------------------------------------------------

#[test]
fn test_map_binop_arithmetic() {
    assert_eq!(map_binop(BinOp::Add, false).unwrap(), BinOpMapping::Arith(TmirBinOp::Add));
    assert_eq!(map_binop(BinOp::Sub, false).unwrap(), BinOpMapping::Arith(TmirBinOp::Sub));
    assert_eq!(map_binop(BinOp::Mul, false).unwrap(), BinOpMapping::Arith(TmirBinOp::Mul));
}

#[test]
fn test_map_binop_division_signedness() {
    assert_eq!(map_binop(BinOp::Div, false).unwrap(), BinOpMapping::Arith(TmirBinOp::UDiv));
    assert_eq!(map_binop(BinOp::Div, true).unwrap(), BinOpMapping::Arith(TmirBinOp::SDiv));
    assert_eq!(map_binop(BinOp::Rem, false).unwrap(), BinOpMapping::Arith(TmirBinOp::URem));
    assert_eq!(map_binop(BinOp::Rem, true).unwrap(), BinOpMapping::Arith(TmirBinOp::SRem));
}

#[test]
fn test_map_binop_bitwise() {
    assert_eq!(map_binop(BinOp::BitAnd, false).unwrap(), BinOpMapping::Arith(TmirBinOp::And));
    assert_eq!(map_binop(BinOp::BitOr, false).unwrap(), BinOpMapping::Arith(TmirBinOp::Or));
    assert_eq!(map_binop(BinOp::BitXor, false).unwrap(), BinOpMapping::Arith(TmirBinOp::Xor));
}

#[test]
fn test_map_binop_shifts() {
    assert_eq!(map_binop(BinOp::Shl, false).unwrap(), BinOpMapping::Arith(TmirBinOp::Shl));
    assert_eq!(map_binop(BinOp::Shr, false).unwrap(), BinOpMapping::Arith(TmirBinOp::LShr));
    assert_eq!(map_binop(BinOp::Shr, true).unwrap(), BinOpMapping::Arith(TmirBinOp::AShr));
}

#[test]
fn test_map_binop_comparisons() {
    assert_eq!(map_binop(BinOp::Eq, false).unwrap(), BinOpMapping::Cmp(ICmpOp::Eq));
    assert_eq!(map_binop(BinOp::Ne, false).unwrap(), BinOpMapping::Cmp(ICmpOp::Ne));
    assert_eq!(map_binop(BinOp::Lt, false).unwrap(), BinOpMapping::Cmp(ICmpOp::Ult));
    assert_eq!(map_binop(BinOp::Lt, true).unwrap(), BinOpMapping::Cmp(ICmpOp::Slt));
    assert_eq!(map_binop(BinOp::Ge, true).unwrap(), BinOpMapping::Cmp(ICmpOp::Sge));
    assert_eq!(map_binop(BinOp::Ge, false).unwrap(), BinOpMapping::Cmp(ICmpOp::Uge));
}

#[test]
fn test_map_binop_cmp_unsupported() {
    assert!(map_binop(BinOp::Cmp, false).is_err());
}

// ---------------------------------------------------------------------------
// UnOp mapping tests
// ---------------------------------------------------------------------------

#[test]
fn test_map_unop() {
    assert_eq!(map_unop(UnOp::Not).unwrap(), tmir::inst::UnOp::Not);
    assert_eq!(map_unop(UnOp::Neg).unwrap(), tmir::inst::UnOp::Neg);
    assert!(map_unop(UnOp::PtrMetadata).is_err());
}

// ---------------------------------------------------------------------------
// Full function lowering tests
// ---------------------------------------------------------------------------

/// Helper: build MIR for `fn add(a: i32, b: i32) -> i32 { a + b }`
fn make_add_function() -> VerifiableFunction {
    VerifiableFunction {
        name: "add".to_string(),
        def_path: "test::add".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
            ],
            blocks: vec![TrustBlock {
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
            return_ty: Ty::i32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn test_lower_add_function() {
    let func = make_add_function();
    let module = lower_to_tmir(&func).expect("should lower");

    assert_eq!(module.name, "add");
    assert_eq!(module.functions.len(), 1);

    let tmir_func = &module.functions[0];
    assert_eq!(tmir_func.name, "add");
    assert_eq!(tmir_func.blocks.len(), 1);

    // Check function type.
    let ft = &module.func_types[tmir_func.ty.index() as usize];
    assert_eq!(ft.params, vec![TmirTy::I32, TmirTy::I32]);
    assert_eq!(ft.returns, vec![TmirTy::I32]);

    // Check the block has BinOp::Add and Return.
    let bb0 = &tmir_func.blocks[0];
    let has_add = bb0
        .body
        .iter()
        .any(|node| matches!(&node.inst, Inst::BinOp { op: TmirBinOp::Add, ty: TmirTy::I32, .. }));
    assert!(has_add, "should have an Add instruction");

    let has_return = bb0.body.iter().any(|node| matches!(&node.inst, Inst::Return { .. }));
    assert!(has_return, "should have a Return instruction");
}

#[test]
fn test_lower_unit_return_function() {
    let func = VerifiableFunction {
        name: "noop".to_string(),
        def_path: "test::noop".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_tmir(&func).expect("should lower");
    let ft = &module.func_types[module.functions[0].ty.index() as usize];
    assert!(ft.returns.is_empty(), "Unit return should produce empty returns");
}

#[test]
fn test_lower_constant_use() {
    let func = VerifiableFunction {
        name: "const_fn".to_string(),
        def_path: "test::const_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::i32(), name: None }],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(42))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::i32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_tmir(&func).expect("should lower");
    let bb0 = &module.functions[0].blocks[0];
    let has_const = bb0.body.iter().any(|node| matches!(&node.inst, Inst::Const { .. }));
    assert!(has_const, "should have a Const instruction");
}

#[test]
fn test_lower_goto_terminator() {
    let func = VerifiableFunction {
        name: "goto_fn".to_string(),
        def_path: "test::goto_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                TrustBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_tmir(&func).expect("should lower");
    assert_eq!(module.functions[0].blocks.len(), 2);

    let bb0 = &module.functions[0].blocks[0];
    let has_br = bb0.body.iter().any(|node| {
        matches!(
            &node.inst,
            Inst::Br { target, .. } if target.index() == 1
        )
    });
    assert!(has_br, "bb0 should branch to bb1");
}

#[test]
fn test_lower_switch_int_binary() {
    let func = VerifiableFunction {
        name: "branch_fn".to_string(),
        def_path: "test::branch_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::Bool, name: Some("cond".into()) },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(1)),
                        targets: vec![(1, BlockId(1))],
                        otherwise: BlockId(2),
                        span: SourceSpan::default(),
                    },
                },
                TrustBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
                TrustBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_tmir(&func).expect("should lower");
    let bb0 = &module.functions[0].blocks[0];

    // Should have ICmp + CondBr for a single-target SwitchInt.
    let has_condbr = bb0.body.iter().any(|node| matches!(&node.inst, Inst::CondBr { .. }));
    assert!(has_condbr, "single-target SwitchInt should emit CondBr");
}

#[test]
fn test_lower_switch_int_multiway() {
    let func = VerifiableFunction {
        name: "switch_fn".to_string(),
        def_path: "test::switch_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(1)),
                        targets: vec![(0, BlockId(1)), (7, BlockId(2))],
                        otherwise: BlockId(3),
                        span: SourceSpan::default(),
                    },
                },
                TrustBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
                TrustBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
                TrustBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_tmir(&func).expect("should lower");
    let bb0 = &module.functions[0].blocks[0];
    let has_switch = bb0.body.iter().any(|node| matches!(&node.inst, Inst::Switch { .. }));
    assert!(has_switch, "multi-target SwitchInt should emit Switch");
}

#[test]
fn test_lower_unreachable() {
    let func = VerifiableFunction {
        name: "unr".to_string(),
        def_path: "test::unr".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::Never, name: None }],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Unreachable,
            }],
            arg_count: 0,
            return_ty: Ty::Never,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_tmir(&func).expect("should lower");
    let bb0 = &module.functions[0].blocks[0];
    let has_unreachable = bb0.body.iter().any(|node| matches!(&node.inst, Inst::Unreachable));
    assert!(has_unreachable, "should emit Unreachable");
}

#[test]
fn test_lower_unary_not() {
    let func = VerifiableFunction {
        name: "not_fn".to_string(),
        def_path: "test::not_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Bool, name: None },
                LocalDecl { index: 1, ty: Ty::Bool, name: Some("x".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::UnaryOp(UnOp::Not, Operand::Copy(Place::local(1))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::Bool,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_tmir(&func).expect("should lower");
    let bb0 = &module.functions[0].blocks[0];
    let has_not = bb0
        .body
        .iter()
        .any(|node| matches!(&node.inst, Inst::UnOp { op: tmir::inst::UnOp::Not, .. }));
    assert!(has_not, "should have a Not instruction");
}

#[test]
fn test_lower_checked_add() {
    // fn checked(a: u64, b: u64) -> u64 with CheckedBinaryOp(Add)
    let func = VerifiableFunction {
        name: "checked_add".to_string(),
        def_path: "test::checked_add".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u64(), name: None },
                LocalDecl { index: 1, ty: Ty::u64(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::u64(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::u64(), Ty::Bool]), name: None },
            ],
            blocks: vec![TrustBlock {
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
            arg_count: 2,
            return_ty: Ty::u64(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_tmir(&func).expect("should lower");
    let bb0 = &module.functions[0].blocks[0];
    let has_overflow = bb0
        .body
        .iter()
        .any(|node| matches!(&node.inst, Inst::Overflow { op: OverflowOp::AddOverflow, .. }));
    assert!(has_overflow, "CheckedBinaryOp(Add) should emit Overflow(AddOverflow)");

    // The Overflow instruction should have a NoOverflow proof annotation.
    let overflow_node = bb0
        .body
        .iter()
        .find(|node| matches!(&node.inst, Inst::Overflow { .. }))
        .expect("overflow node");
    assert!(
        overflow_node.proofs.iter().any(|p| matches!(p, tmir::proof::ProofAnnotation::NoOverflow)),
        "Overflow instruction should carry NoOverflow proof annotation"
    );
}

#[test]
fn test_lower_midpoint_function() {
    // fn get_midpoint(a: u64, b: u64) -> u64 { (a + b) / 2 }
    let func = VerifiableFunction {
        name: "get_midpoint".to_string(),
        def_path: "midpoint::get_midpoint".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u64(), name: None },
                LocalDecl { index: 1, ty: Ty::u64(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::u64(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: Ty::u64(), name: None },
                LocalDecl { index: 4, ty: Ty::u64(), name: None },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                TrustBlock {
                    id: BlockId(1),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Div,
                                Operand::Copy(Place::local(3)),
                                Operand::Constant(ConstValue::Uint(2, 64)),
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
            ],
            arg_count: 2,
            return_ty: Ty::u64(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_tmir(&func).expect("midpoint should lower");
    assert_eq!(module.functions[0].blocks.len(), 2);

    let ft = &module.func_types[module.functions[0].ty.index() as usize];
    assert_eq!(ft.params, vec![TmirTy::I64, TmirTy::I64]);
    assert_eq!(ft.returns, vec![TmirTy::I64]);

    // bb0: Add + Br
    let bb0 = &module.functions[0].blocks[0];
    assert!(bb0.body.iter().any(|n| matches!(&n.inst, Inst::BinOp { op: TmirBinOp::Add, .. })));
    assert!(bb0.body.iter().any(|n| matches!(
        &n.inst,
        Inst::Br { target, .. } if target.index() == 1
    )));

    // bb1: Const(2) + UDiv + Copy + Return
    let bb1 = &module.functions[0].blocks[1];
    assert!(bb1.body.iter().any(|n| matches!(&n.inst, Inst::Const { .. })));
    assert!(bb1.body.iter().any(|n| matches!(&n.inst, Inst::BinOp { op: TmirBinOp::UDiv, .. })));
    assert!(bb1.body.iter().any(|n| matches!(&n.inst, Inst::Return { .. })));
}

#[test]
fn test_lower_nop_statement() {
    let func = VerifiableFunction {
        name: "nop_fn".to_string(),
        def_path: "test::nop_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Nop,
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                        span: SourceSpan::default(),
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

    let module = lower_to_tmir(&func).expect("nop should not block lowering");
    // Should have instructions (at least Copy + Return), no errors.
    assert!(!module.functions[0].blocks[0].body.is_empty());
}

#[test]
fn test_lower_contracts_to_obligations() {
    let func = VerifiableFunction {
        name: "contracted".to_string(),
        def_path: "test::contracted".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::i32(),
        },
        contracts: vec![
            Contract {
                kind: ContractKind::Requires,
                span: SourceSpan::default(),
                body: "x > 0".to_string(),
            },
            Contract {
                kind: ContractKind::Ensures,
                span: SourceSpan::default(),
                body: "result > 0".to_string(),
            },
        ],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_tmir(&func).expect("should lower");
    assert!(
        module.proof_obligations.len() >= 2,
        "should have at least 2 proof obligations (requires + ensures)"
    );

    let has_pre = module.proof_obligations.iter().any(|po| {
        matches!(po.kind, tmir::proof::ObligationKind::Precondition) && po.description == "x > 0"
    });
    assert!(has_pre, "should have a precondition obligation");

    let has_post = module.proof_obligations.iter().any(|po| {
        matches!(po.kind, tmir::proof::ObligationKind::Postcondition)
            && po.description == "result > 0"
    });
    assert!(has_post, "should have a postcondition obligation");
}

#[test]
fn test_lower_drop_terminator() {
    let func = VerifiableFunction {
        name: "drop_fn".to_string(),
        def_path: "test::drop_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Drop {
                        place: Place::local(0),
                        target: BlockId(1),
                        span: SourceSpan::default(),
                    },
                },
                TrustBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_tmir(&func).expect("drop should lower");
    let bb0 = &module.functions[0].blocks[0];
    let has_br =
        bb0.body.iter().any(|n| matches!(&n.inst, Inst::Br { target, .. } if target.index() == 1));
    assert!(has_br, "Drop should emit Br to target block");
}

#[test]
fn test_lower_call_terminator() {
    let func = VerifiableFunction {
        name: "caller".to_string(),
        def_path: "test::caller".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::i32(), name: None }],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        func: "callee".to_string(),
                        args: vec![Operand::Constant(ConstValue::Int(10))],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                TrustBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 0,
            return_ty: Ty::i32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_tmir(&func).expect("call should lower");
    let bb0 = &module.functions[0].blocks[0];
    let has_call = bb0.body.iter().any(|n| matches!(&n.inst, Inst::Call { .. }));
    assert!(has_call, "should have a Call instruction");
    let has_br =
        bb0.body.iter().any(|n| matches!(&n.inst, Inst::Br { target, .. } if target.index() == 1));
    assert!(has_br, "should branch to continuation block after call");
}

#[test]
fn test_lower_cast_widening() {
    let func = VerifiableFunction {
        name: "widen".to_string(),
        def_path: "test::widen".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i8(), name: Some("a".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Cast(Operand::Copy(Place::local(1)), Ty::i32()),
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

    let module = lower_to_tmir(&func).expect("should lower");
    let bb0 = &module.functions[0].blocks[0];
    let has_cast = bb0.body.iter().any(|n| matches!(&n.inst, Inst::Cast { .. }));
    assert!(has_cast, "should have a Cast instruction for widening");
}

#[test]
fn test_error_display() {
    let e = BridgeError::UnsupportedType("Ref { .. }".to_string());
    assert_eq!(e.to_string(), "unsupported type: Ref { .. }");

    let e = BridgeError::UnsupportedOp("calls".to_string());
    assert_eq!(e.to_string(), "unsupported operation: calls");

    let e = BridgeError::MissingBlock(5);
    assert_eq!(e.to_string(), "missing block: bb5");

    let e = BridgeError::MissingLocal(3);
    assert_eq!(e.to_string(), "missing local: _3");
}

#[test]
fn test_lower_assert_terminator() {
    use trust_types::AssertMessage;

    let func = VerifiableFunction {
        name: "assert_fn".to_string(),
        def_path: "test::assert_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::Bool, name: Some("cond".into()) },
            ],
            blocks: vec![
                TrustBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::local(1)),
                        expected: true,
                        msg: AssertMessage::BoundsCheck,
                        target: BlockId(1),
                        span: SourceSpan::default(),
                    },
                },
                TrustBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_tmir(&func).expect("should lower");
    let bb0 = &module.functions[0].blocks[0];

    let has_assert = bb0.body.iter().any(|n| matches!(&n.inst, Inst::Assert { .. }));
    assert!(has_assert, "should have an Assert instruction");

    // Should also have a panic-freedom obligation.
    let has_panic_freedom = module
        .proof_obligations
        .iter()
        .any(|po| matches!(po.kind, tmir::proof::ObligationKind::PanicFreedom));
    assert!(has_panic_freedom, "assert should generate panic-freedom obligation");
}

#[test]
fn test_lower_aggregate_construction() {
    let func = VerifiableFunction {
        name: "agg_fn".to_string(),
        def_path: "test::agg_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Tuple(vec![Ty::i32(), Ty::i32()]), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Aggregate(
                        trust_types::AggregateKind::Tuple,
                        vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::Tuple(vec![Ty::i32(), Ty::i32()]),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_tmir(&func).expect("aggregate should lower");
    let bb0 = &module.functions[0].blocks[0];

    // Should have Undef + InsertField + InsertField + Return.
    let has_undef = bb0.body.iter().any(|n| matches!(&n.inst, Inst::Undef { .. }));
    assert!(has_undef, "aggregate construction should start with Undef");

    let insert_count =
        bb0.body.iter().filter(|n| matches!(&n.inst, Inst::InsertField { .. })).count();
    assert_eq!(insert_count, 2, "should have 2 InsertField instructions for 2-element tuple");
}

#[test]
fn test_lower_discriminant_rvalue() {
    let func = VerifiableFunction {
        name: "discr_fn".to_string(),
        def_path: "test::discr_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u64(), name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Adt {
                        name: "MyEnum".to_string(),
                        fields: vec![("tag".to_string(), Ty::u64())],
                    },
                    name: Some("e".into()),
                },
            ],
            blocks: vec![TrustBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Discriminant(Place::local(1)),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::u64(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let module = lower_to_tmir(&func).expect("discriminant should lower");
    let bb0 = &module.functions[0].blocks[0];
    let has_extract =
        bb0.body.iter().any(|n| matches!(&n.inst, Inst::ExtractField { field: 0, .. }));
    assert!(has_extract, "Discriminant should emit ExtractField(0)");
}
