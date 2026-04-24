// trust-vcgen/unsafe_verify/tests.rs: Tests for unsafe code verification
//
// Part of #79, #137: Unsafe code verification
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use super::detection::{
    attach_safety_comments, detect_unsafe_blocks, generate_safety_vcs, has_raw_deref,
    is_unsafe_fn_call, parse_safety_comment,
};
use super::verifier::{
    UnsafeVerifier, classify_vc_from_assertion, deref_operand_name, generate_unsafe_vcs,
};
use super::*;
use trust_types::fx::FxHashSet;

fn collect_free_vars(formula: &Formula) -> FxHashSet<String> {
    let mut vars = FxHashSet::default();
    collect_vars_recursive(formula, &mut vars);
    vars
}

fn collect_vars_recursive(formula: &Formula, vars: &mut FxHashSet<String>) {
    match formula {
        Formula::Var(name, _) => {
            vars.insert(name.clone());
        }
        _ => {
            for child in formula.children() {
                collect_vars_recursive(child, vars);
            }
        }
    }
}

fn is_conservative_or_concrete_check(formula: &Formula) -> bool {
    match formula {
        Formula::Bool(true) | Formula::Bool(false) => true,
        Formula::Eq(lhs, rhs) => {
            !matches!(lhs.as_ref(), Formula::Var(_, _))
                || !matches!(rhs.as_ref(), Formula::Var(_, _))
        }
        _ => false,
    }
}

/// Build a function with an unsafe ptr::read call.
fn unsafe_ptr_read_function() -> VerifiableFunction {
    VerifiableFunction {
        name: "read_raw".to_string(),
        def_path: "test::read_raw".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u32()) },
                    name: Some("ptr".into()),
                },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("val".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        func: "core::ptr::read".to_string(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(2),
                        target: Some(BlockId(1)),
                        span: SourceSpan {
                            file: "test.rs".into(),
                            line_start: 10,
                            col_start: 8,
                            line_end: 10,
                            col_end: 30,
                        },
                        atomic: None,
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
            ],
            arg_count: 1,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// Build a function with a raw pointer deref in a statement.
fn unsafe_deref_function() -> VerifiableFunction {
    VerifiableFunction {
        name: "deref_raw".to_string(),
        def_path: "test::deref_raw".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u32()) },
                    name: Some("raw_ptr".into()),
                },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("value".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::Use(Operand::Copy(Place {
                        local: 1,
                        projections: vec![Projection::Deref],
                    })),
                    span: SourceSpan {
                        file: "test.rs".into(),
                        line_start: 5,
                        col_start: 4,
                        line_end: 5,
                        col_end: 15,
                    },
                }],
                terminator: Terminator::Return,
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

/// Build a safe function with no unsafe blocks.
fn safe_function() -> VerifiableFunction {
    VerifiableFunction {
        name: "safe_add".to_string(),
        def_path: "test::safe_add".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("b".into()) },
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
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// Build a function with a transmute call.
fn transmute_function() -> VerifiableFunction {
    VerifiableFunction {
        name: "transmute_fn".to_string(),
        def_path: "test::transmute_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("input".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("output".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        func: "core::mem::transmute".to_string(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(2),
                        target: Some(BlockId(1)),
                        span: SourceSpan {
                            file: "test.rs".into(),
                            line_start: 8,
                            col_start: 4,
                            line_end: 8,
                            col_end: 40,
                        },
                        atomic: None,
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
            ],
            arg_count: 1,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// Build a function with an FFI call.
fn ffi_function() -> VerifiableFunction {
    VerifiableFunction {
        name: "call_ffi".to_string(),
        def_path: "test::call_ffi".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Ref {
                        mutable: false,
                        inner: Box::new(Ty::Int { width: 8, signed: false }),
                    },
                    name: Some("buf".into()),
                },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("result".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        func: "libc::ffi::write".to_string(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(2),
                        target: Some(BlockId(1)),
                        span: SourceSpan {
                            file: "test.rs".into(),
                            line_start: 12,
                            col_start: 4,
                            line_end: 12,
                            col_end: 30,
                        },
                        atomic: None,
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
            ],
            arg_count: 1,
            return_ty: Ty::i32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

// ── Existing tests (preserved) ──────────────────────────────────────

#[test]
fn test_detect_unsafe_blocks_ptr_read() {
    let func = unsafe_ptr_read_function();
    let blocks = detect_unsafe_blocks(&func);
    assert_eq!(blocks.len(), 1, "should detect 1 unsafe block for ptr::read");
    assert_eq!(blocks[0].block_id, BlockId(0));
    assert_eq!(blocks[0].span.line_start, 10);
}

#[test]
fn test_detect_unsafe_blocks_deref() {
    let func = unsafe_deref_function();
    let blocks = detect_unsafe_blocks(&func);
    assert_eq!(blocks.len(), 1, "should detect 1 unsafe block for raw deref");
    assert_eq!(blocks[0].block_id, BlockId(0));
}

#[test]
fn test_detect_unsafe_blocks_safe_function() {
    let func = safe_function();
    let blocks = detect_unsafe_blocks(&func);
    assert!(blocks.is_empty(), "safe function should have no unsafe blocks");
}

#[test]
fn test_parse_safety_comment_single_line_because() {
    let comment = "// SAFETY: pointer is non-null because we checked it above";
    let claim = parse_safety_comment(comment);
    assert_eq!(claim.invariant, "pointer is non-null");
    assert_eq!(claim.justification, "we checked it above");
}

#[test]
fn test_parse_safety_comment_multiline() {
    let comment = "// SAFETY: pointer is valid and aligned\n// the caller guarantees this via the function contract";
    let claim = parse_safety_comment(comment);
    assert_eq!(claim.invariant, "pointer is valid and aligned");
    assert_eq!(claim.justification, "the caller guarantees this via the function contract");
}

#[test]
fn test_parse_safety_comment_invariant_only() {
    let comment = "// SAFETY: pointer is non-null";
    let claim = parse_safety_comment(comment);
    assert_eq!(claim.invariant, "pointer is non-null");
    assert_eq!(claim.justification, "no justification provided");
}

#[test]
fn test_parse_safety_comment_empty() {
    let claim = parse_safety_comment("");
    assert!(claim.invariant.is_empty());
    assert_eq!(claim.justification, "no justification provided");
}

#[test]
fn test_parse_safety_comment_no_prefix() {
    let comment = "// this is just a regular comment";
    let claim = parse_safety_comment(comment);
    // No SAFETY: prefix, so the whole comment becomes invariant
    assert_eq!(claim.invariant, "this is just a regular comment");
    assert_eq!(claim.justification, "no justification provided");
}

#[test]
fn test_generate_safety_vcs_with_claim() {
    let func = unsafe_ptr_read_function();
    let blocks = vec![UnsafeBlock {
        span: SourceSpan {
            file: "test.rs".into(),
            line_start: 10,
            col_start: 8,
            line_end: 10,
            col_end: 30,
        },
        safety_comment: Some("// SAFETY: pointer is non-null and aligned".into()),
        safety_claim: Some(SafetyClaim {
            invariant: "pointer is non-null and aligned".to_string(),
            justification: "no justification provided".to_string(),
        }),
        block_id: BlockId(0),
    }];

    let vcs = generate_safety_vcs(&func, &blocks);

    // Should produce: invariant VC + null check VC + alignment check VC
    assert_eq!(vcs.len(), 3, "claim with non-null + aligned = 3 VCs");

    // First VC: the invariant assertion
    assert!(matches!(&vcs[0].kind, VcKind::Assertion { message } if message.contains("[unsafe]")));
    assert!(
        matches!(&vcs[0].kind, VcKind::Assertion { message } if message.contains("SAFETY claim"))
    );

    // Second VC: null pointer check
    assert!(
        matches!(&vcs[1].kind, VcKind::Assertion { message } if message.contains("null pointer check"))
    );

    // Third VC: alignment check
    assert!(
        matches!(&vcs[2].kind, VcKind::Assertion { message } if message.contains("alignment check"))
    );

    // All should be L0Safety level
    for vc in &vcs {
        assert_eq!(vc.kind.proof_level(), ProofLevel::L0Safety);
    }
}

#[test]
fn test_safety_claim_vc_not_vacuously_true() {
    let func = unsafe_ptr_read_function();
    let blocks = vec![UnsafeBlock {
        span: SourceSpan {
            file: "test.rs".into(),
            line_start: 10,
            col_start: 8,
            line_end: 10,
            col_end: 30,
        },
        safety_comment: Some("// SAFETY: pointer is aligned".into()),
        safety_claim: Some(SafetyClaim {
            invariant: "pointer is aligned".to_string(),
            justification: "caller guarantees it".to_string(),
        }),
        block_id: BlockId(0),
    }];

    let vcs = generate_safety_vcs(&func, &blocks);
    assert_eq!(vcs.len(), 2, "claim + alignment check = 2 VCs");

    let alignment_vc = vcs
        .iter()
        .find(|vc| {
            matches!(
                &vc.kind,
                VcKind::Assertion { message } if message.contains("alignment check")
            )
        })
        .expect("alignment VC present");
    assert!(matches!(alignment_vc.formula, Formula::Bool(true)));
    assert!(matches!(
        &alignment_vc.kind,
        VcKind::Assertion { message } if message.contains("(unverified)")
    ));

    for vc in &vcs {
        let vars = collect_free_vars(&vc.formula);
        assert!(
            matches!(vc.formula, Formula::Bool(true) | Formula::Bool(false)) || vars.is_empty(),
            "safety claim VC should not leave free vars in a trivially dischargeable formula: {:?}",
            vc.formula
        );
    }
}

#[test]
fn test_generate_safety_vcs_without_claim() {
    let func = unsafe_ptr_read_function();
    let blocks = vec![UnsafeBlock {
        span: SourceSpan::default(),
        safety_comment: None,
        safety_claim: None,
        block_id: BlockId(0),
    }];

    let vcs = generate_safety_vcs(&func, &blocks);

    assert_eq!(vcs.len(), 1, "missing claim should produce 1 VC");
    assert!(matches!(
        &vcs[0].kind,
        VcKind::Assertion { message } if message.contains("missing SAFETY comment")
    ));
    // Missing SAFETY comment VC is always SAT (finding)
    assert!(matches!(vcs[0].formula, Formula::Bool(true)));
}

#[test]
fn test_generate_safety_vcs_empty() {
    let func = safe_function();
    let blocks: Vec<UnsafeBlock> = vec![];
    let vcs = generate_safety_vcs(&func, &blocks);
    assert!(vcs.is_empty(), "no unsafe blocks = no VCs");
}

#[test]
fn test_attach_safety_comments_matches_by_span() {
    let mut blocks = vec![UnsafeBlock {
        span: SourceSpan {
            file: "test.rs".into(),
            line_start: 10,
            col_start: 8,
            line_end: 10,
            col_end: 30,
        },
        safety_comment: None,
        safety_claim: None,
        block_id: BlockId(0),
    }];

    let comments = vec![(
        SourceSpan {
            file: "test.rs".into(),
            line_start: 8,
            col_start: 4,
            line_end: 9,
            col_end: 50,
        },
        "// SAFETY: pointer is valid because caller guarantees it".to_string(),
    )];

    attach_safety_comments(&mut blocks, &comments);

    assert!(blocks[0].safety_comment.is_some());
    assert!(blocks[0].safety_claim.is_some());
    let claim = blocks[0].safety_claim.as_ref().unwrap();
    assert_eq!(claim.invariant, "pointer is valid");
    assert_eq!(claim.justification, "caller guarantees it");
}

#[test]
fn test_attach_safety_comments_no_match_wrong_file() {
    let mut blocks = vec![UnsafeBlock {
        span: SourceSpan {
            file: "test.rs".into(),
            line_start: 10,
            col_start: 0,
            line_end: 10,
            col_end: 30,
        },
        safety_comment: None,
        safety_claim: None,
        block_id: BlockId(0),
    }];

    let comments = vec![(
        SourceSpan {
            file: "other.rs".into(),
            line_start: 9,
            col_start: 0,
            line_end: 9,
            col_end: 50,
        },
        "// SAFETY: this is in another file".to_string(),
    )];

    attach_safety_comments(&mut blocks, &comments);
    assert!(blocks[0].safety_comment.is_none(), "wrong file should not match");
}

#[test]
fn test_attach_safety_comments_no_match_too_far() {
    let mut blocks = vec![UnsafeBlock {
        span: SourceSpan {
            file: "test.rs".into(),
            line_start: 20,
            col_start: 0,
            line_end: 20,
            col_end: 30,
        },
        safety_comment: None,
        safety_claim: None,
        block_id: BlockId(0),
    }];

    let comments = vec![(
        SourceSpan {
            file: "test.rs".into(),
            line_start: 5,
            col_start: 0,
            line_end: 5,
            col_end: 50,
        },
        "// SAFETY: too far away".to_string(),
    )];

    attach_safety_comments(&mut blocks, &comments);
    assert!(blocks[0].safety_comment.is_none(), "comment too far should not match");
}

#[test]
fn test_is_unsafe_fn_call() {
    assert!(is_unsafe_fn_call("core::ptr::read"));
    assert!(is_unsafe_fn_call("std::ptr::write"));
    assert!(is_unsafe_fn_call("core::slice::from_raw_parts"));
    assert!(is_unsafe_fn_call("std::mem::transmute"));
    assert!(is_unsafe_fn_call("core::intrinsics::copy"));
    assert!(is_unsafe_fn_call("some::ffi::extern_call"));
    assert!(is_unsafe_fn_call("alloc::alloc::alloc"));
    assert!(is_unsafe_fn_call("std::str::from_utf8_unchecked"));
    assert!(!is_unsafe_fn_call("std::vec::Vec::push"));
    assert!(!is_unsafe_fn_call("core::result::Result::unwrap"));
}

#[test]
fn test_has_raw_deref() {
    let raw_func = unsafe_deref_function();
    assert!(has_raw_deref(&raw_func, &Rvalue::Use(Operand::Copy(Place {
        local: 1,
        projections: vec![Projection::Deref],
    }))));

    assert!(!has_raw_deref(&raw_func, &Rvalue::Use(Operand::Copy(Place::local(1)))));

    assert!(has_raw_deref(&raw_func, &Rvalue::Ref {
        mutable: false,
        place: Place { local: 1, projections: vec![Projection::Deref] },
    }));

    let safe_ref_func = VerifiableFunction {
        name: "safe_ref".to_string(),
        def_path: "test::safe_ref".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Ref { mutable: false, inner: Box::new(Ty::u32()) },
                    name: Some("ptr".into()),
                },
            ],
            blocks: vec![],
            arg_count: 1,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    assert!(!has_raw_deref(&safe_ref_func, &Rvalue::Use(Operand::Copy(Place {
        local: 1,
        projections: vec![Projection::Deref],
    }))));
    assert!(!has_raw_deref(&safe_ref_func, &Rvalue::Ref {
        mutable: false,
        place: Place { local: 1, projections: vec![Projection::Deref] },
    }));
}

#[test]
fn test_check_unsafe_integration() {
    let func = unsafe_ptr_read_function();
    let comments = vec![(
        SourceSpan {
            file: "test.rs".into(),
            line_start: 9,
            col_start: 4,
            line_end: 9,
            col_end: 60,
        },
        "// SAFETY: pointer is non-null because allocated on the heap".to_string(),
    )];

    let mut vcs = Vec::new();
    check_unsafe(&func, &comments, &mut vcs);

    // Should have VCs from the unsafe block with the attached comment
    assert!(!vcs.is_empty(), "should generate VCs for unsafe block");
    assert!(
        vcs.iter().any(|vc| matches!(
            &vc.kind,
            VcKind::Assertion { message } if message.contains("[unsafe]")
        )),
        "should have [unsafe] tagged assertions"
    );
}

#[test]
fn test_check_unsafe_safe_function_no_vcs() {
    let func = safe_function();
    let mut vcs = Vec::new();
    check_unsafe(&func, &[], &mut vcs);
    assert!(vcs.is_empty(), "safe function should produce no unsafe VCs");
}

#[test]
fn test_check_unsafe_no_comments_produces_missing_vc() {
    let func = unsafe_ptr_read_function();
    let mut vcs = Vec::new();
    check_unsafe(&func, &[], &mut vcs);

    assert_eq!(vcs.len(), 1, "unsafe block without comment = 1 missing-comment VC");
    assert!(matches!(
        &vcs[0].kind,
        VcKind::Assertion { message } if message.contains("missing SAFETY comment")
    ));
}

// ── New tests (#137): UnsafeVcKind, UnsafeVerifier, generate_unsafe_vcs ──

#[test]
fn test_unsafe_vc_kind_descriptions() {
    let deref = UnsafeVcKind::RawPointerDeref { pointer_expr: "*ptr".into() };
    assert_eq!(deref.description(), "raw pointer dereference: *ptr");

    let transmute = UnsafeVcKind::Transmute { from_ty: "u32".into(), to_ty: "i32".into() };
    assert_eq!(transmute.description(), "transmute from u32 to i32");

    let union_access =
        UnsafeVcKind::UnionAccess { union_name: "MyUnion".into(), field_name: "value".into() };
    assert_eq!(union_access.description(), "union field access: MyUnion.value");

    let ffi = UnsafeVcKind::FfiCall { callee: "libc::write".into() };
    assert_eq!(ffi.description(), "FFI call to libc::write");

    let asm = UnsafeVcKind::InlineAsm { label: "cpuid".into() };
    assert_eq!(asm.description(), "inline assembly: cpuid");

    let mutable_static = UnsafeVcKind::MutableStaticAccess { static_name: "GLOBAL_STATE".into() };
    assert_eq!(mutable_static.description(), "mutable static access: GLOBAL_STATE");
}

#[test]
fn test_unsafe_vc_kind_serialization_roundtrip() {
    let kinds = vec![
        UnsafeVcKind::RawPointerDeref { pointer_expr: "*p".into() },
        UnsafeVcKind::Transmute { from_ty: "u32".into(), to_ty: "f32".into() },
        UnsafeVcKind::UnionAccess { union_name: "U".into(), field_name: "f".into() },
        UnsafeVcKind::FfiCall { callee: "libc::read".into() },
        UnsafeVcKind::InlineAsm { label: "nop".into() },
        UnsafeVcKind::MutableStaticAccess { static_name: "G".into() },
    ];

    for kind in &kinds {
        let json = serde_json::to_string(kind).expect("serialize UnsafeVcKind");
        let round: UnsafeVcKind = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(&round, kind);
    }
}

#[test]
fn test_unsafe_verifier_safe_function_empty() {
    let func = safe_function();
    let mut verifier = UnsafeVerifier::new(&func);
    assert_eq!(verifier.block_count(), 0);
    let vcs = verifier.generate();
    assert!(vcs.is_empty(), "safe function produces no unsafe VCs");
}

#[test]
fn test_unsafe_verifier_ptr_read_no_comments() {
    let func = unsafe_ptr_read_function();
    let mut verifier = UnsafeVerifier::new(&func);
    assert_eq!(verifier.block_count(), 1);
    let vcs = verifier.generate();

    // Should have: 1 missing-comment VC (from claim pass)
    // No typed VCs for ptr::read call (not a deref in stmts, it's a Call terminator)
    assert!(
        vcs.iter().any(|uvc| matches!(
            &uvc.vc.kind,
            VcKind::Assertion { message } if message.contains("missing SAFETY comment")
        )),
        "should have missing-comment VC"
    );
}

#[test]
fn test_unsafe_verifier_deref_generates_typed_vcs() {
    let func = unsafe_deref_function();
    let mut verifier = UnsafeVerifier::new(&func);
    assert_eq!(verifier.block_count(), 1);
    let vcs = verifier.generate();

    // Claim pass: 1 missing-comment VC
    // Typed pass: 3 VCs (null, alignment, bounds) for the deref
    assert_eq!(vcs.len(), 4, "1 missing-comment + 3 deref VCs = 4 total");

    // Check typed VCs
    let deref_vcs: Vec<_> = vcs
        .iter()
        .filter(|uvc| matches!(&uvc.unsafe_kind, UnsafeVcKind::RawPointerDeref { .. }))
        .collect();
    assert_eq!(deref_vcs.len(), 4, "all 4 VCs should be RawPointerDeref");

    // Check VC messages
    let messages: Vec<_> = vcs
        .iter()
        .map(|uvc| match &uvc.vc.kind {
            VcKind::Assertion { message } => message.clone(),
            _ => String::new(),
        })
        .collect();

    assert!(messages.iter().any(|m| m.contains("null check")));
    assert!(messages.iter().any(|m| m.contains("alignment check")));
    assert!(messages.iter().any(|m| m.contains("bounds check")));
}

#[test]
fn test_no_unconstrained_vars_in_deref_vcs() {
    let func = unsafe_deref_function();
    let mut verifier = UnsafeVerifier::new(&func);
    let vcs = verifier.generate();

    let deref_vcs: Vec<_> = vcs
        .iter()
        .filter(|unsafe_vc| matches!(&unsafe_vc.unsafe_kind, UnsafeVcKind::RawPointerDeref { .. }))
        .collect();
    assert!(!deref_vcs.is_empty(), "expected raw deref VCs");

    let bounds_vc = deref_vcs
        .iter()
        .find(|unsafe_vc| {
            matches!(
                &unsafe_vc.vc.kind,
                VcKind::Assertion { message } if message.contains("bounds check")
            )
        })
        .expect("bounds VC present");
    assert!(matches!(bounds_vc.vc.formula, Formula::Bool(true)));
    assert!(matches!(
        &bounds_vc.vc.kind,
        VcKind::Assertion { message } if message.contains("(unverified)")
    ));

    for unsafe_vc in &deref_vcs {
        let vars = collect_free_vars(&unsafe_vc.vc.formula);
        if !vars.is_empty() {
            assert!(
                is_conservative_or_concrete_check(&unsafe_vc.vc.formula),
                "deref VC contains unconstrained vars in unsafe shape: {:?}",
                unsafe_vc.vc.formula
            );
        }
    }
}

#[test]
fn test_unsafe_verifier_transmute_generates_layout_and_validity_vcs() {
    let func = transmute_function();
    let mut verifier = UnsafeVerifier::new(&func);
    assert_eq!(verifier.block_count(), 1);
    let vcs = verifier.generate();

    // Should have:
    // 1 missing-comment VC (from claim pass)
    // 2 transmute VCs (layout + validity)
    let transmute_vcs: Vec<_> = vcs
        .iter()
        .filter(|uvc| matches!(&uvc.unsafe_kind, UnsafeVcKind::Transmute { .. }))
        .collect();
    assert!(transmute_vcs.len() >= 2, "should have at least 2 transmute VCs");

    let messages: Vec<_> = transmute_vcs
        .iter()
        .map(|uvc| match &uvc.vc.kind {
            VcKind::Assertion { message } => message.clone(),
            _ => String::new(),
        })
        .collect();
    assert!(messages.iter().any(|m| m.contains("layout compatibility")));
    assert!(messages.iter().any(|m| m.contains("validity invariant")));
}

#[test]
fn test_no_unconstrained_vars_in_transmute_vcs() {
    let func = transmute_function();
    let mut verifier = UnsafeVerifier::new(&func);
    let vcs = verifier.generate();

    let transmute_vcs: Vec<_> = vcs
        .iter()
        .filter(|unsafe_vc| matches!(&unsafe_vc.unsafe_kind, UnsafeVcKind::Transmute { .. }))
        .collect();
    assert!(!transmute_vcs.is_empty(), "expected transmute VCs");

    let layout_vc = transmute_vcs
        .iter()
        .find(|unsafe_vc| {
            matches!(
                &unsafe_vc.vc.kind,
                VcKind::Assertion { message } if message.contains("layout compatibility")
            )
        })
        .expect("layout VC present");
    assert!(matches!(layout_vc.vc.formula, Formula::Bool(true)));
    assert!(matches!(
        &layout_vc.vc.kind,
        VcKind::Assertion { message } if message.contains("(unverified)")
    ));

    for unsafe_vc in &transmute_vcs {
        let vars = collect_free_vars(&unsafe_vc.vc.formula);
        if !vars.is_empty() {
            assert!(
                is_conservative_or_concrete_check(&unsafe_vc.vc.formula),
                "transmute VC contains unconstrained vars in unsafe shape: {:?}",
                unsafe_vc.vc.formula
            );
        }
    }
}

#[test]
fn test_unsafe_verifier_ffi_generates_pre_post_null_vcs() {
    let func = ffi_function();
    let mut verifier = UnsafeVerifier::new(&func);
    assert_eq!(verifier.block_count(), 1);
    let vcs = verifier.generate();

    let ffi_vcs: Vec<_> =
        vcs.iter().filter(|uvc| matches!(&uvc.unsafe_kind, UnsafeVcKind::FfiCall { .. })).collect();
    assert!(ffi_vcs.len() >= 3, "should have at least 3 FFI VCs");

    let messages: Vec<_> = ffi_vcs
        .iter()
        .map(|uvc| match &uvc.vc.kind {
            VcKind::Assertion { message } => message.clone(),
            _ => String::new(),
        })
        .collect();
    assert!(messages.iter().any(|m| m.contains("precondition")));
    assert!(messages.iter().any(|m| m.contains("postcondition")));
    assert!(messages.iter().any(|m| m.contains("null pointer argument")));
}

#[test]
fn test_no_unconstrained_vars_in_ffi_vcs() {
    let func = ffi_function();
    let mut verifier = UnsafeVerifier::new(&func);
    let vcs = verifier.generate();

    let ffi_vcs: Vec<_> = vcs
        .iter()
        .filter(|unsafe_vc| matches!(&unsafe_vc.unsafe_kind, UnsafeVcKind::FfiCall { .. }))
        .collect();
    assert!(!ffi_vcs.is_empty(), "expected FFI VCs");

    for unsafe_vc in &ffi_vcs {
        let vars = collect_free_vars(&unsafe_vc.vc.formula);
        if !vars.is_empty() {
            assert!(
                is_conservative_or_concrete_check(&unsafe_vc.vc.formula),
                "FFI VC contains unconstrained vars in unsafe shape: {:?}",
                unsafe_vc.vc.formula
            );
        }
    }
}

#[test]
fn test_generate_unsafe_vcs_entry_point() {
    let func = unsafe_deref_function();
    let vcs = generate_unsafe_vcs(&func, &[]);

    assert!(!vcs.is_empty(), "should produce VCs for unsafe function");
    // All VCs should have an unsafe_kind
    for uvc in &vcs {
        let _ = uvc.unsafe_kind.description();
    }
}

#[test]
fn test_generate_unsafe_vcs_with_comments() {
    let func = unsafe_ptr_read_function();
    let comments = vec![(
        SourceSpan {
            file: "test.rs".into(),
            line_start: 9,
            col_start: 4,
            line_end: 9,
            col_end: 60,
        },
        "// SAFETY: pointer is non-null because allocated on the heap".to_string(),
    )];

    let vcs = generate_unsafe_vcs(&func, &comments);

    // With a matching comment, we should get claim VCs (not missing-comment)
    assert!(
        vcs.iter().any(|uvc| matches!(
            &uvc.vc.kind,
            VcKind::Assertion { message } if message.contains("SAFETY claim")
        )),
        "should have SAFETY claim VC"
    );
    assert!(
        !vcs.iter().any(|uvc| matches!(
            &uvc.vc.kind,
            VcKind::Assertion { message } if message.contains("missing SAFETY comment")
        )),
        "should NOT have missing-comment VC when comment is present"
    );
}

#[test]
fn test_unsafe_verifier_with_comments_builder() {
    let func = unsafe_ptr_read_function();
    let comments = vec![(
        SourceSpan {
            file: "test.rs".into(),
            line_start: 9,
            col_start: 4,
            line_end: 9,
            col_end: 60,
        },
        "// SAFETY: pointer is non-null because allocated on the heap".to_string(),
    )];

    let mut verifier = UnsafeVerifier::new(&func).with_comments(comments);
    assert_eq!(verifier.block_count(), 1);
    let vcs = verifier.generate();
    assert!(!vcs.is_empty());
}

#[test]
fn test_classify_vc_from_assertion_transmute() {
    let vc = VerificationCondition {
        kind: VcKind::Assertion { message: "[unsafe:transmute] layout check".into() },
        function: "f".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };
    let kind = classify_vc_from_assertion(&vc);
    assert!(matches!(kind, UnsafeVcKind::Transmute { .. }));
}

#[test]
fn test_classify_vc_from_assertion_ffi() {
    let vc = VerificationCondition {
        kind: VcKind::Assertion { message: "[unsafe] FFI precondition".into() },
        function: "f".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };
    let kind = classify_vc_from_assertion(&vc);
    assert!(matches!(kind, UnsafeVcKind::FfiCall { .. }));
}

#[test]
fn test_classify_vc_from_assertion_default() {
    let vc = VerificationCondition {
        kind: VcKind::Assertion { message: "[unsafe] something generic".into() },
        function: "f".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };
    let kind = classify_vc_from_assertion(&vc);
    assert!(matches!(kind, UnsafeVcKind::RawPointerDeref { .. }));
}

#[test]
fn test_deref_operand_name() {
    let rvalue =
        Rvalue::Use(Operand::Copy(Place { local: 5, projections: vec![Projection::Deref] }));
    assert_eq!(deref_operand_name(&rvalue), "_5");

    let rvalue_ref = Rvalue::Ref {
        mutable: false,
        place: Place { local: 3, projections: vec![Projection::Deref] },
    };
    assert_eq!(deref_operand_name(&rvalue_ref), "_3");

    let rvalue_other = Rvalue::BinaryOp(
        BinOp::Add,
        Operand::Copy(Place::local(1)),
        Operand::Copy(Place::local(2)),
    );
    assert_eq!(deref_operand_name(&rvalue_other), "unknown");
}
