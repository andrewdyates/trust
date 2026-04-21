// trust-integration-tests/tests/rc_pipeline.rs: End-to-end reverse compilation pipeline tests
//
// Exercises the full RC pipeline: raw AArch64 bytes -> disassemble -> lift -> VCgen -> decompile.
// Uses Lifter::new() with pre-extracted boundaries (no Mach-O or special features).
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#![allow(rustc::default_hash_types, rustc::potential_query_instability)]

use trust_decompile::Decompiler;
use trust_lift::cfg::{Cfg, LiftedBlock, LiftedFunction};
use trust_lift::{FunctionBoundary, Lifter};
use trust_types::{
    BasicBlock, BinOp, BlockId, LocalDecl, Operand, Place, Rvalue, SourceSpan, Statement,
    Terminator, Ty, VcKind, VerifiableBody,
};
use trust_vcgen::lift_adapter;

// ---------------------------------------------------------------------------
// AArch64 instruction encodings (little-endian)
// ---------------------------------------------------------------------------

/// ADD X0, X0, X1 — encoding: 0x8B010000
const AARCH64_ADD_X0_X0_X1: [u8; 4] = [0x00, 0x00, 0x01, 0x8B];

/// RET (X30) — encoding: 0xD65F03C0
const AARCH64_RET: [u8; 4] = [0xC0, 0x03, 0x5F, 0xD6];

/// SUB X0, X0, X1 — encoding: 0xCB010000
const AARCH64_SUB_X0_X0_X1: [u8; 4] = [0x00, 0x00, 0x01, 0xCB];

// ---------------------------------------------------------------------------
// 1. Full Lifter pipeline: raw bytes -> decode -> CFG -> SSA -> tMIR -> VCs
// ---------------------------------------------------------------------------

#[test]
fn test_rc_pipeline_lifter_add_ret() {
    // Build a minimal "function" from raw AArch64 bytes: ADD X0,X0,X1; RET
    let mut code = Vec::new();
    code.extend_from_slice(&AARCH64_ADD_X0_X0_X1);
    code.extend_from_slice(&AARCH64_RET);

    let text_base: u64 = 0x1000;
    let text_size = code.len() as u64;

    // The binary IS the text section (text_file_offset = 0).
    let boundary = FunctionBoundary {
        name: "add_func".to_string(),
        start: text_base,
        size: text_size,
    };

    let lifter = Lifter::new(vec![boundary], text_base, text_size, 0);

    // Verify the lifter knows about our function.
    assert_eq!(lifter.functions().len(), 1);
    assert_eq!(lifter.functions()[0].name, "add_func");

    // Lift the function from raw bytes.
    let lifted = lifter
        .lift_function(&code, text_base)
        .expect("lifting ADD+RET should succeed");

    // Verify LiftedFunction structure.
    assert_eq!(lifted.name, "add_func");
    assert_eq!(lifted.entry_point, text_base);
    assert!(!lifted.cfg.blocks.is_empty(), "CFG should have at least one block");
    assert!(
        lifted.cfg.blocks.iter().any(|b| b.is_return),
        "CFG should contain a return block"
    );
    assert!(!lifted.tmir_body.blocks.is_empty(), "tMIR body should have blocks");
    assert!(lifted.ssa.is_some(), "SSA should be constructed");

    // Stage: Generate VCs from lifted function.
    let vcs = lift_adapter::generate_binary_vcs(&lifted);
    // ADD on registers produces at least a stack-pointer VC (from return block).
    assert!(
        !vcs.is_empty(),
        "binary VCs should be non-empty (at minimum stack discipline VC)"
    );
    // All VCs should reference our function name.
    for vc in &vcs {
        assert_eq!(vc.function, "add_func");
    }

    // Stage: Convert to VerifiableFunction for decompiler.
    let verifiable = lift_adapter::lift_to_verifiable(&lifted);
    assert_eq!(verifiable.name, "add_func");
    assert_eq!(verifiable.def_path, "binary::add_func");
    assert_eq!(verifiable.body.blocks.len(), lifted.tmir_body.blocks.len());

    // Stage: Decompile to Rust source.
    let decompiler = Decompiler::default();
    let decompiled = decompiler.decompile(&verifiable);
    // Decompilation may succeed or fail depending on the tMIR shape from semantic lift.
    // Either way, the pipeline should not panic — we verify it completes.
    match decompiled {
        Ok(result) => {
            assert!(!result.source.is_empty(), "decompiled source should be non-empty");
            assert!(result.confidence > 0.0, "confidence should be positive");
        }
        Err(e) => {
            // Decompilation failure on raw lifted binary code is acceptable at this stage.
            // The important thing is the pipeline ran without panicking.
            eprintln!("Decompilation returned error (acceptable for raw binary lift): {e}");
        }
    }
}

#[test]
fn test_rc_pipeline_lifter_sub_ret() {
    // SUB X0,X0,X1; RET
    let mut code = Vec::new();
    code.extend_from_slice(&AARCH64_SUB_X0_X0_X1);
    code.extend_from_slice(&AARCH64_RET);

    let text_base: u64 = 0x2000;
    let text_size = code.len() as u64;

    let boundary = FunctionBoundary {
        name: "sub_func".to_string(),
        start: text_base,
        size: text_size,
    };

    let lifter = Lifter::new(vec![boundary], text_base, text_size, 0);
    let lifted = lifter
        .lift_function(&code, text_base)
        .expect("lifting SUB+RET should succeed");

    assert_eq!(lifted.name, "sub_func");
    assert!(lifted.cfg.blocks.iter().any(|b| b.is_return));

    // VCs should include stack discipline.
    let vcs = lift_adapter::generate_binary_vcs(&lifted);
    let sp_vcs: Vec<_> = vcs
        .iter()
        .filter(|vc| {
            matches!(&vc.kind, VcKind::Assertion { message } if message.contains("stack pointer"))
        })
        .collect();
    assert!(
        !sp_vcs.is_empty(),
        "should produce stack pointer restoration VC for return block"
    );
}

// ---------------------------------------------------------------------------
// 2. Direct LiftedFunction -> VCs -> Decompile (no real binary needed)
// ---------------------------------------------------------------------------

/// Build a synthetic LiftedFunction representing `add_two(x: u64, y: u64) -> u64`.
fn synthetic_add_lifted() -> LiftedFunction {
    let mut cfg = Cfg::new();
    cfg.add_block(LiftedBlock {
        id: 0,
        start_addr: 0x4000,
        instructions: vec![],
        successors: vec![],
        is_return: true,
    });

    let body = VerifiableBody {
        locals: vec![
            LocalDecl { index: 0, ty: Ty::Int { width: 64, signed: false }, name: Some("_result".into()) },
            LocalDecl { index: 1, ty: Ty::Int { width: 64, signed: false }, name: Some("x".into()) },
            LocalDecl { index: 2, ty: Ty::Int { width: 64, signed: false }, name: Some("y".into()) },
            LocalDecl { index: 3, ty: Ty::Int { width: 64, signed: false }, name: None },
        ],
        blocks: vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![
                Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Add,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: SourceSpan {
                        file: "binary:0x4000".to_string(),
                        line_start: 0,
                        col_start: 0,
                        line_end: 0,
                        col_end: 0,
                    },
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
        return_ty: Ty::Int { width: 64, signed: false },
    };

    LiftedFunction {
        name: "add_two".to_string(),
        entry_point: 0x4000,
        cfg,
        tmir_body: body,
        ssa: None,
        annotations: vec![],
    }
}

#[test]
fn test_rc_pipeline_synthetic_vcgen_and_decompile() {
    let lifted = synthetic_add_lifted();

    // Stage 1: Generate VCs.
    let vcs = lift_adapter::generate_binary_vcs(&lifted);
    assert!(!vcs.is_empty(), "should produce VCs for Add operation");

    // Should include ArithmeticOverflow for the Add.
    let overflow_vcs: Vec<_> = vcs
        .iter()
        .filter(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { .. }))
        .collect();
    assert!(
        !overflow_vcs.is_empty(),
        "should produce ArithmeticOverflow VC for unsigned Add"
    );

    // Should include stack discipline VC (from Return terminator).
    let sp_vcs: Vec<_> = vcs
        .iter()
        .filter(|vc| {
            matches!(&vc.kind, VcKind::Assertion { message } if message.contains("stack pointer"))
        })
        .collect();
    assert!(
        !sp_vcs.is_empty(),
        "should produce stack pointer VC for Return"
    );

    // All VCs reference the function.
    for vc in &vcs {
        assert_eq!(vc.function, "add_two");
    }

    // Stage 2: Convert to VerifiableFunction.
    let verifiable = lift_adapter::lift_to_verifiable(&lifted);
    assert_eq!(verifiable.name, "add_two");
    assert_eq!(verifiable.body.arg_count, 2);

    // Stage 3: Decompile.
    let decompiler = Decompiler::default();
    let result = decompiler.decompile(&verifiable).expect("decompile should succeed");
    assert_eq!(result.name, "add_two");
    assert!(result.source.contains("unsafe fn add_two"), "source should contain function name");
    assert!(result.source.contains("x: u64"), "source should contain parameter x");
    assert!(result.source.contains("y: u64"), "source should contain parameter y");
    assert!(result.source.contains("-> u64"), "source should contain return type");
    assert!(result.confidence > 0.0, "confidence should be positive");
}

#[test]
fn test_rc_pipeline_synthetic_decompile_module() {
    let lifted = synthetic_add_lifted();
    let verifiable = lift_adapter::lift_to_verifiable(&lifted);

    let decompiler = Decompiler::default();
    let module = decompiler.decompile_module("binary_module", &[verifiable]);

    assert_eq!(module.name, "binary_module");
    assert_eq!(module.functions.len(), 1);
    assert_eq!(module.functions[0].name, "add_two");

    let source = module.to_source();
    assert!(source.contains("// Decompiled module: binary_module"));
    assert!(source.contains("unsafe fn add_two"));
}

// ---------------------------------------------------------------------------
// 3. Pipeline with router integration
// ---------------------------------------------------------------------------

#[test]
fn test_rc_pipeline_vcgen_to_router() {
    let lifted = synthetic_add_lifted();
    let vcs = lift_adapter::generate_binary_vcs(&lifted);

    // Route VCs through the mock backend.
    let router = trust_router::Router::new();
    let results = router.verify_all(&vcs);

    assert_eq!(results.len(), vcs.len());
    for (vc, _result) in &results {
        assert_eq!(vc.function, "add_two");
    }

    // Build a report.
    let report = trust_report::build_json_report("binary_crate", &results);
    assert_eq!(report.crate_name, "binary_crate");
    assert!(report.summary.total_obligations >= 1);
    assert!(
        report.functions.iter().any(|f| f.function == "add_two"),
        "report should contain add_two"
    );

    // Verify text summary works.
    let text = trust_report::format_json_summary(&report);
    assert!(text.contains("add_two"), "text summary should mention add_two");
}

// ---------------------------------------------------------------------------
// 4. Error cases
// ---------------------------------------------------------------------------

#[test]
fn test_rc_pipeline_lifter_entry_out_of_bounds() {
    let code = [0u8; 8];
    let boundary = FunctionBoundary {
        name: "oob_func".to_string(),
        start: 0x1000,
        size: 8,
    };
    let lifter = Lifter::new(vec![boundary], 0x1000, 8, 0);

    // Entry outside text section should fail.
    let result = lifter.lift_function(&code, 0x5000);
    assert!(result.is_err(), "out-of-bounds entry should produce error");
}

#[test]
fn test_rc_pipeline_empty_lifted_decompile_fails() {
    // A LiftedFunction with empty tMIR body should fail decompilation.
    let mut cfg = Cfg::new();
    cfg.add_block(LiftedBlock {
        id: 0,
        start_addr: 0x5000,
        instructions: vec![],
        successors: vec![],
        is_return: true,
    });

    let lifted = LiftedFunction {
        name: "empty_fn".to_string(),
        entry_point: 0x5000,
        cfg,
        tmir_body: VerifiableBody {
            locals: vec![],
            blocks: vec![],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        ssa: None,
        annotations: vec![],
    };

    let verifiable = lift_adapter::lift_to_verifiable(&lifted);
    let decompiler = Decompiler::default();
    let result = decompiler.decompile(&verifiable);
    assert!(result.is_err(), "empty body should fail decompilation");
}
