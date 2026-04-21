// trust-integration-tests/tests/decompile_pipeline.rs: Decompilation pipeline end-to-end tests
//
// Exercises the full decompilation pipeline:
//   AbstractInsn sequence -> lift_to_mir() -> VerifiableFunction
//   -> generate_vcs() -> Decompiler::decompile() -> DecompiledFunction with Rust source
//
// Part of #816: Decompilation pipeline end-to-end test
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#![allow(rustc::default_hash_types, rustc::potential_query_instability)]

use trust_decompile::Decompiler;
use trust_types::{BinOp, Formula, Sort};
use trust_vcgen::{
    AbstractInsn, AbstractOp, AbstractRegister, AbstractValue, LiftedProgram, MemoryAccess,
    generate_vcs, lift_to_mir,
};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn reg(id: u16, width: u32) -> AbstractRegister {
    AbstractRegister { id, name: format!("r{id}"), width }
}

fn insn(address: u64, op: AbstractOp) -> AbstractInsn {
    AbstractInsn { address, op, size: 4 }
}

// ---------------------------------------------------------------------------
// Test 1: Simple addition — load two args, add, return
// ---------------------------------------------------------------------------

#[test]
fn test_decompile_pipeline_simple_addition() {
    // Construct: r2 = r0 + r1; return r2
    let program = LiftedProgram {
        instructions: vec![
            insn(
                0x1000,
                AbstractOp::BinArith {
                    dst: 2,
                    op: BinOp::Add,
                    lhs: AbstractValue::Register(0),
                    rhs: AbstractValue::Register(1),
                },
            ),
            insn(0x1004, AbstractOp::Return { value: Some(AbstractValue::Register(2)) }),
        ],
        entry_point: 0x1000,
        registers: vec![reg(0, 32), reg(1, 32), reg(2, 32)],
    };

    // Stage 1: Lift to VerifiableFunction
    let func = lift_to_mir(&program).expect("lift should succeed");
    assert!(!func.body.blocks.is_empty(), "lifted function should have blocks");
    assert_eq!(func.body.arg_count, 3, "3 registers = 3 args in lifted function");

    // Stage 2: Generate VCs (overflow check for addition)
    let vcs = generate_vcs(&func);
    // Addition of two registers should produce at least an overflow VC
    assert!(!vcs.is_empty(), "addition should produce VCs (overflow check)");

    // Stage 3: Decompile to Rust source
    let decompiler = Decompiler::default();
    let decompiled = decompiler.decompile(&func).expect("decompile should succeed");

    // Verify the decompiled output contains addition-related code
    assert!(!decompiled.source.is_empty(), "decompiled source should not be empty");
    assert!(decompiled.confidence > 0.0, "confidence should be positive");
    // The source should be a function definition
    assert!(
        decompiled.source.contains("fn "),
        "decompiled source should contain a function definition: {}",
        decompiled.source,
    );
}

// ---------------------------------------------------------------------------
// Test 2: Conditional branch — compare, branch-if, two return paths
// ---------------------------------------------------------------------------

#[test]
fn test_decompile_pipeline_branch() {
    // Construct: if r0 then return 1 else return 0
    let program = LiftedProgram {
        instructions: vec![
            insn(
                0x2000,
                AbstractOp::CondBranch {
                    cond: AbstractValue::Register(0),
                    true_target: 0x2008,
                    false_target: 0x2010,
                },
            ),
            insn(
                0x2008,
                AbstractOp::Return { value: Some(AbstractValue::Formula(Formula::Int(1))) },
            ),
            insn(
                0x2010,
                AbstractOp::Return { value: Some(AbstractValue::Formula(Formula::Int(0))) },
            ),
        ],
        entry_point: 0x2000,
        registers: vec![reg(0, 1)],
    };

    // Stage 1: Lift
    let func = lift_to_mir(&program).expect("lift should succeed");
    assert_eq!(func.body.blocks.len(), 3, "branch program should have 3 blocks");

    // Stage 2: VCs (branches don't necessarily produce overflow VCs, but pipeline should work)
    let _vcs = generate_vcs(&func);

    // Stage 3: Decompile
    let decompiler = Decompiler::default();
    let decompiled = decompiler.decompile(&func).expect("decompile should succeed");

    assert!(!decompiled.source.is_empty(), "decompiled source should not be empty");
    assert!(
        decompiled.source.contains("fn "),
        "decompiled source should contain a function definition: {}",
        decompiled.source,
    );
    // The branching structure should appear somehow in the output (match, if, or multiple blocks)
    let has_branch_structure = decompiled.source.contains("match")
        || decompiled.source.contains("if ")
        || decompiled.source.contains("bb1")
        || decompiled.source.contains("bb2");
    assert!(
        has_branch_structure,
        "decompiled source should reflect branching structure: {}",
        decompiled.source,
    );
}

// ---------------------------------------------------------------------------
// Test 3: Linear arithmetic sequence — add, sub, mul in a straight line
// ---------------------------------------------------------------------------

#[test]
fn test_decompile_pipeline_linear_arithmetic() {
    // Construct: r2 = r0 + r1; r3 = r2 - r0; r4 = r3 * r1; return r4
    let program = LiftedProgram {
        instructions: vec![
            insn(
                0x3000,
                AbstractOp::BinArith {
                    dst: 2,
                    op: BinOp::Add,
                    lhs: AbstractValue::Register(0),
                    rhs: AbstractValue::Register(1),
                },
            ),
            insn(
                0x3004,
                AbstractOp::BinArith {
                    dst: 3,
                    op: BinOp::Sub,
                    lhs: AbstractValue::Register(2),
                    rhs: AbstractValue::Register(0),
                },
            ),
            insn(
                0x3008,
                AbstractOp::BinArith {
                    dst: 4,
                    op: BinOp::Mul,
                    lhs: AbstractValue::Register(3),
                    rhs: AbstractValue::Register(1),
                },
            ),
            insn(0x300C, AbstractOp::Return { value: Some(AbstractValue::Register(4)) }),
        ],
        entry_point: 0x3000,
        registers: vec![reg(0, 64), reg(1, 64), reg(2, 64), reg(3, 64), reg(4, 64)],
    };

    // Stage 1: Lift
    let func = lift_to_mir(&program).expect("lift should succeed");
    assert_eq!(func.body.blocks.len(), 1, "linear program should have 1 block");

    // Stage 2: VCs (multiple arithmetic ops should generate multiple overflow VCs)
    let vcs = generate_vcs(&func);
    assert!(vcs.len() >= 2, "linear arithmetic should produce multiple VCs, got {}", vcs.len());

    // Stage 3: Decompile
    let decompiler = Decompiler::default();
    let decompiled = decompiler.decompile(&func).expect("decompile should succeed");

    assert!(!decompiled.source.is_empty(), "decompiled source should not be empty");
    assert!(
        decompiled.source.contains("fn "),
        "decompiled source should contain a function definition: {}",
        decompiled.source,
    );
    assert!(decompiled.confidence > 0.0, "confidence should be positive");
}

// ---------------------------------------------------------------------------
// Test 4: Full pipeline with discharge — VCs get abstract-interpretation discharge
// ---------------------------------------------------------------------------

#[test]
fn test_decompile_pipeline_with_discharge() {
    // Simple add with known-safe constants: discharge should handle some VCs
    let program = LiftedProgram {
        instructions: vec![
            insn(
                0x4000,
                AbstractOp::BinArith {
                    dst: 2,
                    op: BinOp::Add,
                    lhs: AbstractValue::Register(0),
                    rhs: AbstractValue::Register(1),
                },
            ),
            insn(0x4004, AbstractOp::Return { value: Some(AbstractValue::Register(2)) }),
        ],
        entry_point: 0x4000,
        registers: vec![reg(0, 32), reg(1, 32), reg(2, 32)],
    };

    // Lift
    let func = lift_to_mir(&program).expect("lift should succeed");

    // Use generate_vcs_with_discharge for abstract-interpretation pass
    let (solver_vcs, discharged) = trust_vcgen::generate_vcs_with_discharge(&func);

    // Total VCs should equal solver_vcs + discharged
    let total = solver_vcs.len() + discharged.len();
    assert!(total > 0, "should produce at least one VC");

    // Decompile regardless of discharge results
    let decompiler = Decompiler::default();
    let decompiled = decompiler.decompile(&func).expect("decompile should succeed");
    assert!(
        decompiled.source.contains("fn "),
        "decompiled source should contain function: {}",
        decompiled.source,
    );
}

// ---------------------------------------------------------------------------
// Test 5: Decompile with memory access (load/store round-trip)
// ---------------------------------------------------------------------------

#[test]
fn test_decompile_pipeline_memory_access() {
    let pointer = Formula::Var("ptr".to_string(), Sort::Int);
    let program = LiftedProgram {
        instructions: vec![
            insn(
                0x5000,
                AbstractOp::Load {
                    dst: 0,
                    access: MemoryAccess::Read { addr: pointer.clone(), size: 4 },
                },
            ),
            insn(
                0x5004,
                AbstractOp::BinArith {
                    dst: 1,
                    op: BinOp::Add,
                    lhs: AbstractValue::Register(0),
                    rhs: AbstractValue::Formula(Formula::Int(1)),
                },
            ),
            insn(
                0x5008,
                AbstractOp::Store {
                    access: MemoryAccess::Write {
                        addr: pointer,
                        size: 4,
                        value: Formula::Var("r1".to_string(), Sort::Int),
                    },
                },
            ),
            insn(0x500C, AbstractOp::Return { value: Some(AbstractValue::Register(1)) }),
        ],
        entry_point: 0x5000,
        registers: vec![reg(0, 32), reg(1, 32)],
    };

    // Lift
    let func = lift_to_mir(&program).expect("lift should succeed");
    assert_eq!(func.body.blocks.len(), 1);

    // VCs
    let vcs = generate_vcs(&func);
    assert!(!vcs.is_empty(), "memory + arithmetic should generate VCs");

    // Decompile
    let decompiler = Decompiler::default();
    let decompiled = decompiler.decompile(&func).expect("decompile should succeed");
    assert!(
        decompiled.source.contains("fn "),
        "should produce a valid function: {}",
        decompiled.source,
    );
}
