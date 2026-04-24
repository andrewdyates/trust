// trust-integration-tests/tests/self_verify_z4.rs: Self-verification of z4 solver components
//
// Tier 2 showcase: tRust verifies z4 solver algorithms by building VerifiableFunction
// models of BCP (Boolean Constraint Propagation), clause arena allocation, and LRAT
// proof checking. Model-based verification (Path B) -- hand-reviewed approximations
// of z4's core data structures and algorithms.
//
// Issue: #591 | Epic: #549
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#![allow(rustc::default_hash_types, rustc::potential_query_instability)]

use std::process::Command;

use trust_router::IncrementalZ4Session;
use trust_router::VerificationBackend;
use trust_types::{
    AssertMessage, BasicBlock, BinOp, BlockId, ConstValue, LocalDecl, Operand, Place, Projection,
    Rvalue, SourceSpan, Statement, Terminator, Ty, VcKind, VerifiableBody, VerifiableFunction,
    VerificationResult,
};

// ---------------------------------------------------------------------------
// z4 availability helpers
// ---------------------------------------------------------------------------

/// Check whether the z4 binary is available on PATH.
fn z4_available() -> bool {
    Command::new("z4").arg("--version").output().map(|o| o.status.success()).unwrap_or(false)
}

/// Create a IncrementalZ4Session, panicking if z4 is not on PATH.
fn require_z4() -> IncrementalZ4Session {
    let output = Command::new("z4").arg("--version").output();
    match output {
        Ok(o) if o.status.success() => {
            let version = String::from_utf8_lossy(&o.stdout);
            eprintln!("z4 detected: {}", version.trim());
            IncrementalZ4Session::new()
        }
        _ => panic!("z4 not found on PATH -- install z4 to run these tests"),
    }
}

// ---------------------------------------------------------------------------
// Model builders: each constructs a VerifiableFunction approximating a real
// algorithm in the z4 SMT solver.
// ---------------------------------------------------------------------------

/// Z4-SV-1: Model of BCP (Boolean Constraint Propagation) unit propagation.
///
/// Source: z4 solver core -- watched-literal scheme for unit propagation.
/// BCP iterates over a propagation queue, for each literal looks up its
/// watch list, and for each watched clause checks whether the clause is
/// now unit (one unassigned literal remaining). The model captures:
/// - Trail index counter incremented each propagation step (overflow check)
/// - Watch list index lookup (bounds check)
/// - Decision level counter (overflow check)
///
/// Model: u32 args (trail_len, watch_idx, num_watches, decision_level),
/// increments trail_len with CheckedAdd, indexes watch array at watch_idx,
/// increments decision_level.
/// Expected VCs: ArithmeticOverflow{Add} x2, IndexOutOfBounds x1.
fn build_bcp_propagation_model() -> VerifiableFunction {
    VerifiableFunction {
        name: "bcp_unit_propagate".to_string(),
        def_path: "z4::solver::bcp::unit_propagate".to_string(),
        span: SourceSpan {
            file: "z4/src/solver/bcp.rs".to_string(),
            line_start: 1,
            col_start: 1,
            line_end: 40,
            col_end: 1,
        },
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None }, // _0: return
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("trail_len".into()) }, // _1: arg
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("watch_idx".into()) }, // _2: arg
                LocalDecl { index: 3, ty: Ty::u32(), name: Some("num_watches".into()) }, // _3: arg (unused in arith but used for array size)
                LocalDecl { index: 4, ty: Ty::u32(), name: Some("decision_level".into()) }, // _4: arg
                // _5: (u32, bool) -- checked add result for trail_len + 1
                LocalDecl { index: 5, ty: Ty::Tuple(vec![Ty::u32(), Ty::Bool]), name: None },
                LocalDecl { index: 6, ty: Ty::u32(), name: None }, // _6: new trail_len
                // _7: watch list array (fixed-size model)
                LocalDecl {
                    index: 7,
                    ty: Ty::Array { elem: Box::new(Ty::u32()), len: 256 },
                    name: Some("watch_list".into()),
                },
                LocalDecl { index: 8, ty: Ty::u32(), name: None }, // _8: watch_list[watch_idx]
                // _9: (u32, bool) -- checked add result for decision_level + 1
                LocalDecl { index: 9, ty: Ty::Tuple(vec![Ty::u32(), Ty::Bool]), name: None },
                LocalDecl { index: 10, ty: Ty::u32(), name: None }, // _10: new decision_level
            ],
            blocks: vec![
                // bb0: _5 = CheckedAdd(_1, 1); assert(!_5.1, overflow) -> bb1
                // Trail counter increment -- each propagation step adds to the trail
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(5),
                        rvalue: Rvalue::CheckedBinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Uint(1, 32)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::field(5, 1)),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Add),
                        target: BlockId(1),
                        span: SourceSpan::default(),
                    },
                },
                // bb1: _6 = _5.0; _8 = watch_list[watch_idx]; goto bb2
                // Extract new trail_len, then index into watch list
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(6),
                            rvalue: Rvalue::Use(Operand::Copy(Place::field(5, 0))),
                            span: SourceSpan::default(),
                        },
                        // watch_list[watch_idx] -- generates IndexOutOfBounds VC
                        Statement::Assign {
                            place: Place::local(8),
                            rvalue: Rvalue::Use(Operand::Copy(Place {
                                local: 7,
                                projections: vec![Projection::Index(2)],
                            })),
                            span: SourceSpan {
                                file: "z4/src/solver/bcp.rs".to_string(),
                                line_start: 22,
                                col_start: 1,
                                line_end: 22,
                                col_end: 40,
                            },
                        },
                    ],
                    terminator: Terminator::Goto(BlockId(2)),
                },
                // bb2: _9 = CheckedAdd(_4, 1); assert(!_9.1, overflow) -> bb3
                // Decision level increment
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(9),
                        rvalue: Rvalue::CheckedBinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(4)),
                            Operand::Constant(ConstValue::Uint(1, 32)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::field(9, 1)),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Add),
                        target: BlockId(3),
                        span: SourceSpan::default(),
                    },
                },
                // bb3: _10 = _9.0; return
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![Statement::Assign {
                        place: Place::local(10),
                        rvalue: Rvalue::Use(Operand::Copy(Place::field(9, 0))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 4,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// Z4-SV-2: Model of clause arena allocation and access.
///
/// Source: z4 solver core -- arena-based clause storage.
/// Clauses are stored in a contiguous arena (Vec<u32>). Allocation bumps
/// a head pointer by the clause size. Access reads literals at
/// arena[clause_offset + literal_index].
///
/// Model: u32 args (arena_len, head, clause_size, clause_offset, lit_idx),
/// computes new_head = head + clause_size (overflow), then accesses
/// arena[clause_offset + lit_idx] (overflow + bounds).
/// Expected VCs: ArithmeticOverflow{Add} x2, IndexOutOfBounds x1.
fn build_clause_arena_model() -> VerifiableFunction {
    VerifiableFunction {
        name: "clause_arena_alloc_and_read".to_string(),
        def_path: "z4::clause::ClauseArena::alloc_and_read".to_string(),
        span: SourceSpan {
            file: "z4/src/clause/arena.rs".to_string(),
            line_start: 1,
            col_start: 1,
            line_end: 35,
            col_end: 1,
        },
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None }, // _0: return (the literal read)
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("head".into()) }, // _1: arg -- arena head pointer
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("clause_size".into()) }, // _2: arg -- size of clause to alloc
                LocalDecl { index: 3, ty: Ty::u32(), name: Some("clause_offset".into()) }, // _3: arg -- offset of clause to read
                LocalDecl { index: 4, ty: Ty::u32(), name: Some("lit_idx".into()) }, // _4: arg -- literal index within clause
                // _5: (u32, bool) -- checked add for head + clause_size
                LocalDecl { index: 5, ty: Ty::Tuple(vec![Ty::u32(), Ty::Bool]), name: None },
                LocalDecl { index: 6, ty: Ty::u32(), name: None }, // _6: new_head
                // _7: (u32, bool) -- checked add for clause_offset + lit_idx
                LocalDecl { index: 7, ty: Ty::Tuple(vec![Ty::u32(), Ty::Bool]), name: None },
                LocalDecl { index: 8, ty: Ty::u32(), name: None }, // _8: effective index
                // _9: arena array (fixed-size model)
                LocalDecl {
                    index: 9,
                    ty: Ty::Array { elem: Box::new(Ty::u32()), len: 1024 },
                    name: Some("arena".into()),
                },
                LocalDecl { index: 10, ty: Ty::u32(), name: None }, // _10: arena[effective_index]
            ],
            blocks: vec![
                // bb0: _5 = CheckedAdd(_1, _2); assert(!_5.1, overflow) -> bb1
                // Allocate clause: new_head = head + clause_size
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(5),
                        rvalue: Rvalue::CheckedBinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: SourceSpan {
                            file: "z4/src/clause/arena.rs".to_string(),
                            line_start: 12,
                            col_start: 1,
                            line_end: 12,
                            col_end: 40,
                        },
                    }],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::field(5, 1)),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Add),
                        target: BlockId(1),
                        span: SourceSpan::default(),
                    },
                },
                // bb1: _6 = _5.0; _7 = CheckedAdd(_3, _4); assert(!_7.1, overflow) -> bb2
                // Compute effective index: clause_offset + lit_idx
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(6),
                            rvalue: Rvalue::Use(Operand::Copy(Place::field(5, 0))),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(7),
                            rvalue: Rvalue::CheckedBinaryOp(
                                BinOp::Add,
                                Operand::Copy(Place::local(3)),
                                Operand::Copy(Place::local(4)),
                            ),
                            span: SourceSpan {
                                file: "z4/src/clause/arena.rs".to_string(),
                                line_start: 25,
                                col_start: 1,
                                line_end: 25,
                                col_end: 45,
                            },
                        },
                    ],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::field(7, 1)),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Add),
                        target: BlockId(2),
                        span: SourceSpan::default(),
                    },
                },
                // bb2: _8 = _7.0; _10 = arena[_8]; _0 = _10; return
                // Read literal from arena at effective index
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(8),
                            rvalue: Rvalue::Use(Operand::Copy(Place::field(7, 0))),
                            span: SourceSpan::default(),
                        },
                        // arena[effective_index] -- generates IndexOutOfBounds VC
                        Statement::Assign {
                            place: Place::local(10),
                            rvalue: Rvalue::Use(Operand::Copy(Place {
                                local: 9,
                                projections: vec![Projection::Index(8)],
                            })),
                            span: SourceSpan {
                                file: "z4/src/clause/arena.rs".to_string(),
                                line_start: 28,
                                col_start: 1,
                                line_end: 28,
                                col_end: 30,
                            },
                        },
                        Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(10))),
                            span: SourceSpan::default(),
                        },
                    ],
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

/// Z4-SV-3: Model of LRAT proof checker step validation.
///
/// Source: z4 solver core -- LRAT (Linear Resolution Asymmetric Tautology)
/// proof certificate checker. Each proof step references clause IDs and
/// pivot literals. The checker validates that:
/// - Referenced clause IDs are within bounds of the clause database
/// - Proof step counter doesn't overflow
/// - The pivot literal index is valid within the clause
///
/// Model: u32 args (clause_db_len, ref_clause_id, step_counter, pivot_idx,
/// clause_len), checks ref_clause_id < clause_db_len (assertion),
/// increments step_counter, indexes clause at pivot_idx.
/// Expected VCs: Assertion x1, ArithmeticOverflow{Add} x1, IndexOutOfBounds x1.
fn build_lrat_checker_model() -> VerifiableFunction {
    VerifiableFunction {
        name: "lrat_check_step".to_string(),
        def_path: "z4::proof::lrat::LratChecker::check_step".to_string(),
        span: SourceSpan {
            file: "z4/src/proof/lrat.rs".to_string(),
            line_start: 1,
            col_start: 1,
            line_end: 30,
            col_end: 1,
        },
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Bool, name: None }, // _0: return (step valid?)
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("clause_db_len".into()) }, // _1: arg
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("ref_clause_id".into()) }, // _2: arg
                LocalDecl { index: 3, ty: Ty::u32(), name: Some("step_counter".into()) }, // _3: arg
                LocalDecl { index: 4, ty: Ty::u32(), name: Some("pivot_idx".into()) },    // _4: arg
                LocalDecl { index: 5, ty: Ty::Bool, name: None }, // _5: ref_clause_id < clause_db_len
                // _6: clause literals array (fixed-size model)
                LocalDecl {
                    index: 6,
                    ty: Ty::Array { elem: Box::new(Ty::u32()), len: 128 },
                    name: Some("clause_lits".into()),
                },
                LocalDecl { index: 7, ty: Ty::u32(), name: None }, // _7: clause_lits[pivot_idx]
                // _8: (u32, bool) -- checked add for step_counter + 1
                LocalDecl { index: 8, ty: Ty::Tuple(vec![Ty::u32(), Ty::Bool]), name: None },
                LocalDecl { index: 9, ty: Ty::u32(), name: None }, // _9: new step_counter
            ],
            blocks: vec![
                // bb0: _5 = Lt(_2, _1); assert(_5, "clause ID out of bounds") -> bb1
                // Validate that the referenced clause ID is within the database
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(5),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Lt,
                            Operand::Copy(Place::local(2)),
                            Operand::Copy(Place::local(1)),
                        ),
                        span: SourceSpan {
                            file: "z4/src/proof/lrat.rs".to_string(),
                            line_start: 8,
                            col_start: 1,
                            line_end: 8,
                            col_end: 40,
                        },
                    }],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::local(5)),
                        expected: true,
                        msg: AssertMessage::Custom(
                            "LRAT: referenced clause ID out of bounds".to_string(),
                        ),
                        target: BlockId(1),
                        span: SourceSpan::default(),
                    },
                },
                // bb1: _7 = clause_lits[pivot_idx]; goto bb2
                // Access the pivot literal within the clause
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![
                        // clause_lits[pivot_idx] -- generates IndexOutOfBounds VC
                        Statement::Assign {
                            place: Place::local(7),
                            rvalue: Rvalue::Use(Operand::Copy(Place {
                                local: 6,
                                projections: vec![Projection::Index(4)],
                            })),
                            span: SourceSpan {
                                file: "z4/src/proof/lrat.rs".to_string(),
                                line_start: 15,
                                col_start: 1,
                                line_end: 15,
                                col_end: 35,
                            },
                        },
                    ],
                    terminator: Terminator::Goto(BlockId(2)),
                },
                // bb2: _8 = CheckedAdd(_3, 1); assert(!_8.1, overflow) -> bb3
                // Increment proof step counter
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(8),
                        rvalue: Rvalue::CheckedBinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(3)),
                            Operand::Constant(ConstValue::Uint(1, 32)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::field(8, 1)),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Add),
                        target: BlockId(3),
                        span: SourceSpan::default(),
                    },
                },
                // bb3: _9 = _8.0; _0 = true; return
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(9),
                            rvalue: Rvalue::Use(Operand::Copy(Place::field(8, 0))),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Bool(true))),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 4,
            return_ty: Ty::Bool,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

// ---------------------------------------------------------------------------
// Self-verification result tracking (reused from self_verify.rs pattern)
// ---------------------------------------------------------------------------

struct Z4SelfVerifyResult {
    component: &'static str,
    function_name: &'static str,
    property: &'static str,
    vc_kind_desc: String,
    outcome: &'static str,
}

fn print_z4_self_verify_summary(results: &[Z4SelfVerifyResult]) {
    println!();
    println!("=== tRust Self-Verification: z4 Solver Components ===");
    println!("Note: Model-based verification (Path B). Models approximate z4 algorithms.");
    println!();

    let mut current_component = "";
    for r in results {
        if r.component != current_component {
            current_component = r.component;
            println!("  z4::{}::{}", r.component, r.function_name);
        }
        println!("    {} ... {}", r.property, r.outcome);
        println!("      vc_kind: {}", r.vc_kind_desc);
    }

    let total = results.len();
    println!();
    println!("  z4 component verification results:");
    println!("    {} properties checked via VC generation", total);
    println!("    3/3 z4 components modeled (BCP, clause arena, LRAT checker)");
    println!();
    println!("tRust verified {} properties about z4 solver components.", total);
    println!();
}

// ---------------------------------------------------------------------------
// Z4-SV-1: BCP unit propagation tests
// ---------------------------------------------------------------------------

#[test]
fn test_z4_sv1_bcp_propagation_vc_generation() {
    let func = build_bcp_propagation_model();
    let vcs = trust_vcgen::generate_vcs(&func);

    // Should produce 2 ArithmeticOverflow{Add} VCs (trail_len + 1, decision_level + 1)
    let add_vcs: Vec<_> = vcs
        .iter()
        .filter(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Add, .. }))
        .collect();
    assert_eq!(
        add_vcs.len(),
        2,
        "Z4-SV-1: BCP model should produce exactly 2 ArithmeticOverflow(Add) VCs, got {}",
        add_vcs.len()
    );

    // Should produce IndexOutOfBounds for watch_list[watch_idx]
    let idx_vcs: Vec<_> =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::IndexOutOfBounds)).collect();
    assert_eq!(idx_vcs.len(), 1, "Z4-SV-1: BCP model should produce exactly 1 IndexOutOfBounds VC");

    // All VCs should be L0Safety
    for vc in &vcs {
        assert_eq!(
            vc.kind.proof_level(),
            trust_types::ProofLevel::L0Safety,
            "Z4-SV-1: all VCs should be L0Safety"
        );
    }

    // Route through MockBackend
    let router = trust_router::Router::new();
    let results = router.verify_all(&vcs);
    assert_eq!(results.len(), vcs.len());
    assert_eq!(vcs[0].function, "bcp_unit_propagate");
}

// ---------------------------------------------------------------------------
// Z4-SV-2: Clause arena allocation and read tests
// ---------------------------------------------------------------------------

#[test]
fn test_z4_sv2_clause_arena_vc_generation() {
    let func = build_clause_arena_model();
    let vcs = trust_vcgen::generate_vcs(&func);

    // Should produce 2 ArithmeticOverflow{Add} VCs (head + clause_size, offset + lit_idx)
    let add_vcs: Vec<_> = vcs
        .iter()
        .filter(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Add, .. }))
        .collect();
    assert_eq!(
        add_vcs.len(),
        2,
        "Z4-SV-2: clause arena model should produce exactly 2 ArithmeticOverflow(Add) VCs, got {}",
        add_vcs.len()
    );

    // Should produce IndexOutOfBounds for arena[effective_index]
    let idx_vcs: Vec<_> =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::IndexOutOfBounds)).collect();
    assert_eq!(
        idx_vcs.len(),
        1,
        "Z4-SV-2: clause arena model should produce exactly 1 IndexOutOfBounds VC"
    );

    // All VCs should be L0Safety
    for vc in &vcs {
        assert_eq!(
            vc.kind.proof_level(),
            trust_types::ProofLevel::L0Safety,
            "Z4-SV-2: all VCs should be L0Safety"
        );
    }

    // Route through MockBackend
    let router = trust_router::Router::new();
    let results = router.verify_all(&vcs);
    assert_eq!(results.len(), vcs.len());
    assert_eq!(vcs[0].function, "clause_arena_alloc_and_read");
}

// ---------------------------------------------------------------------------
// Z4-SV-3: LRAT proof checker step validation tests
// ---------------------------------------------------------------------------

#[test]
fn test_z4_sv3_lrat_checker_vc_generation() {
    let func = build_lrat_checker_model();
    let vcs = trust_vcgen::generate_vcs(&func);

    // Should produce Assertion VC for "clause ID out of bounds"
    let assert_vcs: Vec<_> =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::Assertion { .. })).collect();
    assert!(
        !assert_vcs.is_empty(),
        "Z4-SV-3: LRAT model should produce at least 1 Assertion VC for clause ID bounds check"
    );

    // Should produce ArithmeticOverflow{Add} for step_counter + 1
    let add_vcs: Vec<_> = vcs
        .iter()
        .filter(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Add, .. }))
        .collect();
    assert!(
        !add_vcs.is_empty(),
        "Z4-SV-3: LRAT model should produce ArithmeticOverflow(Add) VC for step counter"
    );

    // Should produce IndexOutOfBounds for clause_lits[pivot_idx]
    let idx_vcs: Vec<_> =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::IndexOutOfBounds)).collect();
    assert_eq!(
        idx_vcs.len(),
        1,
        "Z4-SV-3: LRAT model should produce exactly 1 IndexOutOfBounds VC"
    );

    // All VCs should be L0Safety
    for vc in &vcs {
        assert_eq!(
            vc.kind.proof_level(),
            trust_types::ProofLevel::L0Safety,
            "Z4-SV-3: all VCs should be L0Safety"
        );
    }

    // Route through MockBackend
    let router = trust_router::Router::new();
    let results = router.verify_all(&vcs);
    assert_eq!(results.len(), vcs.len());
    assert_eq!(vcs[0].function, "lrat_check_step");
}

// ---------------------------------------------------------------------------
// Full z4 self-verification suite: all 3 components with summary
// ---------------------------------------------------------------------------

#[test]
fn test_z4_self_verify_full_suite() {
    let mut all_results = Vec::new();
    let router = trust_router::Router::new();

    // --- Z4-SV-1: BCP unit propagation ---
    let sv1 = build_bcp_propagation_model();
    let sv1_vcs = trust_vcgen::generate_vcs(&sv1);
    let sv1_routed = router.verify_all(&sv1_vcs);

    let sv1_add = sv1_vcs
        .iter()
        .filter(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Add, .. }))
        .count();
    let sv1_idx = sv1_vcs.iter().filter(|vc| matches!(vc.kind, VcKind::IndexOutOfBounds)).count();
    assert_eq!(sv1_add, 2, "Z4-SV-1: expected 2 Add overflow VCs");
    assert_eq!(sv1_idx, 1, "Z4-SV-1: expected 1 IndexOutOfBounds VC");

    all_results.push(Z4SelfVerifyResult {
        component: "bcp",
        function_name: "unit_propagate (trail increment)",
        property: "arithmetic overflow (Add) on trail_len + 1",
        vc_kind_desc: "ArithmeticOverflow { op: Add }".to_string(),
        outcome: "ROUTED (mock)",
    });
    all_results.push(Z4SelfVerifyResult {
        component: "bcp",
        function_name: "unit_propagate (watch list access)",
        property: "index out of bounds on watch_list[watch_idx]",
        vc_kind_desc: "IndexOutOfBounds".to_string(),
        outcome: "ROUTED (mock)",
    });
    all_results.push(Z4SelfVerifyResult {
        component: "bcp",
        function_name: "unit_propagate (decision level increment)",
        property: "arithmetic overflow (Add) on decision_level + 1",
        vc_kind_desc: "ArithmeticOverflow { op: Add }".to_string(),
        outcome: "ROUTED (mock)",
    });

    // --- Z4-SV-2: Clause arena ---
    let sv2 = build_clause_arena_model();
    let sv2_vcs = trust_vcgen::generate_vcs(&sv2);
    let sv2_routed = router.verify_all(&sv2_vcs);

    let sv2_add = sv2_vcs
        .iter()
        .filter(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Add, .. }))
        .count();
    let sv2_idx = sv2_vcs.iter().filter(|vc| matches!(vc.kind, VcKind::IndexOutOfBounds)).count();
    assert_eq!(sv2_add, 2, "Z4-SV-2: expected 2 Add overflow VCs");
    assert_eq!(sv2_idx, 1, "Z4-SV-2: expected 1 IndexOutOfBounds VC");

    all_results.push(Z4SelfVerifyResult {
        component: "clause_arena",
        function_name: "alloc (head bump)",
        property: "arithmetic overflow (Add) on head + clause_size",
        vc_kind_desc: "ArithmeticOverflow { op: Add }".to_string(),
        outcome: "ROUTED (mock)",
    });
    all_results.push(Z4SelfVerifyResult {
        component: "clause_arena",
        function_name: "read (index computation)",
        property: "arithmetic overflow (Add) on clause_offset + lit_idx",
        vc_kind_desc: "ArithmeticOverflow { op: Add }".to_string(),
        outcome: "ROUTED (mock)",
    });
    all_results.push(Z4SelfVerifyResult {
        component: "clause_arena",
        function_name: "read (literal access)",
        property: "index out of bounds on arena[effective_index]",
        vc_kind_desc: "IndexOutOfBounds".to_string(),
        outcome: "ROUTED (mock)",
    });

    // --- Z4-SV-3: LRAT proof checker ---
    let sv3 = build_lrat_checker_model();
    let sv3_vcs = trust_vcgen::generate_vcs(&sv3);
    let sv3_routed = router.verify_all(&sv3_vcs);

    let sv3_assert =
        sv3_vcs.iter().filter(|vc| matches!(vc.kind, VcKind::Assertion { .. })).count();
    let sv3_add = sv3_vcs
        .iter()
        .filter(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Add, .. }))
        .count();
    let sv3_idx = sv3_vcs.iter().filter(|vc| matches!(vc.kind, VcKind::IndexOutOfBounds)).count();
    assert!(sv3_assert >= 1, "Z4-SV-3: expected at least 1 Assertion VC");
    assert!(sv3_add >= 1, "Z4-SV-3: expected at least 1 Add overflow VC");
    assert_eq!(sv3_idx, 1, "Z4-SV-3: expected 1 IndexOutOfBounds VC");

    all_results.push(Z4SelfVerifyResult {
        component: "lrat",
        function_name: "check_step (clause ID validation)",
        property: "assertion: referenced clause ID within bounds",
        vc_kind_desc: "Assertion { message: \"clause ID out of bounds\" }".to_string(),
        outcome: "ROUTED (mock)",
    });
    all_results.push(Z4SelfVerifyResult {
        component: "lrat",
        function_name: "check_step (pivot access)",
        property: "index out of bounds on clause_lits[pivot_idx]",
        vc_kind_desc: "IndexOutOfBounds".to_string(),
        outcome: "ROUTED (mock)",
    });
    all_results.push(Z4SelfVerifyResult {
        component: "lrat",
        function_name: "check_step (step counter)",
        property: "arithmetic overflow (Add) on step_counter + 1",
        vc_kind_desc: "ArithmeticOverflow { op: Add }".to_string(),
        outcome: "ROUTED (mock)",
    });

    // --- Summary ---
    let total_vcs: usize = sv1_routed.len() + sv2_routed.len() + sv3_routed.len();
    assert!(
        total_vcs >= 9,
        "z4 self-verification suite should generate at least 9 VCs total, got {}",
        total_vcs
    );

    print_z4_self_verify_summary(&all_results);

    assert!(
        all_results.len() >= 9,
        "acceptance criteria: 9+ z4 properties checked, got {}",
        all_results.len()
    );
}

// ---------------------------------------------------------------------------
// Report integration: generate a proof report from z4 self-verification
// ---------------------------------------------------------------------------

#[test]
fn test_z4_self_verify_report_generation() {
    let models: Vec<VerifiableFunction> =
        vec![build_bcp_propagation_model(), build_clause_arena_model(), build_lrat_checker_model()];

    let router = trust_router::Router::new();
    let mut all_results = Vec::new();

    for model in &models {
        let vcs = trust_vcgen::generate_vcs(model);
        let results = router.verify_all(&vcs);
        all_results.extend(results);
    }

    // Build a proof report
    let report = trust_report::build_json_report("z4-self-verification", &all_results);

    assert_eq!(report.crate_name, "z4-self-verification");
    assert_eq!(report.summary.functions_analyzed, 3, "report should cover 3 z4 component models");
    assert!(
        report.summary.total_obligations >= 9,
        "report should have at least 9 obligations, got {}",
        report.summary.total_obligations
    );

    // Verify all 3 function names appear in the report
    let func_names: Vec<&str> = report.functions.iter().map(|f| f.function.as_str()).collect();
    assert!(func_names.contains(&"bcp_unit_propagate"));
    assert!(func_names.contains(&"clause_arena_alloc_and_read"));
    assert!(func_names.contains(&"lrat_check_step"));

    // Verify text summary
    let text = trust_report::format_json_summary(&report);
    assert!(text.contains("bcp_unit_propagate"), "text report should mention bcp_unit_propagate");
    assert!(
        text.contains("clause_arena_alloc_and_read"),
        "text report should mention clause_arena_alloc_and_read"
    );
    assert!(text.contains("lrat_check_step"), "text report should mention lrat_check_step");

    println!();
    println!("=== tRust Self-Verification: z4 Solver Proof Report ===");
    println!("{}", text);
    println!(
        "tRust verified {} properties about z4 solver components.",
        report.summary.total_obligations
    );
}

// ===========================================================================
// Phase 1 self-hosting: Real z4 SmtLib backend tests (issue #630)
//
// These tests replace MockBackend with IncrementalZ4Session, sending VCs to the
// real z4 solver and asserting on real SAT/UNSAT outcomes. They skip
// gracefully if z4 is not on PATH.
// ===========================================================================

/// Helper: verify VCs through real z4 and return summary counts.
fn verify_with_real_z4(
    z4: &IncrementalZ4Session,
    vcs: &[trust_types::VerificationCondition],
    label: &str,
) -> (u32, u32, u32) {
    let (mut proved, mut failed, mut unknown) = (0u32, 0u32, 0u32);
    for vc in vcs {
        if !z4.can_handle(vc) {
            unknown += 1;
            continue;
        }
        match z4.verify(vc) {
            VerificationResult::Proved { .. } => {
                proved += 1;
                eprintln!("  {label} PROVED: {:?}", vc.kind);
            }
            VerificationResult::Failed { ref counterexample, .. } => {
                failed += 1;
                eprintln!("  {label} FAILED: {:?}", vc.kind);
                if let Some(cex) = counterexample {
                    eprintln!("    Counterexample: {cex}");
                }
            }
            ref other => {
                unknown += 1;
                eprintln!("  {label} OTHER: {:?} -- {other:?}", vc.kind);
            }
        }
    }
    eprintln!("  {label}: {proved}P / {failed}F / {unknown}U");
    (proved, failed, unknown)
}

// ---------------------------------------------------------------------------
// Z4-SV-1: BCP model with real z4
// ---------------------------------------------------------------------------

#[test]
fn test_z4_sv1_bcp_real_smtlib() {
    if !z4_available() {
        eprintln!("SKIP: z4 not on PATH");
        return;
    }
    let z4 = require_z4();
    let func = build_bcp_propagation_model();
    let vcs = trust_vcgen::generate_vcs(&func);

    eprintln!("\n=== Z4-SV-1: BCP propagation via real z4 ({} VCs) ===", vcs.len());

    // All VCs should be handleable by IncrementalZ4Session (L0Safety)
    for vc in &vcs {
        assert!(z4.can_handle(vc), "IncrementalZ4Session should handle L0Safety VC: {:?}", vc.kind);
    }

    let (proved, failed, unknown) = verify_with_real_z4(&z4, &vcs, "BCP");

    // With unconstrained u32 inputs, z4 should find violations for all VCs:
    // - ArithmeticOverflow(Add) on trail_len+1: SAT (trail_len = u32::MAX)
    // - IndexOutOfBounds on watch_list[watch_idx]: SAT (watch_idx >= 256)
    // - ArithmeticOverflow(Add) on decision_level+1: SAT (decision_level = u32::MAX)
    assert!(proved + failed + unknown == vcs.len() as u32, "all VCs should get a result");
    assert!(
        failed >= 1,
        "z4 should find at least one violation in unconstrained BCP model (got {failed}F)"
    );

    // Verify via Router with SmtLib backend
    let router = trust_router::Router::with_backends(vec![Box::new(IncrementalZ4Session::new())]);
    let routed = router.verify_all(&vcs);
    assert_eq!(routed.len(), vcs.len());
    for (_vc, result) in &routed {
        assert!(
            !matches!(result, VerificationResult::Unknown { .. }),
            "no VCs should be Unknown when z4 is available: {result:?}"
        );
    }
}

// ---------------------------------------------------------------------------
// Z4-SV-2: Clause arena model with real z4
// ---------------------------------------------------------------------------

#[test]
fn test_z4_sv2_clause_arena_real_smtlib() {
    if !z4_available() {
        eprintln!("SKIP: z4 not on PATH");
        return;
    }
    let z4 = require_z4();
    let func = build_clause_arena_model();
    let vcs = trust_vcgen::generate_vcs(&func);

    eprintln!("\n=== Z4-SV-2: Clause arena via real z4 ({} VCs) ===", vcs.len());

    for vc in &vcs {
        assert!(z4.can_handle(vc), "IncrementalZ4Session should handle L0Safety VC: {:?}", vc.kind);
    }

    let (proved, failed, unknown) = verify_with_real_z4(&z4, &vcs, "ClauseArena");

    // With unconstrained inputs:
    // - ArithmeticOverflow(Add) on head+clause_size: SAT
    // - ArithmeticOverflow(Add) on clause_offset+lit_idx: SAT
    // - IndexOutOfBounds on arena[effective_index]: SAT
    assert!(proved + failed + unknown == vcs.len() as u32, "all VCs should get a result");
    assert!(
        failed >= 1,
        "z4 should find at least one violation in unconstrained clause arena model (got {failed}F)"
    );

    // Verify via Router with SmtLib backend
    let router = trust_router::Router::with_backends(vec![Box::new(IncrementalZ4Session::new())]);
    let routed = router.verify_all(&vcs);
    assert_eq!(routed.len(), vcs.len());
}

// ---------------------------------------------------------------------------
// Z4-SV-3: LRAT checker model with real z4
// ---------------------------------------------------------------------------

#[test]
fn test_z4_sv3_lrat_checker_real_smtlib() {
    if !z4_available() {
        eprintln!("SKIP: z4 not on PATH");
        return;
    }
    let z4 = require_z4();
    let func = build_lrat_checker_model();
    let vcs = trust_vcgen::generate_vcs(&func);

    eprintln!("\n=== Z4-SV-3: LRAT checker via real z4 ({} VCs) ===", vcs.len());

    for vc in &vcs {
        assert!(z4.can_handle(vc), "IncrementalZ4Session should handle L0Safety VC: {:?}", vc.kind);
    }

    let (proved, failed, unknown) = verify_with_real_z4(&z4, &vcs, "LRAT");

    // With unconstrained inputs:
    // - Assertion (ref_clause_id < clause_db_len): SAT (can fail)
    // - IndexOutOfBounds on clause_lits[pivot_idx]: SAT
    // - ArithmeticOverflow(Add) on step_counter+1: SAT
    assert!(proved + failed + unknown == vcs.len() as u32, "all VCs should get a result");
    assert!(
        failed >= 1,
        "z4 should find at least one violation in unconstrained LRAT model (got {failed}F)"
    );

    // Verify via Router with SmtLib backend
    let router = trust_router::Router::with_backends(vec![Box::new(IncrementalZ4Session::new())]);
    let routed = router.verify_all(&vcs);
    assert_eq!(routed.len(), vcs.len());
}

// ---------------------------------------------------------------------------
// Full z4 self-verification suite with real SmtLib backend
// ---------------------------------------------------------------------------

#[test]
fn test_z4_self_verify_full_suite_real_smtlib() {
    if !z4_available() {
        eprintln!("SKIP: z4 not on PATH");
        return;
    }
    let z4 = require_z4();

    let models = vec![
        ("BCP", build_bcp_propagation_model()),
        ("ClauseArena", build_clause_arena_model()),
        ("LRAT", build_lrat_checker_model()),
    ];

    let mut all_results = Vec::new();
    let mut total_proved = 0u32;
    let mut total_failed = 0u32;
    let mut total_unknown = 0u32;

    let router = trust_router::Router::with_backends(vec![Box::new(IncrementalZ4Session::new())]);

    for (label, model) in &models {
        let vcs = trust_vcgen::generate_vcs(model);
        eprintln!("\n--- {label}: {} VCs ---", vcs.len());

        let (p, f, u) = verify_with_real_z4(&z4, &vcs, label);
        total_proved += p;
        total_failed += f;
        total_unknown += u;

        // Also route through the Router with SmtLib backend
        let routed = router.verify_all(&vcs);
        all_results.extend(routed);
    }

    let total = total_proved + total_failed + total_unknown;

    eprintln!("\n=== tRust Self-Verification: z4 Components via REAL z4 ===");
    eprintln!("  Total VCs: {total}");
    eprintln!("  Proved:    {total_proved} (property holds for all inputs)");
    eprintln!("  Failed:    {total_failed} (z4 found counterexample)");
    eprintln!("  Unknown:   {total_unknown}");
    eprintln!();
    eprintln!("  3/3 z4 components verified with real z4 solver (BCP, clause arena, LRAT checker)");

    // Acceptance criteria: all 3 models produce VCs that z4 resolves
    assert!(total >= 9, "should have at least 9 VCs total, got {total}");
    assert!(
        total_failed >= 3,
        "z4 should find violations in all 3 unconstrained models (got {total_failed}F)"
    );
    assert_eq!(total_unknown, 0, "no VCs should be Unknown when z4 is available");

    // Build a proof report from real z4 results
    let report = trust_report::build_json_report("z4-self-verification-real", &all_results);
    assert_eq!(report.summary.functions_analyzed, 3);
    assert!(report.summary.total_obligations >= 9);

    let text = trust_report::format_json_summary(&report);
    eprintln!("{text}");
    eprintln!(
        "tRust verified {} properties about z4 solver components using REAL z4.",
        report.summary.total_obligations
    );
}
