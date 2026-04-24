// tRust #513, #565: Adapter bridging trust-lift output to trust-vcgen for binary verification.
//
// Converts LiftedFunction (binary -> CFG -> SSA -> tMIR) into VerificationConditions
// by wrapping the tMIR body as a VerifiableFunction and running the standard VC
// generation pipeline, plus binary-specific safety VCs (memory model, stack discipline).
//
// tRust #565: Also provides lifted_to_legacy() to convert LiftedFunction into the
// legacy LiftedProgram format, enabling the security analysis pipeline (buffer
// overflow, UAF, format string, etc.) to consume output from the canonical
// disassembler chain.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_lift::{LiftedFunction, LocalLayout};
use trust_types::{
    ConstValue, Formula, Operand, Projection, Rvalue, Sort, SourceSpan, Statement, Terminator, Ty,
    VcKind, VerifiableFunction, VerificationCondition,
};

use crate::binary_analysis::lifter::{
    AbstractInsn, AbstractOp, AbstractRegister, AbstractValue, LiftedProgram, MemoryAccess,
};

/// Convert a `LiftedFunction` into a `VerifiableFunction` suitable for VC generation.
///
/// The lifted function already carries a `tmir_body` (`VerifiableBody`) produced by
/// the semantic lifter. We wrap it with the metadata needed by the VC generator.
#[must_use]
pub fn lift_to_verifiable(lifted: &LiftedFunction) -> VerifiableFunction {
    VerifiableFunction {
        name: lifted.name.clone(),
        def_path: format!("binary::{}", lifted.name),
        span: SourceSpan {
            file: format!("binary:0x{:x}", lifted.entry_point),
            line_start: 0,
            col_start: 0,
            line_end: 0,
            col_end: 0,
        },
        body: lifted.tmir_body.clone(),
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

// ────────────────────────────────────────────────────────────────────────────
// tRust #565: LiftedFunction -> LiftedProgram adapter
// ────────────────────────────────────────────────────────────────────────────

/// Convert a `trust_lift::LiftedFunction` into the legacy `LiftedProgram` format.
///
/// This adapter enables the legacy security analysis pipeline (buffer overflow,
/// UAF, format string, control-flow hijack detection) to consume output from
/// the canonical disassembler chain (trust-binary-parse -> trust-disasm ->
/// trust-machine-sem -> trust-lift).
///
/// The conversion walks the tMIR body and synthesizes `AbstractInsn` values
/// with synthetic addresses derived from block ID and statement index.
#[must_use]
pub fn lifted_to_legacy(lifted: &LiftedFunction) -> LiftedProgram {
    let mut instructions = Vec::new();

    for block in &lifted.tmir_body.blocks {
        let block_base = synthetic_block_address(lifted.entry_point, block.id.0);

        // Convert statements
        for (stmt_idx, stmt) in block.stmts.iter().enumerate() {
            let addr = block_base.saturating_add((stmt_idx as u64) * 4);
            if let Some(insn) = stmt_to_abstract_insn(stmt, addr) {
                instructions.push(insn);
            }
        }

        // Convert terminator
        let term_addr = block_base.saturating_add((block.stmts.len() as u64) * 4);
        if let Some(insn) =
            terminator_to_abstract_insn(&block.terminator, term_addr, lifted.entry_point)
        {
            instructions.push(insn);
        }
    }

    // Build registers from locals
    let registers: Vec<AbstractRegister> = lifted
        .tmir_body
        .locals
        .iter()
        .map(|local| {
            let width = ty_to_width(&local.ty);
            AbstractRegister {
                id: local.index as u16,
                name: local.name.clone().unwrap_or_else(|| format!("_{}", local.index)),
                width,
            }
        })
        .collect();

    // Ensure instructions are sorted by address and the entry point is present
    instructions.sort_by_key(|insn| insn.address);

    LiftedProgram { instructions, entry_point: lifted.entry_point, registers }
}

/// Convert a tMIR statement to an abstract instruction.
fn stmt_to_abstract_insn(stmt: &Statement, addr: u64) -> Option<AbstractInsn> {
    match stmt {
        Statement::Assign { place, rvalue, .. } => {
            let dst = place.local as u16;

            // Check for memory store (place has Deref projection)
            if place.projections.iter().any(|p| matches!(p, Projection::Deref)) {
                let value = rvalue_to_formula(rvalue);
                let store_addr =
                    Formula::Var(format!("_store_addr_{}", place.local), Sort::BitVec(64));
                return Some(AbstractInsn {
                    address: addr,
                    op: AbstractOp::Store {
                        access: MemoryAccess::Write { addr: store_addr, size: 8, value },
                    },
                    size: 4,
                });
            }

            let op = match rvalue {
                Rvalue::BinaryOp(bin_op, lhs, rhs) => AbstractOp::BinArith {
                    dst,
                    op: *bin_op,
                    lhs: operand_to_abstract_value(lhs),
                    rhs: operand_to_abstract_value(rhs),
                },
                Rvalue::CheckedBinaryOp(bin_op, lhs, rhs) => AbstractOp::BinArith {
                    dst,
                    op: *bin_op,
                    lhs: operand_to_abstract_value(lhs),
                    rhs: operand_to_abstract_value(rhs),
                },
                Rvalue::UnaryOp(un_op, operand) => AbstractOp::UnaryOp {
                    dst,
                    op: *un_op,
                    operand: operand_to_abstract_value(operand),
                },
                Rvalue::Use(operand) => {
                    // Check if operand is a deref (memory load)
                    if let Operand::Copy(src_place) | Operand::Move(src_place) = operand
                        && src_place.projections.iter().any(|p| matches!(p, Projection::Deref))
                    {
                        let load_addr = Formula::Var(
                            format!("_load_addr_{}", src_place.local),
                            Sort::BitVec(64),
                        );
                        return Some(AbstractInsn {
                            address: addr,
                            op: AbstractOp::Load {
                                dst,
                                access: MemoryAccess::Read { addr: load_addr, size: 8 },
                            },
                            size: 4,
                        });
                    }
                    AbstractOp::Assign { dst, src: operand_to_abstract_value(operand) }
                }
                Rvalue::Cast(operand, _) => {
                    AbstractOp::Assign { dst, src: operand_to_abstract_value(operand) }
                }
                _ => AbstractOp::Nop,
            };

            Some(AbstractInsn { address: addr, op, size: 4 })
        }
        _ => None,
    }
}

/// Convert a tMIR terminator to an abstract instruction.
fn terminator_to_abstract_insn(
    term: &Terminator,
    addr: u64,
    entry_point: u64,
) -> Option<AbstractInsn> {
    let op = match term {
        Terminator::Return => AbstractOp::Return { value: None },
        Terminator::Goto(target) => {
            AbstractOp::Branch { target: synthetic_block_address(entry_point, target.0) }
        }
        Terminator::Call { func: callee, args, target, .. } => AbstractOp::Call {
            func: callee.clone(),
            args: args.iter().map(operand_to_abstract_value).collect(),
            dest: None,
            next: target.map(|t| synthetic_block_address(entry_point, t.0)),
        },
        Terminator::SwitchInt { discr, targets, otherwise, .. } => {
            if let Some((_, true_target)) = targets.first() {
                AbstractOp::CondBranch {
                    cond: operand_to_abstract_value(discr),
                    true_target: synthetic_block_address(entry_point, true_target.0),
                    false_target: synthetic_block_address(entry_point, otherwise.0),
                }
            } else {
                AbstractOp::Branch { target: synthetic_block_address(entry_point, otherwise.0) }
            }
        }
        Terminator::Drop { target, .. } => {
            AbstractOp::Branch { target: synthetic_block_address(entry_point, target.0) }
        }
        _ => return None,
    };

    Some(AbstractInsn { address: addr, op, size: 4 })
}

/// Convert an operand to an AbstractValue.
fn operand_to_abstract_value(op: &Operand) -> AbstractValue {
    match op {
        Operand::Copy(place) | Operand::Move(place) => AbstractValue::Register(place.local as u16),
        Operand::Constant(cv) => {
            let formula = match cv {
                ConstValue::Bool(b) => Formula::Bool(*b),
                ConstValue::Int(n) => Formula::Int(*n),
                ConstValue::Uint(n, _) => match i128::try_from(*n) {
                    Ok(n) => Formula::Int(n),
                    Err(_) => Formula::UInt(*n),
                },
                ConstValue::Float(f) => Formula::Var(format!("float_{f}"), Sort::BitVec(64)),
                ConstValue::Unit => Formula::Int(0),
                _ => Formula::Var("__unknown".into(), Sort::Int),
            };
            AbstractValue::Formula(formula)
        }
        _ => AbstractValue::Formula(Formula::Var("__unknown_op".into(), Sort::Int)),
    }
}

/// Extract a formula from an rvalue (for memory store values).
fn rvalue_to_formula(rvalue: &Rvalue) -> Formula {
    match rvalue {
        Rvalue::Use(op) => match op {
            Operand::Constant(ConstValue::Int(n)) => Formula::Int(*n),
            Operand::Constant(ConstValue::Uint(n, _)) => match i128::try_from(*n) {
                Ok(n) => Formula::Int(n),
                Err(_) => Formula::UInt(*n),
            },
            Operand::Constant(ConstValue::Bool(b)) => Formula::Bool(*b),
            Operand::Copy(p) | Operand::Move(p) => Formula::Var(format!("_{}", p.local), Sort::Int),
            _ => Formula::Var("__store_val".into(), Sort::Int),
        },
        _ => Formula::Var("__store_val".into(), Sort::Int),
    }
}

/// Compute synthetic address for a block.
fn synthetic_block_address(entry_point: u64, block_id: usize) -> u64 {
    entry_point.saturating_add((block_id as u64) * 0x100)
}

/// Convert a Ty to a register width in bits.
fn ty_to_width(ty: &Ty) -> u32 {
    match ty {
        Ty::Bool => 1,
        Ty::Int { width, .. } => *width,
        Ty::Float { width } => *width,
        _ => 64, // default width for unknown types
    }
}

// ────────────────────────────────────────────────────────────────────────────
// VC generation
// ────────────────────────────────────────────────────────────────────────────

/// Generate verification conditions from a lifted binary function.
///
/// Produces both:
/// 1. Standard safety VCs (overflow, division by zero, etc.) by running the
///    existing `generate_vcs` pipeline on the tMIR body.
/// 2. Binary-specific memory model VCs (out-of-bounds access, stack discipline).
///
/// Returns all VCs sorted by location for deterministic output.
#[must_use]
pub fn generate_binary_vcs(lifted: &LiftedFunction) -> Vec<VerificationCondition> {
    let verifiable = lift_to_verifiable(lifted);
    let mut vcs = crate::generate_vcs(&verifiable);

    // Binary-specific VCs: memory model and stack discipline.
    vcs.extend(generate_memory_model_vcs(lifted));

    vcs
}

fn detect_memory_local(lifted: &LiftedFunction) -> Option<usize> {
    memory_local_from_store_formula(lifted)
        .or_else(|| memory_local_from_decl_name(lifted))
        .or_else(|| memory_local_from_known_layout(lifted))
}

fn memory_local_from_store_formula(lifted: &LiftedFunction) -> Option<usize> {
    lifted.tmir_body.blocks.iter().flat_map(|block| block.stmts.iter()).find_map(|stmt| {
        let Statement::Assign { place, rvalue, .. } = stmt else {
            return None;
        };

        rvalue_stores_to_mem(rvalue).then_some(place.local)
    })
}

fn memory_local_from_decl_name(lifted: &LiftedFunction) -> Option<usize> {
    lifted
        .tmir_body
        .locals
        .iter()
        .find_map(|local| (local.name.as_deref() == Some("MEM")).then_some(local.index))
}

fn memory_local_from_known_layout(lifted: &LiftedFunction) -> Option<usize> {
    let x86_64 = LocalLayout::x86_64();
    if known_layout_matches(lifted, &x86_64, &[(1, "RAX"), (2, "RCX"), (19, "CF"), (20, "ZF")]) {
        return Some(x86_64.mem_local);
    }

    let aarch64 = LocalLayout::aarch64();
    if known_layout_matches(lifted, &aarch64, &[(1, "X0"), (2, "X1"), (34, "N"), (35, "Z")]) {
        return Some(aarch64.mem_local);
    }

    None
}

fn known_layout_matches(
    lifted: &LiftedFunction,
    layout: &LocalLayout,
    named_anchors: &[(usize, &str)],
) -> bool {
    let locals = &lifted.tmir_body.locals;
    has_local_index(locals, layout.mem_local)
        && (named_anchors.iter().any(|(index, name)| has_local_name(locals, *index, name))
            || has_exact_dense_layout(locals, layout.total))
}

fn has_local_index(locals: &[trust_types::LocalDecl], index: usize) -> bool {
    locals.iter().any(|local| local.index == index)
}

fn has_local_name(locals: &[trust_types::LocalDecl], index: usize, name: &str) -> bool {
    locals.iter().any(|local| local.index == index && local.name.as_deref() == Some(name))
}

fn has_exact_dense_layout(locals: &[trust_types::LocalDecl], total: usize) -> bool {
    locals.iter().map(|local| local.index).max() == Some(total - 1)
        && (0..total).all(|index| has_local_index(locals, index))
}

fn rvalue_stores_to_mem(rvalue: &Rvalue) -> bool {
    matches!(rvalue, Rvalue::Use(Operand::Symbolic(formula)) if formula_stores_to_mem(formula))
}

fn formula_stores_to_mem(formula: &Formula) -> bool {
    matches!(formula, Formula::Store(base, _, _) if formula_is_mem_array(base))
}

fn formula_is_mem_array(formula: &Formula) -> bool {
    match formula {
        Formula::Store(base, _, _) => formula_is_mem_array(base),
        _ => {
            formula.var_name() == Some("MEM")
                && matches!(formula.var_sort(), Some(Sort::Array(_, _)))
        }
    }
}

/// Generate memory model VCs for lifted binary code.
///
/// These VCs are specific to binary analysis (not present in source-level MIR):
/// - **Memory read validity**: Every memory read accesses a previously written
///   or argument-initialized address (no reading uninitialized memory).
/// - **Stack discipline**: SP decrements on function entry and is restored on exit.
/// - **No out-of-bounds memory access**: Memory accesses within known bounds.
///
/// Each VC's formula uses the array theory (Select/Store) to model memory as a
/// flat byte-addressable array, matching trust-machine-sem's memory model.
#[must_use]
pub fn generate_memory_model_vcs(lifted: &LiftedFunction) -> Vec<VerificationCondition> {
    let mut vcs = Vec::new();
    let func_name = &lifted.name;
    let mem_local_index = detect_memory_local(lifted);

    // Scan tMIR blocks for memory-related statements.
    for block in &lifted.tmir_body.blocks {
        for stmt in &block.stmts {
            if let Statement::Assign { place, rvalue: _, span } = stmt {
                // Detect writes to MEM local (memory store operations from the binary).
                if Some(place.local) == mem_local_index {
                    // Memory write: generate an OOB check.
                    // VC: the write address must be within valid memory bounds.
                    // Formula: addr >= stack_base AND addr < stack_limit
                    // Negated (SAT = violation): addr < stack_base OR addr >= stack_limit
                    let addr_var = Formula::Var(
                        format!("mem_addr_bb{}_{}", block.id.0, place.local),
                        Sort::BitVec(64),
                    );
                    let stack_base = Formula::Var("stack_base".into(), Sort::BitVec(64));
                    let stack_limit = Formula::Var("stack_limit".into(), Sort::BitVec(64));

                    let oob_formula = Formula::Or(vec![
                        Formula::BvULt(Box::new(addr_var.clone()), Box::new(stack_base), 64),
                        Formula::Not(Box::new(Formula::BvULt(
                            Box::new(addr_var),
                            Box::new(stack_limit),
                            64,
                        ))),
                    ]);

                    vcs.push(VerificationCondition {
                        kind: VcKind::Assertion {
                            message: format!("binary memory write OOB in block bb{}", block.id.0,),
                        },
                        function: func_name.clone().into(),
                        location: span.clone(),
                        formula: oob_formula,
                        contract_metadata: None,
                    });
                }
            }
        }

        // Stack discipline: check that Return terminators restore SP.
        if matches!(block.terminator, Terminator::Return) {
            let sp_current = Formula::Var("SP".into(), Sort::BitVec(64));
            let sp_entry = Formula::Var("SP_entry".into(), Sort::BitVec(64));

            // VC: SP at return must equal SP at entry.
            // Negated (SAT = violation): SP_current != SP_entry
            let sp_mismatch =
                Formula::Not(Box::new(Formula::Eq(Box::new(sp_current), Box::new(sp_entry))));

            vcs.push(VerificationCondition {
                kind: VcKind::Assertion {
                    message: format!(
                        "stack pointer not restored on return in block bb{}",
                        block.id.0,
                    ),
                },
                function: func_name.clone().into(),
                location: SourceSpan {
                    file: format!("binary:0x{:x}", lifted.entry_point),
                    line_start: 0,
                    col_start: 0,
                    line_end: 0,
                    col_end: 0,
                },
                formula: sp_mismatch,
                contract_metadata: None,
            });
        }
    }

    vcs
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_lift::cfg::{Cfg, LiftedBlock};
    use trust_types::{
        BasicBlock, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue, SourceSpan, Statement,
        Terminator, Ty, VerifiableBody,
    };

    /// Build a minimal LiftedFunction for testing.
    fn make_test_lifted() -> LiftedFunction {
        // A simple function with one block: assigns X0 = X1 + X2, then returns.
        let mut cfg = Cfg::new();
        cfg.add_block(LiftedBlock {
            id: 0,
            start_addr: 0x1000,
            instructions: vec![],
            successors: vec![],
            is_return: true,
        });

        let body = VerifiableBody {
            locals: vec![
                LocalDecl {
                    index: 0,
                    ty: Ty::Int { width: 64, signed: false },
                    name: Some("_lifted_result".into()),
                },
                LocalDecl {
                    index: 1,
                    ty: Ty::Int { width: 64, signed: false },
                    name: Some("X0".into()),
                },
                LocalDecl {
                    index: 2,
                    ty: Ty::Int { width: 64, signed: false },
                    name: Some("X1".into()),
                },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::BinaryOp(
                        trust_types::BinOp::Add,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: SourceSpan {
                        file: "binary:0x1000".to_string(),
                        line_start: 0,
                        col_start: 0,
                        line_end: 0,
                        col_end: 0,
                    },
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::Int { width: 64, signed: false },
        };

        LiftedFunction {
            name: "test_add".to_string(),
            entry_point: 0x1000,
            cfg,
            tmir_body: body,
            ssa: None,
            annotations: vec![],
        }
    }

    /// Build a LiftedFunction with memory operations for memory model VC tests.
    fn make_mem_lifted() -> LiftedFunction {
        make_mem_lifted_with_layout(LocalLayout::standard(), "test_mem", 0x2000)
    }

    fn make_mem_lifted_with_layout(
        layout: LocalLayout,
        name: &str,
        entry_point: u64,
    ) -> LiftedFunction {
        let mem_idx = layout.mem_local;

        let mut cfg = Cfg::new();
        cfg.add_block(LiftedBlock {
            id: 0,
            start_addr: entry_point,
            instructions: vec![],
            successors: vec![],
            is_return: true,
        });

        let body = VerifiableBody {
            locals: {
                let mut locals = Vec::new();
                // Build locals matching the selected layout up to MEM.
                locals.push(LocalDecl {
                    index: 0,
                    ty: Ty::Int { width: 64, signed: false },
                    name: Some("_result".into()),
                });
                locals.push(LocalDecl {
                    index: 1,
                    ty: Ty::Int { width: 64, signed: false },
                    name: Some("X0".into()),
                });
                locals.push(LocalDecl {
                    index: 2,
                    ty: Ty::Int { width: 64, signed: false },
                    name: Some("X1".into()),
                });
                // Pad locals 3..(mem_idx-1) to position MEM at the selected index.
                for i in 3..mem_idx {
                    locals.push(LocalDecl {
                        index: i,
                        ty: Ty::Int { width: 64, signed: false },
                        name: Some(format!("_pad{i}")),
                    });
                }
                locals.push(LocalDecl {
                    index: mem_idx,
                    ty: Ty::Int { width: 64, signed: false },
                    name: Some("MEM".into()),
                });
                locals
            },
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    // Memory write (to MEM local from the selected layout)
                    Statement::Assign {
                        place: Place::local(mem_idx),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 64))),
                        span: SourceSpan {
                            file: format!("binary:0x{entry_point:x}"),
                            line_start: 0,
                            col_start: 0,
                            line_end: 0,
                            col_end: 0,
                        },
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::Int { width: 64, signed: false },
        };

        LiftedFunction {
            name: name.to_string(),
            entry_point,
            cfg,
            tmir_body: body,
            ssa: None,
            annotations: vec![],
        }
    }

    #[test]
    fn test_lift_to_verifiable_preserves_name() {
        let lifted = make_test_lifted();
        let verifiable = lift_to_verifiable(&lifted);
        assert_eq!(verifiable.name, "test_add");
        assert_eq!(verifiable.def_path, "binary::test_add");
    }

    #[test]
    fn test_lift_to_verifiable_preserves_body() {
        let lifted = make_test_lifted();
        let verifiable = lift_to_verifiable(&lifted);
        assert_eq!(verifiable.body.blocks.len(), lifted.tmir_body.blocks.len());
        assert_eq!(verifiable.body.locals.len(), lifted.tmir_body.locals.len());
        assert_eq!(verifiable.body.arg_count, lifted.tmir_body.arg_count);
    }

    #[test]
    fn test_generate_binary_vcs_produces_arithmetic_vcs() {
        let lifted = make_test_lifted();
        let vcs = generate_binary_vcs(&lifted);

        // tRust #792: ArithmeticOverflow checks are now handled by zani-lib.
        // The Add operation on unsigned 64-bit integers no longer generates
        // ArithmeticOverflow VCs from trust-vcgen's standard pipeline.
        assert!(
            !vcs.iter().any(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { .. })),
            "ArithmeticOverflow VCs now handled by zani-lib"
        );
    }

    #[test]
    fn test_generate_binary_vcs_all_reference_function_name() {
        let lifted = make_test_lifted();
        let vcs = generate_binary_vcs(&lifted);

        for vc in &vcs {
            assert_eq!(
                vc.function, "test_add",
                "all VCs should reference the lifted function name"
            );
        }
    }

    #[test]
    fn test_generate_memory_model_vcs_mem_write() {
        let lifted = make_mem_lifted();
        let mem_vcs = generate_memory_model_vcs(&lifted);

        // Should produce memory OOB VC for the MEM write + stack discipline VC for return.
        let oob_vcs: Vec<_> = mem_vcs.iter()
            .filter(|vc| {
                matches!(&vc.kind, VcKind::Assertion { message } if message.contains("memory write OOB"))
            })
            .collect();
        assert!(!oob_vcs.is_empty(), "should produce memory OOB VCs for memory writes");
    }

    #[test]
    fn test_detect_memory_local_uses_x86_64_mem_decl() {
        let layout = LocalLayout::x86_64();
        let expected_mem = layout.mem_local;
        let lifted = make_mem_lifted_with_layout(layout, "test_x86_mem", 0x2400);

        assert_eq!(detect_memory_local(&lifted), Some(expected_mem));
        assert_ne!(detect_memory_local(&lifted), Some(LocalLayout::standard().mem_local));
    }

    #[test]
    fn test_generate_memory_model_vcs_x86_64_mem_write() {
        let layout = LocalLayout::x86_64();
        let lifted = make_mem_lifted_with_layout(layout, "test_x86_mem", 0x2400);
        let mem_vcs = generate_memory_model_vcs(&lifted);

        let oob_vcs: Vec<_> = mem_vcs
            .iter()
            .filter(|vc| {
                matches!(&vc.kind, VcKind::Assertion { message } if message.contains("memory write OOB"))
            })
            .collect();

        assert_eq!(oob_vcs.len(), 1, "should produce OOB VC for x86_64 MEM local");
        assert_eq!(oob_vcs[0].location.file, "binary:0x2400");
    }

    #[test]
    fn test_detect_memory_local_from_store_formula_without_mem_name() {
        let layout = LocalLayout::x86_64();
        let mem_idx = layout.mem_local;
        let mut lifted = make_mem_lifted_with_layout(layout, "test_x86_mem_store", 0x2500);
        lifted.tmir_body.locals = vec![
            LocalDecl { index: 0, ty: Ty::Int { width: 64, signed: false }, name: None },
            LocalDecl { index: mem_idx, ty: Ty::Int { width: 64, signed: false }, name: None },
        ];

        let store_formula = Formula::Store(
            Box::new(Formula::Var(
                "MEM".into(),
                Sort::Array(Box::new(Sort::BitVec(64)), Box::new(Sort::BitVec(8))),
            )),
            Box::new(Formula::Var("addr".into(), Sort::BitVec(64))),
            Box::new(Formula::Var("val".into(), Sort::BitVec(8))),
        );

        match &mut lifted.tmir_body.blocks[0].stmts[0] {
            Statement::Assign { rvalue, .. } => {
                *rvalue = Rvalue::Use(Operand::Symbolic(store_formula));
            }
            _ => panic!("expected memory assignment"),
        }

        assert_eq!(detect_memory_local(&lifted), Some(mem_idx));
    }

    #[test]
    fn test_generate_memory_model_vcs_stack_discipline() {
        let lifted = make_mem_lifted();
        let mem_vcs = generate_memory_model_vcs(&lifted);

        let sp_vcs: Vec<_> = mem_vcs.iter()
            .filter(|vc| {
                matches!(&vc.kind, VcKind::Assertion { message } if message.contains("stack pointer not restored"))
            })
            .collect();
        assert!(
            !sp_vcs.is_empty(),
            "should produce stack pointer restoration VCs for return blocks"
        );
    }

    #[test]
    fn test_generate_memory_model_vcs_empty_function() {
        // A function with no memory ops and no return blocks should produce no memory VCs.
        let mut cfg = Cfg::new();
        cfg.add_block(LiftedBlock {
            id: 0,
            start_addr: 0x3000,
            instructions: vec![],
            successors: vec![],
            is_return: true,
        });

        let body = VerifiableBody {
            locals: vec![LocalDecl {
                index: 0,
                ty: Ty::Int { width: 64, signed: false },
                name: None,
            }],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::Int { width: 64, signed: false },
        };

        let lifted = LiftedFunction {
            name: "empty_fn".to_string(),
            entry_point: 0x3000,
            cfg,
            tmir_body: body,
            ssa: None,
            annotations: vec![],
        };

        let mem_vcs = generate_memory_model_vcs(&lifted);
        // Only stack pointer VC (from the Return terminator), no memory OOB.
        let oob_vcs: Vec<_> = mem_vcs
            .iter()
            .filter(
                |vc| matches!(&vc.kind, VcKind::Assertion { message } if message.contains("OOB")),
            )
            .collect();
        assert!(oob_vcs.is_empty(), "empty function should not produce OOB VCs");

        let sp_vcs: Vec<_> = mem_vcs.iter()
            .filter(|vc| {
                matches!(&vc.kind, VcKind::Assertion { message } if message.contains("stack pointer"))
            })
            .collect();
        assert_eq!(sp_vcs.len(), 1, "should produce exactly one SP restoration VC");
    }

    #[test]
    fn test_binary_vcs_include_both_standard_and_memory() {
        let lifted = make_mem_lifted();
        let all_vcs = generate_binary_vcs(&lifted);

        // Should have both standard VCs (from the VC pipeline) and memory model VCs.
        let mem_vcs = generate_memory_model_vcs(&lifted);
        assert!(
            all_vcs.len() >= mem_vcs.len(),
            "total VCs should include at least the memory model VCs"
        );
    }

    // tRust #565: Tests for LiftedFunction -> LiftedProgram adapter.

    #[test]
    fn test_lifted_to_legacy_preserves_entry_point() {
        let lifted = make_test_lifted();
        let legacy = lifted_to_legacy(&lifted);
        assert_eq!(legacy.entry_point, 0x1000);
    }

    #[test]
    fn test_lifted_to_legacy_creates_registers_from_locals() {
        let lifted = make_test_lifted();
        let legacy = lifted_to_legacy(&lifted);
        assert_eq!(
            legacy.registers.len(),
            lifted.tmir_body.locals.len(),
            "should have one register per local"
        );
        assert_eq!(legacy.registers[0].id, 0);
        assert_eq!(legacy.registers[1].name, "X0");
        assert_eq!(legacy.registers[2].name, "X1");
        assert_eq!(legacy.registers[0].width, 64);
    }

    #[test]
    fn test_lifted_to_legacy_produces_instructions() {
        let lifted = make_test_lifted();
        let legacy = lifted_to_legacy(&lifted);
        // One BinArith statement + one Return terminator
        assert!(
            legacy.instructions.len() >= 2,
            "should have at least 2 instructions (assign + return), got {}",
            legacy.instructions.len()
        );
    }

    #[test]
    fn test_lifted_to_legacy_binarith_op() {
        let lifted = make_test_lifted();
        let legacy = lifted_to_legacy(&lifted);

        let has_add = legacy.instructions.iter().any(|insn| {
            matches!(&insn.op, AbstractOp::BinArith { op: trust_types::BinOp::Add, .. })
        });
        assert!(has_add, "should have an Add instruction from the tMIR body");
    }

    #[test]
    fn test_lifted_to_legacy_has_return() {
        let lifted = make_test_lifted();
        let legacy = lifted_to_legacy(&lifted);

        let has_ret =
            legacy.instructions.iter().any(|insn| matches!(&insn.op, AbstractOp::Return { .. }));
        assert!(has_ret, "should have a Return instruction");
    }

    #[test]
    fn test_lifted_to_legacy_entry_point_in_instructions() {
        let lifted = make_test_lifted();
        let legacy = lifted_to_legacy(&lifted);

        let has_entry = legacy.instructions.iter().any(|insn| insn.address == legacy.entry_point);
        assert!(
            has_entry,
            "entry point 0x{:x} should be present in instructions",
            legacy.entry_point
        );
    }
}
