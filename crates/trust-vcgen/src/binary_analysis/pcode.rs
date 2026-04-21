// trust-vcgen/binary_analysis/pcode.rs: P-code instruction set representation
//
// Models Ghidra's P-code intermediate representation for binary lifting.
// P-code is a register-transfer language that normalizes machine instructions
// across architectures. Each machine instruction decomposes into one or more
// P-code operations on varnodes (register/memory/constant references).
//
// Reference: Ghidra/Framework/SoftwareModeling/src/main/java/ghidra/program/model/pcode/
// See also: NSA Ghidra 2019, "The Ghidra Book" (Eagle & Nance, 2020)
//
// Part of #101: Binary Lifting
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};

use super::lifter::{AbstractInsn, AbstractOp, AbstractValue, MemoryAccess};
use trust_types::{BinOp, Formula, Sort, UnOp};

// ---------------------------------------------------------------------------
// P-code opcodes (from Ghidra's PcodeOp.java)
// ---------------------------------------------------------------------------

/// P-code operation codes corresponding to Ghidra's instruction set.
///
/// Reference: `Ghidra/Framework/SoftwareModeling/.../pcode/PcodeOp.java`
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum PcodeOpcode {
    // Data movement
    Copy,
    Load,
    Store,

    // Arithmetic
    IntAdd,
    IntSub,
    IntMult,
    IntDiv,
    IntSdiv,
    IntRem,
    IntSrem,
    IntNegate,

    // Logical
    IntAnd,
    IntOr,
    IntXor,
    IntNot,
    IntLeftShift,
    IntRightShift,
    IntSarShift,

    // Comparison
    IntEqual,
    IntNotEqual,
    IntLess,
    IntSless,
    IntLessEqual,
    IntSlessEqual,

    // Extension / truncation
    IntZext,
    IntSext,
    Subpiece,

    // Boolean
    BoolAnd,
    BoolOr,
    BoolXor,
    BoolNegate,

    // Floating point
    FloatAdd,
    FloatSub,
    FloatMult,
    FloatDiv,
    FloatNeg,
    FloatAbs,
    FloatSqrt,
    FloatNan,
    FloatEqual,
    FloatNotEqual,
    FloatLess,
    FloatLessEqual,
    FloatInt2Float,
    FloatFloat2Int,
    FloatTrunc,
    FloatCeil,
    FloatFloor,
    FloatRound,

    // Control flow
    Branch,
    CBranch,
    BranchInd,
    Call,
    CallInd,
    Return,

    // Memory
    Piece,
    CPoolRef,
    New,

    // Miscellaneous
    Multiequal,
    Indirect,
    Cast,
    PtrAdd,
    PtrSub,
    Unimplemented,
}

// ---------------------------------------------------------------------------
// P-code varnode (operand)
// ---------------------------------------------------------------------------

/// A varnode is the fundamental operand in P-code: a triple of
/// (address space, offset, size).
///
/// In Ghidra's model:
/// - Register space: offset = register ID, size = register width in bytes
/// - Constant space: offset = literal value
/// - RAM space: offset = memory address
/// - Unique space: offset = temporary ID
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Varnode {
    /// Address space identifier.
    pub space: AddressSpace,
    /// Offset within the address space.
    pub offset: u64,
    /// Size in bytes.
    pub size: u32,
}

/// P-code address space identifiers.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum AddressSpace {
    /// Machine registers.
    Register,
    /// Constant/immediate values.
    Constant,
    /// Main memory (RAM).
    Ram,
    /// Temporary/unique variables.
    Unique,
}

// ---------------------------------------------------------------------------
// P-code instruction
// ---------------------------------------------------------------------------

/// A single P-code operation with its operands.
///
/// Each machine instruction typically decomposes into 1-5 P-code operations.
/// For example, `ADD R1, R2, R3` becomes:
///   `INT_ADD (reg:R1, 8) = (reg:R2, 8), (reg:R3, 8)`
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PcodeInsn {
    /// Address of the original machine instruction.
    pub address: u64,
    /// Sub-instruction index within the machine instruction (0-based).
    pub seq_num: u16,
    /// The P-code operation.
    pub opcode: PcodeOpcode,
    /// Output varnode (None for control-flow ops like Branch/Return).
    pub output: Option<Varnode>,
    /// Input varnodes.
    pub inputs: Vec<Varnode>,
}

/// A sequence of P-code instructions representing one or more machine
/// instructions, suitable for translation to our abstract instruction layer.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PcodeBlock {
    /// P-code instructions in execution order.
    pub ops: Vec<PcodeInsn>,
    /// Base address of the block.
    pub base_address: u64,
}

// ---------------------------------------------------------------------------
// Translation: P-code -> AbstractInsn
// ---------------------------------------------------------------------------

/// Translate a sequence of P-code instructions into abstract instructions.
///
/// This performs a one-to-one mapping where possible, collapsing
/// P-code patterns into our higher-level abstract ops. Unsupported
/// opcodes are mapped to `AbstractOp::Nop`.
#[must_use]
pub fn translate_pcode_block(block: &PcodeBlock) -> Vec<AbstractInsn> {
    block.ops.iter().filter_map(translate_pcode_insn).collect()
}

/// Translate a single P-code instruction to an abstract instruction.
///
/// Returns `None` for P-code ops that have no meaningful abstract
/// equivalent (e.g., `Multiequal`, `Indirect`, `Cast`).
#[must_use]
pub fn translate_pcode_insn(insn: &PcodeInsn) -> Option<AbstractInsn> {
    let op = match insn.opcode {
        // Data movement
        PcodeOpcode::Copy => translate_copy(insn)?,
        PcodeOpcode::Load => translate_load(insn)?,
        PcodeOpcode::Store => translate_store(insn)?,

        // Arithmetic
        PcodeOpcode::IntAdd => translate_binop(insn, BinOp::Add)?,
        PcodeOpcode::IntSub => translate_binop(insn, BinOp::Sub)?,
        PcodeOpcode::IntMult => translate_binop(insn, BinOp::Mul)?,
        PcodeOpcode::IntDiv => translate_binop(insn, BinOp::Div)?,
        PcodeOpcode::IntSdiv => translate_binop(insn, BinOp::Div)?,
        PcodeOpcode::IntRem => translate_binop(insn, BinOp::Rem)?,
        PcodeOpcode::IntSrem => translate_binop(insn, BinOp::Rem)?,
        PcodeOpcode::IntNegate => translate_unop(insn, UnOp::Neg)?,

        // Logical
        PcodeOpcode::IntAnd => translate_binop(insn, BinOp::BitAnd)?,
        PcodeOpcode::IntOr => translate_binop(insn, BinOp::BitOr)?,
        PcodeOpcode::IntXor => translate_binop(insn, BinOp::BitXor)?,
        PcodeOpcode::IntNot => translate_unop(insn, UnOp::Not)?,
        PcodeOpcode::IntLeftShift => translate_binop(insn, BinOp::Shl)?,
        PcodeOpcode::IntRightShift => translate_binop(insn, BinOp::Shr)?,
        PcodeOpcode::IntSarShift => translate_binop(insn, BinOp::Shr)?,

        // Comparison -> BinArith producing a boolean register
        PcodeOpcode::IntEqual => translate_binop(insn, BinOp::Eq)?,
        PcodeOpcode::IntNotEqual => translate_binop(insn, BinOp::Ne)?,
        PcodeOpcode::IntLess => translate_binop(insn, BinOp::Lt)?,
        PcodeOpcode::IntSless => translate_binop(insn, BinOp::Lt)?,
        PcodeOpcode::IntLessEqual => translate_binop(insn, BinOp::Le)?,
        PcodeOpcode::IntSlessEqual => translate_binop(insn, BinOp::Le)?,

        // Extension
        PcodeOpcode::IntZext | PcodeOpcode::IntSext | PcodeOpcode::Subpiece => {
            translate_copy(insn)?
        }

        // Boolean
        PcodeOpcode::BoolAnd => translate_binop(insn, BinOp::BitAnd)?,
        PcodeOpcode::BoolOr => translate_binop(insn, BinOp::BitOr)?,
        PcodeOpcode::BoolXor => translate_binop(insn, BinOp::BitXor)?,
        PcodeOpcode::BoolNegate => translate_unop(insn, UnOp::Not)?,

        // Floating point arithmetic
        PcodeOpcode::FloatAdd => translate_binop(insn, BinOp::Add)?,
        PcodeOpcode::FloatSub => translate_binop(insn, BinOp::Sub)?,
        PcodeOpcode::FloatMult => translate_binop(insn, BinOp::Mul)?,
        PcodeOpcode::FloatDiv => translate_binop(insn, BinOp::Div)?,
        PcodeOpcode::FloatNeg => translate_unop(insn, UnOp::Neg)?,

        // Float comparison
        PcodeOpcode::FloatEqual => translate_binop(insn, BinOp::Eq)?,
        PcodeOpcode::FloatNotEqual => translate_binop(insn, BinOp::Ne)?,
        PcodeOpcode::FloatLess => translate_binop(insn, BinOp::Lt)?,
        PcodeOpcode::FloatLessEqual => translate_binop(insn, BinOp::Le)?,

        // Float conversion (modeled as copy)
        PcodeOpcode::FloatInt2Float
        | PcodeOpcode::FloatFloat2Int
        | PcodeOpcode::FloatTrunc
        | PcodeOpcode::FloatCeil
        | PcodeOpcode::FloatFloor
        | PcodeOpcode::FloatRound
        | PcodeOpcode::FloatAbs
        | PcodeOpcode::FloatSqrt
        | PcodeOpcode::FloatNan => translate_copy(insn)?,

        // Control flow
        PcodeOpcode::Branch => translate_branch(insn)?,
        PcodeOpcode::CBranch => translate_cbranch(insn)?,
        PcodeOpcode::BranchInd => translate_branch_ind(insn),
        PcodeOpcode::Call => translate_call(insn)?,
        PcodeOpcode::CallInd => translate_call_ind(insn)?,
        PcodeOpcode::Return => AbstractOp::Return { value: None },

        // Memory construction
        PcodeOpcode::Piece => translate_copy(insn)?,

        // No-ops in our model
        PcodeOpcode::Multiequal
        | PcodeOpcode::Indirect
        | PcodeOpcode::Cast
        | PcodeOpcode::CPoolRef
        | PcodeOpcode::New
        | PcodeOpcode::PtrAdd
        | PcodeOpcode::PtrSub
        | PcodeOpcode::Unimplemented => AbstractOp::Nop,
    };

    Some(AbstractInsn {
        address: insn.address,
        op,
        size: insn.inputs.first().map_or(4, |v| v.size.max(1) as u8),
    })
}

// ---------------------------------------------------------------------------
// Translation helpers
// ---------------------------------------------------------------------------

fn varnode_to_abstract_value(vn: &Varnode) -> AbstractValue {
    match vn.space {
        AddressSpace::Register => AbstractValue::Register(vn.offset as u16),
        AddressSpace::Constant => {
            AbstractValue::Formula(Formula::BitVec {
                value: vn.offset as i128,
                width: vn.size.saturating_mul(8),
            })
        }
        AddressSpace::Ram => AbstractValue::Formula(Formula::Var(
            format!("mem_{:x}", vn.offset),
            Sort::BitVec(vn.size.saturating_mul(8)),
        )),
        AddressSpace::Unique => AbstractValue::Register(vn.offset as u16),
    }
}

fn varnode_to_formula(vn: &Varnode) -> Formula {
    match vn.space {
        AddressSpace::Register => {
            Formula::Var(format!("r{}", vn.offset), Sort::BitVec(vn.size.saturating_mul(8)))
        }
        AddressSpace::Constant => Formula::BitVec {
            value: vn.offset as i128,
            width: vn.size.saturating_mul(8),
        },
        AddressSpace::Ram => Formula::Var(
            format!("mem_{:x}", vn.offset),
            Sort::BitVec(vn.size.saturating_mul(8)),
        ),
        AddressSpace::Unique => {
            Formula::Var(format!("tmp_{}", vn.offset), Sort::BitVec(vn.size.saturating_mul(8)))
        }
    }
}

fn output_register(insn: &PcodeInsn) -> Option<u16> {
    insn.output.as_ref().and_then(|vn| match vn.space {
        AddressSpace::Register | AddressSpace::Unique => Some(vn.offset as u16),
        _ => None,
    })
}

fn translate_copy(insn: &PcodeInsn) -> Option<AbstractOp> {
    let dst = output_register(insn)?;
    let src = insn.inputs.first()?;
    Some(AbstractOp::UnaryOp {
        dst,
        op: UnOp::Not,  // We model COPY as identity; closest available is double-not
        operand: varnode_to_abstract_value(src),
    })
}

fn translate_load(insn: &PcodeInsn) -> Option<AbstractOp> {
    let dst = output_register(insn)?;
    // P-code LOAD: input[0] = address space ID, input[1] = address
    let addr_vn = insn.inputs.get(1).or_else(|| insn.inputs.first())?;
    let size = insn.output.as_ref().map_or(4, |o| o.size);
    Some(AbstractOp::Load {
        dst,
        access: MemoryAccess::Read {
            addr: varnode_to_formula(addr_vn),
            size,
        },
    })
}

fn translate_store(insn: &PcodeInsn) -> Option<AbstractOp> {
    // P-code STORE: input[0] = address space ID, input[1] = address, input[2] = value
    let addr_vn = insn.inputs.get(1).or_else(|| insn.inputs.first())?;
    let val_vn = insn.inputs.get(2).or_else(|| insn.inputs.get(1))?;
    let size = val_vn.size;
    Some(AbstractOp::Store {
        access: MemoryAccess::Write {
            addr: varnode_to_formula(addr_vn),
            size,
            value: varnode_to_formula(val_vn),
        },
    })
}

fn translate_binop(insn: &PcodeInsn, op: BinOp) -> Option<AbstractOp> {
    let dst = output_register(insn)?;
    let lhs = insn.inputs.first()?;
    let rhs = insn.inputs.get(1)?;
    Some(AbstractOp::BinArith {
        dst,
        op,
        lhs: varnode_to_abstract_value(lhs),
        rhs: varnode_to_abstract_value(rhs),
    })
}

fn translate_unop(insn: &PcodeInsn, op: UnOp) -> Option<AbstractOp> {
    let dst = output_register(insn)?;
    let operand = insn.inputs.first()?;
    Some(AbstractOp::UnaryOp {
        dst,
        op,
        operand: varnode_to_abstract_value(operand),
    })
}

fn translate_branch(insn: &PcodeInsn) -> Option<AbstractOp> {
    let target_vn = insn.inputs.first()?;
    Some(AbstractOp::Branch { target: target_vn.offset })
}

fn translate_cbranch(insn: &PcodeInsn) -> Option<AbstractOp> {
    let target_vn = insn.inputs.first()?;
    let cond_vn = insn.inputs.get(1)?;
    // P-code CBranch: if cond, goto target; else fallthrough
    // false_target is the next sequential address
    let false_target = insn.address.wrapping_add(4); // approximate
    Some(AbstractOp::CondBranch {
        cond: varnode_to_abstract_value(cond_vn),
        true_target: target_vn.offset,
        false_target,
    })
}

fn translate_branch_ind(insn: &PcodeInsn) -> AbstractOp {
    // Indirect branch: we cannot resolve the target statically.
    // Model as return (conservative).
    let value = insn.inputs.first().map(varnode_to_abstract_value);
    AbstractOp::Return { value }
}

fn translate_call(insn: &PcodeInsn) -> Option<AbstractOp> {
    let target_vn = insn.inputs.first()?;
    let func_name = format!("sub_{:x}", target_vn.offset);
    let args: Vec<AbstractValue> = insn.inputs.iter().skip(1).map(varnode_to_abstract_value).collect();
    let dest = output_register(insn);
    Some(AbstractOp::Call {
        func: func_name,
        args,
        dest,
        next: Some(insn.address.wrapping_add(4)),
    })
}

fn translate_call_ind(insn: &PcodeInsn) -> Option<AbstractOp> {
    let target_vn = insn.inputs.first()?;
    let func_name = format!("indirect_{:x}", target_vn.offset);
    let args: Vec<AbstractValue> = insn.inputs.iter().skip(1).map(varnode_to_abstract_value).collect();
    let dest = output_register(insn);
    Some(AbstractOp::Call {
        func: func_name,
        args,
        dest,
        next: Some(insn.address.wrapping_add(4)),
    })
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn reg_vn(id: u64, size: u32) -> Varnode {
        Varnode { space: AddressSpace::Register, offset: id, size }
    }

    fn const_vn(value: u64, size: u32) -> Varnode {
        Varnode { space: AddressSpace::Constant, offset: value, size }
    }

    fn ram_vn(addr: u64, size: u32) -> Varnode {
        Varnode { space: AddressSpace::Ram, offset: addr, size }
    }

    fn pcode(
        address: u64,
        opcode: PcodeOpcode,
        output: Option<Varnode>,
        inputs: Vec<Varnode>,
    ) -> PcodeInsn {
        PcodeInsn { address, seq_num: 0, opcode, output, inputs }
    }

    #[test]
    fn test_translate_int_add() {
        let insn = pcode(
            0x1000,
            PcodeOpcode::IntAdd,
            Some(reg_vn(0, 8)),
            vec![reg_vn(1, 8), reg_vn(2, 8)],
        );
        let result = translate_pcode_insn(&insn).expect("should translate");
        assert_eq!(result.address, 0x1000);
        assert!(matches!(
            result.op,
            AbstractOp::BinArith { dst: 0, op: BinOp::Add, .. }
        ));
    }

    #[test]
    fn test_translate_int_sub() {
        let insn = pcode(
            0x1004,
            PcodeOpcode::IntSub,
            Some(reg_vn(3, 4)),
            vec![reg_vn(1, 4), const_vn(1, 4)],
        );
        let result = translate_pcode_insn(&insn).expect("should translate");
        assert!(matches!(
            result.op,
            AbstractOp::BinArith { dst: 3, op: BinOp::Sub, .. }
        ));
    }

    #[test]
    fn test_translate_load() {
        let insn = pcode(
            0x2000,
            PcodeOpcode::Load,
            Some(reg_vn(5, 4)),
            vec![const_vn(0, 4), ram_vn(0x8000, 4)],
        );
        let result = translate_pcode_insn(&insn).expect("should translate");
        assert!(matches!(
            result.op,
            AbstractOp::Load { dst: 5, access: MemoryAccess::Read { size: 4, .. } }
        ));
    }

    #[test]
    fn test_translate_store() {
        let insn = pcode(
            0x2004,
            PcodeOpcode::Store,
            None,
            vec![const_vn(0, 4), ram_vn(0x8000, 4), reg_vn(5, 4)],
        );
        let result = translate_pcode_insn(&insn).expect("should translate");
        assert!(matches!(
            result.op,
            AbstractOp::Store { access: MemoryAccess::Write { size: 4, .. } }
        ));
    }

    #[test]
    fn test_translate_branch() {
        let insn = pcode(
            0x3000,
            PcodeOpcode::Branch,
            None,
            vec![ram_vn(0x4000, 4)],
        );
        let result = translate_pcode_insn(&insn).expect("should translate");
        assert!(matches!(
            result.op,
            AbstractOp::Branch { target: 0x4000 }
        ));
    }

    #[test]
    fn test_translate_cbranch() {
        let insn = pcode(
            0x3004,
            PcodeOpcode::CBranch,
            None,
            vec![ram_vn(0x4000, 4), reg_vn(7, 1)],
        );
        let result = translate_pcode_insn(&insn).expect("should translate");
        assert!(matches!(
            result.op,
            AbstractOp::CondBranch { true_target: 0x4000, .. }
        ));
    }

    #[test]
    fn test_translate_call() {
        let insn = pcode(
            0x5000,
            PcodeOpcode::Call,
            Some(reg_vn(0, 8)),
            vec![ram_vn(0x6000, 4), reg_vn(1, 8)],
        );
        let result = translate_pcode_insn(&insn).expect("should translate");
        assert!(matches!(result.op, AbstractOp::Call { .. }));
        if let AbstractOp::Call { func, args, dest, .. } = &result.op {
            assert_eq!(func, "sub_6000");
            assert_eq!(args.len(), 1);
            assert_eq!(*dest, Some(0));
        }
    }

    #[test]
    fn test_translate_return() {
        let insn = pcode(0x7000, PcodeOpcode::Return, None, vec![]);
        let result = translate_pcode_insn(&insn).expect("should translate");
        assert!(matches!(result.op, AbstractOp::Return { value: None }));
    }

    #[test]
    fn test_translate_comparison() {
        let insn = pcode(
            0x8000,
            PcodeOpcode::IntEqual,
            Some(reg_vn(10, 1)),
            vec![reg_vn(1, 8), reg_vn(2, 8)],
        );
        let result = translate_pcode_insn(&insn).expect("should translate");
        assert!(matches!(
            result.op,
            AbstractOp::BinArith { dst: 10, op: BinOp::Eq, .. }
        ));
    }

    #[test]
    fn test_translate_nop_opcodes() {
        for opcode in [
            PcodeOpcode::Multiequal,
            PcodeOpcode::Indirect,
            PcodeOpcode::Cast,
            PcodeOpcode::Unimplemented,
        ] {
            let insn = pcode(0x9000, opcode, None, vec![]);
            let result = translate_pcode_insn(&insn).expect("should translate");
            assert!(matches!(result.op, AbstractOp::Nop));
        }
    }

    #[test]
    fn test_translate_block() {
        let block = PcodeBlock {
            base_address: 0x1000,
            ops: vec![
                pcode(
                    0x1000,
                    PcodeOpcode::IntAdd,
                    Some(reg_vn(0, 8)),
                    vec![reg_vn(1, 8), reg_vn(2, 8)],
                ),
                pcode(
                    0x1004,
                    PcodeOpcode::IntSub,
                    Some(reg_vn(3, 8)),
                    vec![reg_vn(0, 8), const_vn(1, 8)],
                ),
                pcode(0x1008, PcodeOpcode::Return, None, vec![]),
            ],
        };

        let insns = translate_pcode_block(&block);
        assert_eq!(insns.len(), 3);
        assert!(matches!(insns[0].op, AbstractOp::BinArith { op: BinOp::Add, .. }));
        assert!(matches!(insns[1].op, AbstractOp::BinArith { op: BinOp::Sub, .. }));
        assert!(matches!(insns[2].op, AbstractOp::Return { .. }));
    }

    #[test]
    fn test_translate_int_not() {
        let insn = pcode(
            0xA000,
            PcodeOpcode::IntNot,
            Some(reg_vn(4, 8)),
            vec![reg_vn(3, 8)],
        );
        let result = translate_pcode_insn(&insn).expect("should translate");
        assert!(matches!(
            result.op,
            AbstractOp::UnaryOp { dst: 4, op: UnOp::Not, .. }
        ));
    }

    #[test]
    fn test_translate_shift_ops() {
        let insn = pcode(
            0xB000,
            PcodeOpcode::IntLeftShift,
            Some(reg_vn(5, 8)),
            vec![reg_vn(3, 8), const_vn(2, 8)],
        );
        let result = translate_pcode_insn(&insn).expect("should translate");
        assert!(matches!(
            result.op,
            AbstractOp::BinArith { dst: 5, op: BinOp::Shl, .. }
        ));
    }

    #[test]
    fn test_varnode_serialization_roundtrip() {
        let vn = Varnode { space: AddressSpace::Register, offset: 42, size: 8 };
        let json = serde_json::to_string(&vn).expect("serialize");
        let round: Varnode = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(round, vn);
    }

    #[test]
    fn test_pcode_insn_serialization_roundtrip() {
        let insn = PcodeInsn {
            address: 0x1000,
            seq_num: 0,
            opcode: PcodeOpcode::IntAdd,
            output: Some(reg_vn(0, 8)),
            inputs: vec![reg_vn(1, 8), reg_vn(2, 8)],
        };
        let json = serde_json::to_string(&insn).expect("serialize");
        let round: PcodeInsn = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(round, insn);
    }

    #[test]
    fn test_branch_ind_translates_to_return() {
        let insn = pcode(
            0xC000,
            PcodeOpcode::BranchInd,
            None,
            vec![reg_vn(15, 8)],
        );
        let result = translate_pcode_insn(&insn).expect("should translate");
        assert!(matches!(result.op, AbstractOp::Return { value: Some(_) }));
    }

    #[test]
    fn test_call_ind_translates() {
        let insn = pcode(
            0xD000,
            PcodeOpcode::CallInd,
            Some(reg_vn(0, 8)),
            vec![reg_vn(15, 8), reg_vn(1, 8)],
        );
        let result = translate_pcode_insn(&insn).expect("should translate");
        assert!(matches!(result.op, AbstractOp::Call { .. }));
    }

    #[test]
    fn test_float_add_translates() {
        let insn = pcode(
            0xE000,
            PcodeOpcode::FloatAdd,
            Some(reg_vn(6, 8)),
            vec![reg_vn(7, 8), reg_vn(8, 8)],
        );
        let result = translate_pcode_insn(&insn).expect("should translate");
        assert!(matches!(
            result.op,
            AbstractOp::BinArith { dst: 6, op: BinOp::Add, .. }
        ));
    }
}
