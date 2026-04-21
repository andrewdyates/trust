// trust-lift: Calling convention recovery and stack frame analysis
//
// tRust: #583 — Detects calling conventions from prologue patterns,
// computes stack frame sizes, identifies leaf vs non-leaf functions,
// and recovers callee-saved register spills.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_disasm::instruction::ControlFlow;
use trust_disasm::opcode::Opcode;
use trust_disasm::operand::{MemoryOperand, Operand, Register};
use trust_types::Ty;

use crate::cfg::Cfg;
use crate::lifter::LiftArch;

/// Detected calling convention.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CallingConvention {
    /// AArch64 Procedure Call Standard (ARM 64-bit).
    Aapcs64,
    /// System V AMD64 ABI (x86-64 Linux/macOS).
    SysV64,
    /// Microsoft x64 calling convention (x86-64 Windows).
    Win64,
    /// Could not determine calling convention.
    Unknown,
}

/// Recovered function signature combining arg_count, return type,
/// calling convention, frame size, and callee-saved register info.
#[derive(Debug, Clone)]
pub struct FunctionSignature {
    /// Detected calling convention.
    pub convention: CallingConvention,
    /// Number of arguments (from register usage analysis).
    pub arg_count: usize,
    /// Return type (from return value analysis).
    pub return_ty: Ty,
    /// Stack frame size in bytes (from SP modifications in prologue).
    pub frame_size: u64,
    /// Whether this is a leaf function (no outgoing calls).
    pub is_leaf: bool,
    /// Callee-saved registers spilled in the prologue.
    pub callee_saved: Vec<Register>,
}

/// Detect calling convention from prologue patterns and target architecture.
///
/// **AArch64 (AAPCS64):** Looks for `STP X29, X30, [SP, #-N]!` or
/// `SUB SP, SP, #N` patterns in the entry block.
///
/// **x86-64 (SysV):** Looks for `PUSH RBP` / `MOV RBP, RSP` patterns.
#[must_use]
pub(crate) fn detect_calling_convention(cfg: &Cfg, arch: LiftArch) -> CallingConvention {
    match arch {
        LiftArch::Aarch64 => detect_convention_aarch64(cfg),
        LiftArch::X86_64 => detect_convention_x86_64(cfg),
    }
}

/// Compute stack frame size from SP modifications in the prologue.
///
/// Scans the entry block for instructions that subtract from SP
/// (AArch64: `SUB SP, SP, #N` or `STP ..., [SP, #-N]!`;
/// x86-64: `SUB RSP, N` or `PUSH`).
#[must_use]
pub(crate) fn analyze_frame_size(cfg: &Cfg, arch: LiftArch) -> u64 {
    let entry_block = match cfg.blocks.get(cfg.entry) {
        Some(b) => b,
        None => return 0,
    };

    match arch {
        LiftArch::Aarch64 => analyze_frame_size_aarch64(entry_block),
        LiftArch::X86_64 => analyze_frame_size_x86_64(entry_block),
    }
}

/// Identify callee-saved register spills in the prologue.
///
/// **AArch64:** Detects `STP Xn, Xm, [SP, ...]` where Xn/Xm are
/// callee-saved registers (X19-X28, X29/FP, X30/LR).
///
/// **x86-64:** Detects `PUSH Rn` where Rn is a callee-saved register
/// (RBX, RBP, R12-R15).
#[must_use]
pub(crate) fn detect_callee_saved(cfg: &Cfg, arch: LiftArch) -> Vec<Register> {
    let entry_block = match cfg.blocks.get(cfg.entry) {
        Some(b) => b,
        None => return Vec::new(),
    };

    match arch {
        LiftArch::Aarch64 => detect_callee_saved_aarch64(entry_block),
        LiftArch::X86_64 => detect_callee_saved_x86_64(entry_block),
    }
}

/// Determine if a function is a leaf (makes no outgoing calls).
///
/// Scans all blocks for `BL`/`BLR` (AArch64) or `CALL` (x86-64).
#[must_use]
pub(crate) fn is_leaf_function(cfg: &Cfg) -> bool {
    for block in &cfg.blocks {
        for insn in &block.instructions {
            if insn.flow == ControlFlow::Call {
                return false;
            }
        }
    }
    true
}

/// Build a complete `FunctionSignature` from CFG analysis.
#[must_use]
pub(crate) fn recover_signature(cfg: &Cfg, arch: LiftArch, arg_count: usize, return_ty: Ty) -> FunctionSignature {
    FunctionSignature {
        convention: detect_calling_convention(cfg, arch),
        arg_count,
        return_ty,
        frame_size: analyze_frame_size(cfg, arch),
        is_leaf: is_leaf_function(cfg),
        callee_saved: detect_callee_saved(cfg, arch),
    }
}

// =========================================================================
// AArch64 helpers
// =========================================================================

/// AArch64 callee-saved GPR indices: X19-X28 (indices 19-28),
/// X29/FP (index 29), X30/LR (index 30).
const AARCH64_CALLEE_SAVED: std::ops::RangeInclusive<u8> = 19..=30;

/// Detect AAPCS64 convention by looking for FP/LR save in the prologue.
fn detect_convention_aarch64(cfg: &Cfg) -> CallingConvention {
    let entry_block = match cfg.blocks.get(cfg.entry) {
        Some(b) => b,
        None => return CallingConvention::Unknown,
    };

    for insn in &entry_block.instructions {
        // STP X29, X30, [SP, #-N]! is the canonical AAPCS64 frame setup.
        if insn.opcode == Opcode::Stp
            && is_fp_lr_store(insn) {
                return CallingConvention::Aapcs64;
            }
        // SUB SP, SP, #N also indicates standard AArch64 frame allocation.
        if insn.opcode == Opcode::Sub
            && modifies_sp_aarch64(insn) {
                return CallingConvention::Aapcs64;
            }
    }

    // If no prologue detected but arch is AArch64, it may be a leaf function
    // still using AAPCS64 — return Aapcs64 as the default for the arch.
    CallingConvention::Aapcs64
}

/// Detect SysV convention by looking for PUSH RBP / MOV RBP, RSP.
fn detect_convention_x86_64(cfg: &Cfg) -> CallingConvention {
    let entry_block = match cfg.blocks.get(cfg.entry) {
        Some(b) => b,
        None => return CallingConvention::Unknown,
    };

    for insn in &entry_block.instructions {
        // PUSH RBP is the canonical SysV frame setup.
        if insn.opcode == Opcode::Push
            && let Some(Operand::Reg(reg)) = insn.operand(0) {
                // RBP = GPR index 5 on x86-64.
                if reg.kind == trust_disasm::operand::RegKind::Gpr && reg.index == 5 {
                    return CallingConvention::SysV64;
                }
            }
    }

    // Default for x86-64 without prologue detected.
    CallingConvention::SysV64
}

/// Check if an STP instruction stores FP (X29) and LR (X30).
fn is_fp_lr_store(insn: &trust_disasm::Instruction) -> bool {
    // STP Rt1, Rt2, [Xn, #imm]! has operands: Rt1, Rt2, Mem
    if insn.operand_count() < 3 {
        return false;
    }
    let is_x29 = matches!(insn.operand(0), Some(Operand::Reg(r)) if r.kind == trust_disasm::operand::RegKind::Gpr && r.index == 29);
    let is_x30 = matches!(insn.operand(1), Some(Operand::Reg(r)) if r.kind == trust_disasm::operand::RegKind::Gpr && r.index == 30);
    is_x29 && is_x30
}

/// Check if a SUB instruction modifies SP (SUB SP, SP, #N).
fn modifies_sp_aarch64(insn: &trust_disasm::Instruction) -> bool {
    if insn.operand_count() < 2 {
        return false;
    }
    let dst_is_sp = matches!(insn.operand(0), Some(Operand::Reg(r)) if r.is_stack_pointer());
    let src_is_sp = matches!(insn.operand(1), Some(Operand::Reg(r)) if r.is_stack_pointer());
    dst_is_sp && src_is_sp
}

/// Compute AArch64 frame size from SP modifications.
fn analyze_frame_size_aarch64(block: &crate::cfg::LiftedBlock) -> u64 {
    let mut total: u64 = 0;

    for insn in &block.instructions {
        match insn.opcode {
            // SUB SP, SP, #N — explicit frame allocation.
            Opcode::Sub if modifies_sp_aarch64(insn) => {
                if let Some(Operand::Imm(n)) = insn.operand(2) {
                    total += n;
                }
            }
            // STP ..., [SP, #-N]! — pre-index store that decrements SP.
            Opcode::Stp => {
                if let Some(Operand::Mem(MemoryOperand::PreIndex { base, offset })) = insn.operand(2)
                    && base.is_stack_pointer() && *offset < 0 {
                        total += (-offset) as u64;
                    }
            }
            _ => {}
        }
    }

    total
}

/// Compute x86-64 frame size from RSP modifications.
fn analyze_frame_size_x86_64(block: &crate::cfg::LiftedBlock) -> u64 {
    let mut total: u64 = 0;

    for insn in &block.instructions {
        match insn.opcode {
            // PUSH Rn — each push allocates 8 bytes.
            Opcode::Push => {
                total += 8;
            }
            // SUB RSP, N — explicit frame allocation.
            Opcode::Sub => {
                if insn.operand_count() >= 2 {
                    let dst_is_rsp = matches!(insn.operand(0), Some(Operand::Reg(r))
                        if r.is_stack_pointer() || (r.kind == trust_disasm::operand::RegKind::Gpr && r.index == 4 && r.width == 64));
                    if dst_is_rsp
                        && let Some(Operand::Imm(n)) = insn.operand(1) {
                            total += n;
                        }
                }
            }
            _ => {}
        }
    }

    total
}

/// Detect callee-saved register spills in an AArch64 prologue.
fn detect_callee_saved_aarch64(block: &crate::cfg::LiftedBlock) -> Vec<Register> {
    let mut saved = Vec::new();

    for insn in &block.instructions {
        // STP Xn, Xm, [SP, ...] where Xn/Xm are callee-saved.
        if insn.opcode == Opcode::Stp {
            // Check that the memory operand uses SP as base.
            let mem_is_sp = if insn.operand_count() >= 3 {
                match insn.operand(2) {
                    Some(Operand::Mem(MemoryOperand::PreIndex { base, .. }))
                    | Some(Operand::Mem(MemoryOperand::BaseOffset { base, .. }))
                    | Some(Operand::Mem(MemoryOperand::Base { base })) => base.is_stack_pointer(),
                    _ => false,
                }
            } else {
                false
            };

            if mem_is_sp {
                for op_idx in 0..2 {
                    if let Some(Operand::Reg(r)) = insn.operand(op_idx)
                        && r.kind == trust_disasm::operand::RegKind::Gpr
                            && AARCH64_CALLEE_SAVED.contains(&r.index)
                            && !saved.contains(r) {
                                saved.push(*r);
                            }
                }
            }
        }
        // STR Xn, [SP, ...] for single register saves.
        if insn.opcode == Opcode::Str {
            let mem_is_sp = if insn.operand_count() >= 2 {
                match insn.operand(1) {
                    Some(Operand::Mem(MemoryOperand::PreIndex { base, .. }))
                    | Some(Operand::Mem(MemoryOperand::BaseOffset { base, .. }))
                    | Some(Operand::Mem(MemoryOperand::Base { base })) => base.is_stack_pointer(),
                    _ => false,
                }
            } else {
                false
            };

            if mem_is_sp
                && let Some(Operand::Reg(r)) = insn.operand(0)
                    && r.kind == trust_disasm::operand::RegKind::Gpr
                        && AARCH64_CALLEE_SAVED.contains(&r.index)
                        && !saved.contains(r) {
                            saved.push(*r);
                        }
        }
    }

    saved
}

/// Detect callee-saved register spills in an x86-64 prologue.
///
/// x86-64 SysV callee-saved: RBX(3), RBP(5), R12(12), R13(13), R14(14), R15(15).
fn detect_callee_saved_x86_64(block: &crate::cfg::LiftedBlock) -> Vec<Register> {
    const X86_CALLEE_SAVED: [u8; 6] = [3, 5, 12, 13, 14, 15]; // RBX, RBP, R12-R15
    let mut saved = Vec::new();

    for insn in &block.instructions {
        if insn.opcode == Opcode::Push
            && let Some(Operand::Reg(r)) = insn.operand(0)
                && r.kind == trust_disasm::operand::RegKind::Gpr
                    && X86_CALLEE_SAVED.contains(&r.index)
                    && !saved.contains(r) {
                        saved.push(*r);
                    }
    }

    saved
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_disasm::aarch64::Aarch64Decoder;
    use trust_disasm::arch::Decoder;

    /// Decode an AArch64 instruction from a u32 encoding.
    fn decode_aarch64(encoding: u32) -> trust_disasm::Instruction {
        let bytes = encoding.to_le_bytes();
        let decoder = Aarch64Decoder::new();
        decoder.decode(&bytes, 0x1000).expect("decode should succeed")
    }

    /// Build a CFG with one entry block containing the given instructions.
    fn cfg_with_entry_block(instructions: Vec<trust_disasm::Instruction>) -> Cfg {
        let mut cfg = Cfg::new();
        cfg.add_block(crate::cfg::LiftedBlock {
            id: 0,
            start_addr: 0x1000,
            instructions,
            successors: vec![],
            is_return: true,
        });
        cfg
    }

    /// Build a CFG with multiple blocks.
    fn cfg_with_blocks(blocks: Vec<Vec<trust_disasm::Instruction>>) -> Cfg {
        let mut cfg = Cfg::new();
        for (id, instructions) in blocks.into_iter().enumerate() {
            cfg.add_block(crate::cfg::LiftedBlock {
                id,
                start_addr: 0x1000 + (id as u64 * 0x100),
                instructions,
                successors: vec![],
                is_return: id == 0, // only entry block returns for simplicity
            });
        }
        cfg
    }

    // =====================================================================
    // Leaf function detection
    // =====================================================================

    #[test]
    fn test_leaf_function_ret_only() {
        // RET — no calls, is leaf.
        let cfg = cfg_with_entry_block(vec![
            decode_aarch64(0xD65F03C0), // RET
        ]);
        assert!(is_leaf_function(&cfg));
    }

    #[test]
    fn test_non_leaf_function_bl() {
        // BL target — has a call, not leaf.
        // BL encoding: 0b100101 + imm26. BL +0 = 0x94000000
        let cfg = cfg_with_entry_block(vec![
            decode_aarch64(0x94000000), // BL +0
            decode_aarch64(0xD65F03C0), // RET
        ]);
        assert!(!is_leaf_function(&cfg));
    }

    #[test]
    fn test_non_leaf_function_blr() {
        // BLR X8 — indirect call, not leaf.
        // BLR encoding: 1101011_0001_11111_000000_Rn_00000
        // BLR X8 = 0xD63F0100
        let cfg = cfg_with_entry_block(vec![
            decode_aarch64(0xD63F0100), // BLR X8
            decode_aarch64(0xD65F03C0), // RET
        ]);
        assert!(!is_leaf_function(&cfg));
    }

    #[test]
    fn test_leaf_function_branch_no_call() {
        // B target — unconditional branch but NOT a call, still leaf.
        // B +0 = 0x14000000
        let cfg = cfg_with_entry_block(vec![
            decode_aarch64(0x14000000), // B +0
        ]);
        assert!(is_leaf_function(&cfg));
    }

    #[test]
    fn test_non_leaf_call_in_second_block() {
        // Call is in a non-entry block — still non-leaf.
        let cfg = cfg_with_blocks(vec![
            vec![decode_aarch64(0xD65F03C0)], // block 0: RET
            vec![decode_aarch64(0x94000000)], // block 1: BL +0
        ]);
        assert!(!is_leaf_function(&cfg));
    }

    // =====================================================================
    // Calling convention detection (AArch64)
    // =====================================================================

    #[test]
    fn test_detect_convention_aarch64_stp_fp_lr() {
        // STP X29, X30, [SP, #-16]!
        // Encoding: opc=10, V=0, type=101, imm7=-2(signed 7-bit: 0x7E), Rt2=30, Rn=31(SP), Rt=29
        // Pre-index STP: 10_101_0_011_iiiiiii_Rt2_Rn___Rt
        // imm7 = -16/8 = -2 => 7-bit signed: 1111110 = 0x7E
        // 10_101_0_011_1111110_11110_11111_11101 = 0xA9BF7BFD
        let cfg = cfg_with_entry_block(vec![
            decode_aarch64(0xA9BF7BFD), // STP X29, X30, [SP, #-16]!
            decode_aarch64(0xD65F03C0), // RET
        ]);
        assert_eq!(detect_calling_convention(&cfg, LiftArch::Aarch64), CallingConvention::Aapcs64);
    }

    #[test]
    fn test_detect_convention_aarch64_sub_sp() {
        // SUB SP, SP, #32
        // sf=1, op=1, S=0, sh=0, imm12=32, Rn=31(SP), Rd=31(SP)
        // 1_1_0_10001_0_0_000000100000_11111_11111 = 0xD10083FF
        let cfg = cfg_with_entry_block(vec![
            decode_aarch64(0xD10083FF), // SUB SP, SP, #32
            decode_aarch64(0xD65F03C0), // RET
        ]);
        assert_eq!(detect_calling_convention(&cfg, LiftArch::Aarch64), CallingConvention::Aapcs64);
    }

    #[test]
    fn test_detect_convention_aarch64_leaf_default() {
        // Leaf function with no prologue — still defaults to AAPCS64 on AArch64.
        let cfg = cfg_with_entry_block(vec![
            decode_aarch64(0xD65F03C0), // RET
        ]);
        assert_eq!(detect_calling_convention(&cfg, LiftArch::Aarch64), CallingConvention::Aapcs64);
    }

    #[test]
    fn test_detect_convention_empty_cfg() {
        let cfg = Cfg::new();
        assert_eq!(detect_calling_convention(&cfg, LiftArch::Aarch64), CallingConvention::Unknown);
    }

    // =====================================================================
    // Frame size analysis (AArch64)
    // =====================================================================

    #[test]
    fn test_frame_size_sub_sp() {
        // SUB SP, SP, #64 => frame_size = 64
        // imm12=64 => 0xD10103FF
        let cfg = cfg_with_entry_block(vec![
            decode_aarch64(0xD10103FF), // SUB SP, SP, #64
            decode_aarch64(0xD65F03C0), // RET
        ]);
        assert_eq!(analyze_frame_size(&cfg, LiftArch::Aarch64), 64);
    }

    #[test]
    fn test_frame_size_stp_preindex() {
        // STP X29, X30, [SP, #-16]! => frame_size = 16 (pre-index decrement)
        let cfg = cfg_with_entry_block(vec![
            decode_aarch64(0xA9BF7BFD), // STP X29, X30, [SP, #-16]!
            decode_aarch64(0xD65F03C0), // RET
        ]);
        assert_eq!(analyze_frame_size(&cfg, LiftArch::Aarch64), 16);
    }

    #[test]
    fn test_frame_size_combined_stp_and_sub() {
        // STP X29, X30, [SP, #-16]! + SUB SP, SP, #32 => frame_size = 48
        let cfg = cfg_with_entry_block(vec![
            decode_aarch64(0xA9BF7BFD), // STP X29, X30, [SP, #-16]!
            decode_aarch64(0xD10083FF), // SUB SP, SP, #32
            decode_aarch64(0xD65F03C0), // RET
        ]);
        assert_eq!(analyze_frame_size(&cfg, LiftArch::Aarch64), 48);
    }

    #[test]
    fn test_frame_size_zero_leaf() {
        // Leaf function: RET only => frame_size = 0
        let cfg = cfg_with_entry_block(vec![
            decode_aarch64(0xD65F03C0), // RET
        ]);
        assert_eq!(analyze_frame_size(&cfg, LiftArch::Aarch64), 0);
    }

    #[test]
    fn test_frame_size_empty_cfg() {
        let cfg = Cfg::new();
        assert_eq!(analyze_frame_size(&cfg, LiftArch::Aarch64), 0);
    }

    // =====================================================================
    // Callee-saved register detection (AArch64)
    // =====================================================================

    #[test]
    fn test_callee_saved_fp_lr() {
        // STP X29, X30, [SP, #-16]! — both are callee-saved.
        let cfg = cfg_with_entry_block(vec![
            decode_aarch64(0xA9BF7BFD), // STP X29, X30, [SP, #-16]!
            decode_aarch64(0xD65F03C0), // RET
        ]);
        let saved = detect_callee_saved(&cfg, LiftArch::Aarch64);
        assert_eq!(saved.len(), 2);
        assert!(saved.iter().any(|r| r.index == 29));
        assert!(saved.iter().any(|r| r.index == 30));
    }

    #[test]
    fn test_callee_saved_multiple_pairs() {
        // STP X29, X30, [SP, #-48]!
        // STP X19, X20, [SP, #16] (offset store, not pre-index)
        //
        // STP X19, X20, [SP, #16]:
        // opc=10, V=0, type=010, imm7=16/8=2 => 0000010, Rt2=20, Rn=31(SP), Rt=19
        // 10_101_0_010_0000010_10100_11111_10011 = 0xA9025FF3
        let cfg = cfg_with_entry_block(vec![
            decode_aarch64(0xA9BF7BFD), // STP X29, X30, [SP, #-48]!
            decode_aarch64(0xA90153F3), // STP X19, X20, [SP, #16]
            decode_aarch64(0xD65F03C0), // RET
        ]);
        let saved = detect_callee_saved(&cfg, LiftArch::Aarch64);
        // Debug: print decoded instructions and saved registers
        let insn2 = decode_aarch64(0xA9025FF3);
        eprintln!("insn2 opcode: {:?}, operand_count: {}", insn2.opcode, insn2.operand_count());
        for i in 0..insn2.operand_count() {
            eprintln!("  operand[{i}]: {:?}", insn2.operand(i));
        }
        eprintln!("saved registers: {:?}", saved);
        assert_eq!(saved.len(), 4);
        assert!(saved.iter().any(|r| r.index == 19));
        assert!(saved.iter().any(|r| r.index == 20));
        assert!(saved.iter().any(|r| r.index == 29));
        assert!(saved.iter().any(|r| r.index == 30));
    }

    #[test]
    fn test_callee_saved_none_leaf() {
        // Leaf function with no register saves.
        let cfg = cfg_with_entry_block(vec![
            decode_aarch64(0xD65F03C0), // RET
        ]);
        let saved = detect_callee_saved(&cfg, LiftArch::Aarch64);
        assert!(saved.is_empty());
    }

    #[test]
    fn test_callee_saved_non_callee_saved_not_detected() {
        // STP X0, X1, [SP, #-16]! — X0, X1 are NOT callee-saved.
        // opc=10, V=0, type=101, imm7=-2, Rt2=1, Rn=31(SP), Rt=0
        // 10_101_0_011_1111110_00001_11111_00000 = 0xA9BF07E0
        let cfg = cfg_with_entry_block(vec![
            decode_aarch64(0xA9BF07E0), // STP X0, X1, [SP, #-16]!
            decode_aarch64(0xD65F03C0), // RET
        ]);
        let saved = detect_callee_saved(&cfg, LiftArch::Aarch64);
        assert!(saved.is_empty());
    }

    #[test]
    fn test_callee_saved_empty_cfg() {
        let cfg = Cfg::new();
        let saved = detect_callee_saved(&cfg, LiftArch::Aarch64);
        assert!(saved.is_empty());
    }

    // =====================================================================
    // Full signature recovery
    // =====================================================================

    #[test]
    fn test_recover_signature_leaf() {
        // Simple leaf function: RET only.
        let cfg = cfg_with_entry_block(vec![
            decode_aarch64(0xD65F03C0), // RET
        ]);
        let sig = recover_signature(&cfg, LiftArch::Aarch64, 0, Ty::Unit);
        assert_eq!(sig.convention, CallingConvention::Aapcs64);
        assert_eq!(sig.arg_count, 0);
        assert_eq!(sig.return_ty, Ty::Unit);
        assert_eq!(sig.frame_size, 0);
        assert!(sig.is_leaf);
        assert!(sig.callee_saved.is_empty());
    }

    #[test]
    fn test_recover_signature_standard_prologue() {
        // Standard AAPCS64 function:
        // STP X29, X30, [SP, #-16]!
        // SUB SP, SP, #32
        // BL target
        // RET
        let cfg = cfg_with_entry_block(vec![
            decode_aarch64(0xA9BF7BFD), // STP X29, X30, [SP, #-16]!
            decode_aarch64(0xD10083FF), // SUB SP, SP, #32
            decode_aarch64(0x94000000), // BL +0
            decode_aarch64(0xD65F03C0), // RET
        ]);
        let sig = recover_signature(&cfg, LiftArch::Aarch64, 2, Ty::Int { width: 64, signed: true });
        assert_eq!(sig.convention, CallingConvention::Aapcs64);
        assert_eq!(sig.arg_count, 2);
        assert_eq!(sig.return_ty, Ty::Int { width: 64, signed: true });
        assert_eq!(sig.frame_size, 48); // 16 (STP) + 32 (SUB)
        assert!(!sig.is_leaf); // has BL
        assert_eq!(sig.callee_saved.len(), 2); // X29, X30
    }
}
