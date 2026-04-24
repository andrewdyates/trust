// trust-lift: Semantic lifting — convert machine Effects to tMIR Statements
//
// This module bridges trust-machine-sem (instruction semantics as Effects) with
// trust-types (tMIR Statements). Each Effect becomes one or more tMIR Statements
// that faithfully represent the instruction's behavior in the verification IR.
//
// tRust: #573 — architecture-aware semantic lifting (AArch64 + x86_64).
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_disasm::ControlFlow;
use trust_machine_sem::{Aarch64Semantics, Effect, MachineState, Semantics, X86_64Semantics};
use trust_types::{
    BasicBlock as TmirBlock, BlockId, ConstValue, Formula, LocalDecl, Operand, Place, Rvalue,
    SourceSpan, Statement, Terminator, Ty,
};

use crate::cfg::{Cfg, LiftedBlock};
use crate::error::LiftError;
use crate::lifter::LiftArch;

/// Local variable layout for a lifted function.
///
/// Maps machine registers, SP, PC, flags, and memory to tMIR local indices.
/// Public so that downstream crates (e.g. trust-vcgen) can reference layout
/// indices without hardcoding magic constants.
///
/// Architecture-aware: use `LocalLayout::aarch64()` or `LocalLayout::x86_64()`
/// to get the correct register file mapping.
#[derive(Debug, Clone)]
pub struct LocalLayout {
    /// _0: return place
    pub return_local: usize,
    /// Base index of GPR locals (GPR[i] = gpr_base + i).
    pub gpr_base: usize,
    /// Number of general-purpose registers in this layout.
    pub gpr_count: usize,
    /// Stack pointer local index.
    pub sp_local: usize,
    /// Program counter local index.
    pub pc_local: usize,
    /// Flag locals — mapped to architecture-specific condition flags.
    /// AArch64: N, Z, C, V. x86_64: CF, ZF, SF, OF.
    pub flag_n: usize,
    pub flag_z: usize,
    pub flag_c: usize,
    pub flag_v: usize,
    /// Memory (array) local index.
    pub mem_local: usize,
    /// Total number of locals.
    pub total: usize,
    /// Human-readable GPR names for `to_local_decls()`.
    gpr_names: GprNames,
    /// Human-readable flag names for `to_local_decls()`.
    flag_names: [&'static str; 4],
}

/// GPR naming strategy — avoids heap allocation for static register names.
#[derive(Debug, Clone)]
enum GprNames {
    /// AArch64: X0..X30 (31 registers).
    Aarch64,
    /// x86_64: RAX, RCX, RDX, RBX, RSP, RBP, RSI, RDI, R8-R15 (16 registers).
    X86_64,
}

/// x86_64 GPR names in index order (matching standard register encoding).
const X86_64_GPR_NAMES: [&str; 16] = [
    "RAX", "RCX", "RDX", "RBX", "RSP", "RBP", "RSI", "RDI", "R8", "R9", "R10", "R11", "R12", "R13",
    "R14", "R15",
];

impl LocalLayout {
    /// AArch64 layout: 0=return, 1-31=X0-X30, 32=SP, 33=PC, 34-37=NZCV, 38=MEM.
    #[must_use]
    pub fn aarch64() -> Self {
        Self {
            return_local: 0,
            gpr_base: 1,
            gpr_count: 31,
            sp_local: 32,
            pc_local: 33,
            flag_n: 34,
            flag_z: 35,
            flag_c: 36,
            flag_v: 37,
            mem_local: 38,
            total: 39,
            gpr_names: GprNames::Aarch64,
            flag_names: ["N", "Z", "C", "V"],
        }
    }

    /// Alias for `aarch64()` — backward compatibility.
    #[must_use]
    pub fn standard() -> Self {
        Self::aarch64()
    }

    /// x86_64 layout: 0=return, 1-16=RAX-R15, 17=RSP, 18=RIP, 19-22=CF/ZF/SF/OF, 23=MEM.
    ///
    /// 16 GPRs (RAX through R15), plus RSP (dedicated stack pointer local),
    /// RIP (program counter), 4 flags (CF/ZF/SF/OF), and MEM. Total: 24.
    #[must_use]
    pub fn x86_64() -> Self {
        Self {
            return_local: 0,
            gpr_base: 1,
            gpr_count: 16,
            sp_local: 17,
            pc_local: 18,
            // x86_64 EFLAGS: CF, ZF, SF, OF
            flag_n: 19,
            flag_z: 20,
            flag_c: 21,
            flag_v: 22,
            mem_local: 23,
            total: 24,
            gpr_names: GprNames::X86_64,
            flag_names: ["CF", "ZF", "SF", "OF"],
        }
    }

    /// Get the local index for a GPR by register index.
    pub(crate) fn gpr(&self, index: u8) -> usize {
        self.gpr_base + index as usize
    }

    /// Build the LocalDecl vector for tMIR.
    pub(crate) fn to_local_decls(&self) -> Vec<LocalDecl> {
        let mut decls = Vec::with_capacity(self.total);

        // _0: return (u64)
        decls.push(LocalDecl {
            index: 0,
            ty: Ty::Int { width: 64, signed: false },
            name: Some("_lifted_result".to_string()),
        });

        // GPRs
        for i in 0..self.gpr_count {
            let name = match &self.gpr_names {
                GprNames::Aarch64 => format!("X{i}"),
                GprNames::X86_64 => X86_64_GPR_NAMES
                    .get(i)
                    .map(|s| s.to_string())
                    .unwrap_or_else(|| format!("GPR{i}")),
            };
            decls.push(LocalDecl {
                index: self.gpr(i as u8),
                ty: Ty::Int { width: 64, signed: false },
                name: Some(name),
            });
        }

        // SP
        decls.push(LocalDecl {
            index: self.sp_local,
            ty: Ty::Int { width: 64, signed: false },
            name: Some("SP".to_string()),
        });

        // PC
        decls.push(LocalDecl {
            index: self.pc_local,
            ty: Ty::Int { width: 64, signed: false },
            name: Some("PC".to_string()),
        });

        // Flags
        for (idx, name) in [
            (self.flag_n, self.flag_names[0]),
            (self.flag_z, self.flag_names[1]),
            (self.flag_c, self.flag_names[2]),
            (self.flag_v, self.flag_names[3]),
        ] {
            decls.push(LocalDecl { index: idx, ty: Ty::Bool, name: Some(name.to_string()) });
        }

        // MEM (modeled as u64 for now — semantics are in the formulas)
        decls.push(LocalDecl {
            index: self.mem_local,
            ty: Ty::Int { width: 64, signed: false },
            name: Some("MEM".to_string()),
        });

        decls
    }
}

/// Convert a Formula to a tMIR Operand.
///
/// Concrete bitvector/boolean constants are lowered to ConstValue for readability;
/// all other formulas become Operand::Symbolic.
fn formula_to_operand(formula: &Formula) -> Operand {
    match formula {
        Formula::BitVec { value, width } => {
            // Non-negative bitvec constants can be represented as ConstValue::Uint.
            if *value >= 0 {
                Operand::Constant(ConstValue::Uint(*value as u128, *width))
            } else {
                Operand::Symbolic(formula.clone())
            }
        }
        Formula::Bool(b) => Operand::Constant(ConstValue::Bool(*b)),
        // Everything else (variables, operations, etc.) is symbolic.
        _ => Operand::Symbolic(formula.clone()),
    }
}

fn strict_lift_error(message: impl Into<String>) -> LiftError {
    LiftError::Ssa(format!("semantic lift proof mode: {}", message.into()))
}

/// Convert a single Effect into tMIR Statement(s).
///
/// # tRust: #564 — uses actual Formula values from Effects
///
/// Each Effect variant carries Formula fields describing the actual computation.
/// We emit those into tMIR via `Operand::Symbolic(formula)` so downstream VC
/// generation reasons over real semantics, not placeholders.
fn effect_to_stmts(
    effect: &Effect,
    layout: &LocalLayout,
    binary_addr: u64,
) -> Result<Vec<Statement>, LiftError> {
    let span = SourceSpan {
        file: format!("binary:0x{binary_addr:x}"),
        line_start: 0,
        col_start: 0,
        line_end: 0,
        col_end: 0,
    };

    match effect {
        Effect::RegWrite { index, value, .. } => {
            // tRust: #573 — architecture-aware GPR bounds.
            // AArch64: index 31 is ZR (writes are no-ops).
            // x86_64: all 16 GPR indices (0-15) are real registers.
            if (*index as usize) >= layout.gpr_count {
                return Ok(vec![Statement::Nop]);
            }
            // tRust: #564 — emit actual formula value, not placeholder zero.
            Ok(vec![Statement::Assign {
                place: Place::local(layout.gpr(*index)),
                rvalue: Rvalue::Use(formula_to_operand(value)),
                span,
            }])
        }
        Effect::SpWrite { value } => {
            // tRust: #564 — emit actual SP formula.
            Ok(vec![Statement::Assign {
                place: Place::local(layout.sp_local),
                rvalue: Rvalue::Use(formula_to_operand(value)),
                span,
            }])
        }
        Effect::MemWrite { address, value, .. } => {
            // tRust: #564 — emit Store(MEM, address, value) formula.
            let store_formula = Formula::Store(
                Box::new(Formula::Var(
                    "MEM".into(),
                    trust_types::Sort::Array(
                        Box::new(trust_types::Sort::BitVec(64)),
                        Box::new(trust_types::Sort::BitVec(8)),
                    ),
                )),
                Box::new(address.clone()),
                Box::new(value.clone()),
            );
            Ok(vec![Statement::Assign {
                place: Place::local(layout.mem_local),
                rvalue: Rvalue::Use(Operand::Symbolic(store_formula)),
                span,
            }])
        }
        Effect::MemRead { .. } => {
            // Memory reads are modeled as part of the subsequent RegWrite
            Ok(vec![Statement::Nop])
        }
        Effect::FlagUpdate { n, z, c, v } => {
            // tRust: #564 — emit actual flag formulas, not placeholder false.
            Ok(vec![
                Statement::Assign {
                    place: Place::local(layout.flag_n),
                    rvalue: Rvalue::Use(formula_to_operand(n)),
                    span: span.clone(),
                },
                Statement::Assign {
                    place: Place::local(layout.flag_z),
                    rvalue: Rvalue::Use(formula_to_operand(z)),
                    span: span.clone(),
                },
                Statement::Assign {
                    place: Place::local(layout.flag_c),
                    rvalue: Rvalue::Use(formula_to_operand(c)),
                    span: span.clone(),
                },
                Statement::Assign {
                    place: Place::local(layout.flag_v),
                    rvalue: Rvalue::Use(formula_to_operand(v)),
                    span,
                },
            ])
        }
        Effect::Branch { .. } | Effect::ConditionalBranch { .. } => {
            // Branches are handled at the terminator level, not as statements
            Ok(vec![])
        }
        Effect::Call { .. } => {
            // Calls: link register write is handled by RegWrite effect
            Ok(vec![])
        }
        Effect::Return { .. } => {
            // Returns are handled at the terminator level
            Ok(vec![])
        }
        Effect::PcUpdate { value } => {
            // tRust: #564 — emit actual PC formula.
            Ok(vec![Statement::Assign {
                place: Place::local(layout.pc_local),
                rvalue: Rvalue::Use(formula_to_operand(value)),
                span,
            }])
        }
        Effect::FpRegWrite { index, width, .. } => Err(strict_lift_error(format!(
            "unsupported FP register write effect at binary:0x{binary_addr:x}: V{index} width {width}; no tMIR FP local layout is available"
        ))),
        _ => Err(strict_lift_error(format!(
            "unsupported effect at binary:0x{binary_addr:x}: {effect:?}"
        ))),
    }
}

fn successor_block_id(
    cfg: &Cfg,
    block: &LiftedBlock,
    successor_addr: u64,
    ordinal: usize,
) -> Result<BlockId, LiftError> {
    cfg.block_index(successor_addr)
        .map(BlockId)
        .ok_or_else(|| {
            strict_lift_error(format!(
                "block {} at 0x{:x} successor #{ordinal} points to 0x{successor_addr:x}, which is not a recovered block",
                block.id, block.start_addr
            ))
        })
}

fn bitvec_mask(width: u32) -> Option<u128> {
    match width {
        0 => None,
        64 => Some(u128::from(u64::MAX)),
        1..=63 => Some((1u128 << width) - 1),
        _ => None,
    }
}

fn bitvec_value_to_u64(value: i128, width: u32) -> Option<u64> {
    let mask = bitvec_mask(width)?;
    let modulus = mask + 1;
    let normalized = if value < 0 {
        let modulus = i128::try_from(modulus).ok()?;
        value.rem_euclid(modulus) as u128
    } else {
        u128::try_from(value).ok()?
    };

    if normalized <= mask { u64::try_from(normalized).ok() } else { None }
}

fn constant_pc_value(formula: &Formula) -> Option<u64> {
    match formula {
        Formula::BitVec { value, width } => bitvec_value_to_u64(*value, *width),
        Formula::UInt(value) => u64::try_from(*value).ok(),
        Formula::Int(value) => u64::try_from(*value).ok(),
        Formula::BvAdd(lhs, rhs, width) => {
            let mask = bitvec_mask(*width)?;
            let lhs = u128::from(constant_pc_value(lhs)?);
            let rhs = u128::from(constant_pc_value(rhs)?);
            u64::try_from((lhs.wrapping_add(rhs)) & mask).ok()
        }
        Formula::BvSub(lhs, rhs, width) => {
            let mask = bitvec_mask(*width)?;
            let lhs = u128::from(constant_pc_value(lhs)?);
            let rhs = u128::from(constant_pc_value(rhs)?);
            u64::try_from((lhs.wrapping_sub(rhs)) & mask).ok()
        }
        Formula::BvZeroExt(inner, width) => {
            let mask = bitvec_mask(*width)?;
            u64::try_from(u128::from(constant_pc_value(inner)?) & mask).ok()
        }
        Formula::IntToBv(inner, width) => {
            let value = match inner.as_ref() {
                Formula::Int(value) => *value,
                Formula::UInt(value) => i128::try_from(*value).ok()?,
                Formula::BitVec { value, .. } => *value,
                _ => return None,
            };
            bitvec_value_to_u64(value, *width)
        }
        _ => None,
    }
}

fn branch_discr_from_final_pc_update(
    block: &LiftedBlock,
    value: &Formula,
    target_addr: u64,
    fallthrough_addr: u64,
) -> Result<Operand, LiftError> {
    let Formula::Ite(condition, target, fallthrough) = value else {
        return Err(strict_lift_error(format!(
            "block {} at 0x{:x} has two CFG successors but no conditional branch semantics",
            block.id, block.start_addr
        )));
    };

    let actual_target = constant_pc_value(target).ok_or_else(|| {
        strict_lift_error(format!(
            "block {} at 0x{:x} final PC ITE target is not a constant address: {target:?}",
            block.id, block.start_addr
        ))
    })?;
    let actual_fallthrough = constant_pc_value(fallthrough).ok_or_else(|| {
        strict_lift_error(format!(
            "block {} at 0x{:x} final PC ITE fallthrough is not a constant address: {fallthrough:?}",
            block.id, block.start_addr
        ))
    })?;

    if actual_target != target_addr || actual_fallthrough != fallthrough_addr {
        return Err(strict_lift_error(format!(
            "block {} at 0x{:x} final PC ITE destinations do not match recovered CFG: target 0x{actual_target:x} vs 0x{target_addr:x}, fallthrough 0x{actual_fallthrough:x} vs 0x{fallthrough_addr:x}",
            block.id, block.start_addr
        )));
    }

    Ok(Operand::Symbolic(condition.as_ref().clone()))
}

fn conditional_branch_discr(
    block: &LiftedBlock,
    effects_for_block: &[Effect],
    state: &MachineState,
    target_addr: u64,
    fallthrough_addr: u64,
) -> Result<Operand, LiftError> {
    if let Some(discr) = effects_for_block.iter().rev().find_map(|eff| {
        if let Effect::ConditionalBranch { condition, .. } = eff {
            Some(Operand::Symbolic(trust_machine_sem::condition_to_formula(state, *condition)))
        } else {
            None
        }
    }) {
        return Ok(discr);
    }

    match effects_for_block.last() {
        Some(Effect::PcUpdate { value }) => {
            branch_discr_from_final_pc_update(block, value, target_addr, fallthrough_addr)
        }
        _ => Err(strict_lift_error(format!(
            "block {} at 0x{:x} has two CFG successors but no conditional branch semantics",
            block.id, block.start_addr
        ))),
    }
}

fn is_terminal_direct_external_branch(block: &LiftedBlock, cfg: &Cfg) -> Result<bool, LiftError> {
    let Some(last) = block.instructions.last() else {
        return Ok(false);
    };

    if !matches!(last.flow, ControlFlow::Branch | ControlFlow::ConditionalBranch) {
        return Ok(false);
    }

    let Some(target) = last.branch_target() else {
        return Err(strict_lift_error(format!(
            "block {} at 0x{:x} ends in {:?} without a direct branch target",
            block.id, block.start_addr, last.flow
        )));
    };

    if cfg.block_index(target).is_some() {
        return Err(strict_lift_error(format!(
            "block {} at 0x{:x} branches to recovered block 0x{target:x} but has no CFG successor",
            block.id, block.start_addr
        )));
    }

    Ok(true)
}

/// Determine the tMIR terminator for a lifted block based on its effects and successors.
///
/// # tRust: #564 — wire condition formulas into SwitchInt
fn block_terminator(
    block: &LiftedBlock,
    cfg: &Cfg,
    effects_for_block: &[Effect],
    state: &MachineState,
) -> Result<Terminator, LiftError> {
    if block.is_return {
        return Ok(Terminator::Return);
    }

    if matches!(block.instructions.last().map(|insn| insn.flow), Some(ControlFlow::Exception)) {
        return Ok(Terminator::Unreachable);
    }

    match block.successors.len() {
        0 if matches!(block.instructions.last().map(|insn| insn.flow), Some(ControlFlow::Call)) => {
            Ok(Terminator::Unreachable)
        }
        0 if is_terminal_direct_external_branch(block, cfg)? => Ok(Terminator::Unreachable),
        0 => Err(strict_lift_error(format!(
            "block {} at 0x{:x} has no successors and is not marked as a return",
            block.id, block.start_addr
        ))),
        1 => {
            if matches!(
                block.instructions.last().map(|insn| insn.flow),
                Some(ControlFlow::ConditionalBranch)
            ) {
                return Err(strict_lift_error(format!(
                    "block {} at 0x{:x} has one CFG successor for a conditional branch; existing tMIR edges cannot represent a mixed in-function/external branch",
                    block.id, block.start_addr
                )));
            }
            let target = successor_block_id(cfg, block, block.successors[0], 0)?;
            Ok(Terminator::Goto(target))
        }
        2 => {
            let fallthrough = successor_block_id(cfg, block, block.successors[0], 0)?;
            let target = successor_block_id(cfg, block, block.successors[1], 1)?;
            let last_addr =
                block.instructions.last().map(|i| i.address).unwrap_or(block.start_addr);

            // tRust: #564 — extract condition from ConditionalBranch effect, or from a
            // final PC update ITE for branch forms whose semantics update PC directly.
            let discr = conditional_branch_discr(
                block,
                effects_for_block,
                state,
                block.successors[1],
                block.successors[0],
            )?;

            Ok(Terminator::SwitchInt {
                discr,
                targets: vec![(1, target)],
                otherwise: fallthrough,
                span: SourceSpan {
                    file: format!("binary:0x{last_addr:x}"),
                    line_start: 0,
                    col_start: 0,
                    line_end: 0,
                    col_end: 0,
                },
            })
        }
        n => Err(strict_lift_error(format!(
            "block {} at 0x{:x} has {n} CFG successors; strict semantic lifting only supports 0, 1, or 2",
            block.id, block.start_addr
        ))),
    }
}

/// Lift an entire CFG into tMIR blocks using real instruction semantics.
///
/// # tRust: #573 — architecture-aware semantic lifting
///
/// Dispatches to the appropriate ISA semantics and register layout based on
/// the target architecture.
pub(crate) fn lift_cfg_semantic(
    cfg: &Cfg,
    arch: LiftArch,
) -> Result<(Vec<TmirBlock>, LocalLayout), LiftError> {
    match arch {
        LiftArch::Aarch64 => {
            lift_cfg_with_semantics(cfg, &Aarch64Semantics, LocalLayout::aarch64())
        }
        LiftArch::X86_64 => lift_cfg_with_semantics(cfg, &X86_64Semantics, LocalLayout::x86_64()),
    }
}

/// Inner lifting loop, generic over the ISA semantics implementation.
fn lift_cfg_with_semantics(
    cfg: &Cfg,
    semantics: &dyn Semantics,
    layout: LocalLayout,
) -> Result<(Vec<TmirBlock>, LocalLayout), LiftError> {
    let mut tmir_blocks = Vec::with_capacity(cfg.blocks.len());

    for block in &cfg.blocks {
        let mut stmts = Vec::new();
        let mut state = MachineState::symbolic();
        let mut block_effects: Vec<Effect> = Vec::new();

        for insn in &block.instructions {
            state.pc = trust_types::Formula::BitVec { value: insn.address as i128, width: 64 };

            let effects = semantics.effects(&state, insn).map_err(|err| {
                strict_lift_error(format!(
                    "unsupported instruction semantics at binary:0x{:x} opcode {:?}: {err}",
                    insn.address, insn.opcode
                ))
            })?;

            for effect in &effects {
                let mut new_stmts = effect_to_stmts(effect, &layout, insn.address)?;
                stmts.append(&mut new_stmts);
                apply_effect_to_state(&mut state, effect);
                block_effects.push(effect.clone());
            }
        }

        stmts.retain(|s| !matches!(s, Statement::Nop));
        let terminator = block_terminator(block, cfg, &block_effects, &state)?;

        tmir_blocks.push(TmirBlock { id: BlockId(block.id), stmts, terminator });
    }

    Ok((tmir_blocks, layout))
}

/// Update the symbolic MachineState based on an Effect.
fn apply_effect_to_state(state: &mut MachineState, effect: &Effect) {
    match effect {
        Effect::RegWrite { index, value, .. } if (*index as usize) < state.gpr.len() => {
            state.gpr[*index as usize] = value.clone();
        }
        Effect::SpWrite { value } => {
            state.sp = value.clone();
        }
        Effect::PcUpdate { value } => {
            state.pc = value.clone();
        }
        Effect::MemWrite { .. } => {}
        Effect::FlagUpdate { n, z, c, v } => {
            state.flags.n = n.clone();
            state.flags.z = z.clone();
            state.flags.c = c.clone();
            state.flags.v = v.clone();
        }
        _ => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_local_layout_standard() {
        let layout = LocalLayout::standard();
        assert_eq!(layout.gpr(0), 1);
        assert_eq!(layout.gpr(30), 31);
        assert_eq!(layout.sp_local, 32);
        assert_eq!(layout.pc_local, 33);
        assert_eq!(layout.total, 39);
    }

    #[test]
    fn test_local_layout_aarch64() {
        let layout = LocalLayout::aarch64();
        assert_eq!(layout.gpr_count, 31);
        assert_eq!(layout.gpr(0), 1);
        assert_eq!(layout.gpr(30), 31);
        assert_eq!(layout.sp_local, 32);
        assert_eq!(layout.pc_local, 33);
        assert_eq!(layout.flag_n, 34);
        assert_eq!(layout.flag_z, 35);
        assert_eq!(layout.flag_c, 36);
        assert_eq!(layout.flag_v, 37);
        assert_eq!(layout.mem_local, 38);
        assert_eq!(layout.total, 39);
    }

    #[test]
    fn test_local_layout_x86_64() {
        let layout = LocalLayout::x86_64();
        assert_eq!(layout.gpr_count, 16);
        assert_eq!(layout.gpr(0), 1); // RAX
        assert_eq!(layout.gpr(15), 16); // R15
        assert_eq!(layout.sp_local, 17);
        assert_eq!(layout.pc_local, 18);
        assert_eq!(layout.flag_n, 19); // CF
        assert_eq!(layout.flag_z, 20); // ZF
        assert_eq!(layout.flag_c, 21); // SF
        assert_eq!(layout.flag_v, 22); // OF
        assert_eq!(layout.mem_local, 23);
        assert_eq!(layout.total, 24);
    }

    #[test]
    fn test_local_decls_count() {
        let layout = LocalLayout::standard();
        let decls = layout.to_local_decls();
        assert_eq!(decls.len(), layout.total);
    }

    #[test]
    fn test_local_decls_count_x86_64() {
        let layout = LocalLayout::x86_64();
        let decls = layout.to_local_decls();
        assert_eq!(decls.len(), layout.total);
    }

    #[test]
    fn test_x86_64_gpr_names() {
        let layout = LocalLayout::x86_64();
        let decls = layout.to_local_decls();
        assert_eq!(decls[1].name.as_deref(), Some("RAX"));
        assert_eq!(decls[2].name.as_deref(), Some("RCX"));
        assert_eq!(decls[3].name.as_deref(), Some("RDX"));
        assert_eq!(decls[4].name.as_deref(), Some("RBX"));
        assert_eq!(decls[5].name.as_deref(), Some("RSP"));
        assert_eq!(decls[6].name.as_deref(), Some("RBP"));
        assert_eq!(decls[7].name.as_deref(), Some("RSI"));
        assert_eq!(decls[8].name.as_deref(), Some("RDI"));
        assert_eq!(decls[9].name.as_deref(), Some("R8"));
        assert_eq!(decls[16].name.as_deref(), Some("R15"));
    }

    #[test]
    fn test_x86_64_flag_names() {
        let layout = LocalLayout::x86_64();
        let decls = layout.to_local_decls();
        let flag_decls: Vec<_> = decls.iter().filter(|d| d.ty == Ty::Bool).collect();
        assert_eq!(flag_decls.len(), 4);
        assert_eq!(flag_decls[0].name.as_deref(), Some("CF"));
        assert_eq!(flag_decls[1].name.as_deref(), Some("ZF"));
        assert_eq!(flag_decls[2].name.as_deref(), Some("SF"));
        assert_eq!(flag_decls[3].name.as_deref(), Some("OF"));
    }

    #[test]
    fn test_lift_empty_cfg_aarch64() {
        let cfg = Cfg::new();
        let (blocks, layout) =
            lift_cfg_semantic(&cfg, LiftArch::Aarch64).expect("empty CFG should lift");
        assert!(blocks.is_empty());
        assert_eq!(layout.total, 39);
    }

    #[test]
    fn test_lift_empty_cfg_x86_64() {
        let cfg = Cfg::new();
        let (blocks, layout) =
            lift_cfg_semantic(&cfg, LiftArch::X86_64).expect("empty CFG should lift");
        assert!(blocks.is_empty());
        assert_eq!(layout.total, 24);
    }

    #[test]
    fn test_block_terminator_return() {
        let cfg = Cfg::new();
        let block = LiftedBlock {
            id: 0,
            start_addr: 0x1000,
            instructions: vec![],
            successors: vec![],
            is_return: true,
        };
        let state = MachineState::symbolic();
        assert!(matches!(
            block_terminator(&block, &cfg, &[], &state).expect("return terminator"),
            Terminator::Return
        ));
    }

    #[test]
    fn test_block_terminator_missing_successor_fails_strict() {
        let mut cfg = Cfg::new();
        let block = LiftedBlock {
            id: 0,
            start_addr: 0x1000,
            instructions: vec![],
            successors: vec![0x2000],
            is_return: false,
        };
        cfg.add_block(block.clone());
        let state = MachineState::symbolic();

        let err = block_terminator(&block, &cfg, &[], &state).expect_err("missing successor");
        assert!(err.to_string().contains("successor #0"));
    }

    #[test]
    fn test_block_terminator_two_successors_requires_condition() {
        let mut cfg = Cfg::new();
        let block = LiftedBlock {
            id: 0,
            start_addr: 0x1000,
            instructions: vec![],
            successors: vec![0x1010, 0x1020],
            is_return: false,
        };
        cfg.add_block(block.clone());
        cfg.add_block(LiftedBlock {
            id: 1,
            start_addr: 0x1010,
            instructions: vec![],
            successors: vec![],
            is_return: true,
        });
        cfg.add_block(LiftedBlock {
            id: 2,
            start_addr: 0x1020,
            instructions: vec![],
            successors: vec![],
            is_return: true,
        });
        let state = MachineState::symbolic();

        let err = block_terminator(&block, &cfg, &[], &state).expect_err("missing condition");
        assert!(err.to_string().contains("no conditional branch semantics"));
    }

    #[test]
    fn test_block_terminator_pc_update_ite_mismatch_fails_strict() {
        let mut cfg = Cfg::new();
        let block = LiftedBlock {
            id: 0,
            start_addr: 0x1000,
            instructions: vec![],
            successors: vec![0x1004, 0x1020],
            is_return: false,
        };
        cfg.add_block(block.clone());
        cfg.add_block(LiftedBlock {
            id: 1,
            start_addr: 0x1004,
            instructions: vec![],
            successors: vec![],
            is_return: true,
        });
        cfg.add_block(LiftedBlock {
            id: 2,
            start_addr: 0x1020,
            instructions: vec![],
            successors: vec![],
            is_return: true,
        });

        let pc_update = Effect::PcUpdate {
            value: Formula::Ite(
                Box::new(Formula::Var("take_branch".into(), trust_types::Sort::Bool)),
                Box::new(Formula::BitVec { value: 0x1030, width: 64 }),
                Box::new(Formula::BitVec { value: 0x1004, width: 64 }),
            ),
        };
        let state = MachineState::symbolic();

        let err = block_terminator(&block, &cfg, &[pc_update], &state)
            .expect_err("mismatched PC ITE destinations should fail");
        assert!(err.to_string().contains("do not match recovered CFG"));
    }

    #[test]
    fn test_block_terminator_last_call_without_successor_is_unreachable() {
        let cfg = Cfg::new();
        let block = LiftedBlock {
            id: 0,
            start_addr: 0x1000,
            instructions: vec![decode_aarch64(0x94000040, 0x1000)], // BL #0x100
            successors: vec![],
            is_return: false,
        };
        let state = MachineState::symbolic();

        assert!(matches!(
            block_terminator(&block, &cfg, &[], &state).expect("last call should lift"),
            Terminator::Unreachable
        ));
    }

    #[test]
    fn test_lift_direct_external_branch_is_unreachable() {
        let mut cfg = Cfg::new();
        cfg.add_block(LiftedBlock {
            id: 0,
            start_addr: 0x1000,
            instructions: vec![decode_aarch64(0x14000040, 0x1000)], // B #0x100 -> 0x1100
            successors: vec![],
            is_return: false,
        });

        let (blocks, _) = lift_cfg_semantic(&cfg, LiftArch::Aarch64)
            .expect("direct external branch should lift as terminal unreachable");
        assert_eq!(blocks.len(), 1);
        assert!(matches!(blocks[0].terminator, Terminator::Unreachable));
    }

    #[test]
    fn test_effect_regwrite_to_stmt() {
        let layout = LocalLayout::standard();
        let formula = trust_types::Formula::BitVec { value: 42, width: 64 };
        let effect = Effect::RegWrite { index: 5, width: 64, value: formula.clone() };
        let stmts = effect_to_stmts(&effect, &layout, 0x1000).expect("RegWrite should lift");
        assert_eq!(stmts.len(), 1);
        match &stmts[0] {
            Statement::Assign { place, rvalue, .. } => {
                assert_eq!(place.local, layout.gpr(5));
                match rvalue {
                    Rvalue::Use(Operand::Constant(ConstValue::Uint(42, 64))) => {}
                    _ => panic!("expected Uint(42, 64), got: {rvalue:?}"),
                }
            }
            _ => panic!("expected Assign"),
        }
    }

    #[test]
    fn test_effect_zr_write_is_nop() {
        let layout = LocalLayout::standard();
        let effect = Effect::RegWrite {
            index: 31,
            width: 64,
            value: trust_types::Formula::BitVec { value: 0, width: 64 },
        };
        let stmts = effect_to_stmts(&effect, &layout, 0x1000).expect("ZR write should lift");
        assert_eq!(stmts.len(), 1);
        assert!(matches!(stmts[0], Statement::Nop));
    }

    /// tRust: #573 — x86_64 has 16 GPRs; index >= 16 is a Nop.
    #[test]
    fn test_effect_regwrite_x86_64_out_of_range_is_nop() {
        let layout = LocalLayout::x86_64();
        let effect = Effect::RegWrite {
            index: 16,
            width: 64,
            value: trust_types::Formula::BitVec { value: 0, width: 64 },
        };
        let stmts =
            effect_to_stmts(&effect, &layout, 0x1000).expect("out-of-range write should lift");
        assert_eq!(stmts.len(), 1);
        assert!(matches!(stmts[0], Statement::Nop));
    }

    /// tRust: #573 — x86_64 GPR index 15 (R15) should produce a valid Assign.
    #[test]
    fn test_effect_regwrite_x86_64_r15() {
        let layout = LocalLayout::x86_64();
        let effect = Effect::RegWrite {
            index: 15,
            width: 64,
            value: trust_types::Formula::BitVec { value: 99, width: 64 },
        };
        let stmts = effect_to_stmts(&effect, &layout, 0x1000).expect("R15 write should lift");
        assert_eq!(stmts.len(), 1);
        match &stmts[0] {
            Statement::Assign { place, .. } => {
                assert_eq!(place.local, layout.gpr(15));
            }
            _ => panic!("expected Assign for R15"),
        }
    }

    #[test]
    fn test_effect_regwrite_symbolic_formula_preserved() {
        let layout = LocalLayout::standard();
        let sym_formula = Formula::BvAdd(
            Box::new(Formula::Var("X1".into(), trust_types::Sort::BitVec(64))),
            Box::new(Formula::Var("X2".into(), trust_types::Sort::BitVec(64))),
            64,
        );
        let effect = Effect::RegWrite { index: 0, width: 64, value: sym_formula.clone() };
        let stmts = effect_to_stmts(&effect, &layout, 0x2000).expect("symbolic RegWrite");
        assert_eq!(stmts.len(), 1);
        match &stmts[0] {
            Statement::Assign { place, rvalue, .. } => {
                assert_eq!(place.local, layout.gpr(0));
                match rvalue {
                    Rvalue::Use(Operand::Symbolic(f)) => assert_eq!(f, &sym_formula),
                    _ => panic!("expected Symbolic operand, got: {rvalue:?}"),
                }
            }
            _ => panic!("expected Assign"),
        }
    }

    #[test]
    fn test_effect_sp_write_carries_formula() {
        let layout = LocalLayout::standard();
        let sp_formula = Formula::BvSub(
            Box::new(Formula::Var("SP".into(), trust_types::Sort::BitVec(64))),
            Box::new(Formula::BitVec { value: 16, width: 64 }),
            64,
        );
        let effect = Effect::SpWrite { value: sp_formula.clone() };
        let stmts = effect_to_stmts(&effect, &layout, 0x3000).expect("SP write");
        assert_eq!(stmts.len(), 1);
        match &stmts[0] {
            Statement::Assign { place, rvalue, .. } => {
                assert_eq!(place.local, layout.sp_local);
                match rvalue {
                    Rvalue::Use(Operand::Symbolic(f)) => assert_eq!(f, &sp_formula),
                    _ => panic!("expected Symbolic operand, got: {rvalue:?}"),
                }
            }
            _ => panic!("expected Assign"),
        }
    }

    #[test]
    fn test_effect_flag_update_carries_formulas() {
        let layout = LocalLayout::standard();
        let n_formula = Formula::BvSLt(
            Box::new(Formula::Var("result".into(), trust_types::Sort::BitVec(64))),
            Box::new(Formula::BitVec { value: 0, width: 64 }),
            64,
        );
        let z_formula = Formula::Eq(
            Box::new(Formula::Var("result".into(), trust_types::Sort::BitVec(64))),
            Box::new(Formula::BitVec { value: 0, width: 64 }),
        );
        let effect = Effect::FlagUpdate {
            n: n_formula.clone(),
            z: z_formula.clone(),
            c: Formula::Bool(false),
            v: Formula::Bool(false),
        };
        let stmts = effect_to_stmts(&effect, &layout, 0x4000).expect("flag update");
        assert_eq!(stmts.len(), 4);

        match &stmts[0] {
            Statement::Assign { place, rvalue, .. } => {
                assert_eq!(place.local, layout.flag_n);
                match rvalue {
                    Rvalue::Use(Operand::Symbolic(f)) => assert_eq!(f, &n_formula),
                    _ => panic!("expected Symbolic for N flag, got: {rvalue:?}"),
                }
            }
            _ => panic!("expected Assign for N flag"),
        }

        match &stmts[1] {
            Statement::Assign { place, rvalue, .. } => {
                assert_eq!(place.local, layout.flag_z);
                match rvalue {
                    Rvalue::Use(Operand::Symbolic(f)) => assert_eq!(f, &z_formula),
                    _ => panic!("expected Symbolic for Z flag, got: {rvalue:?}"),
                }
            }
            _ => panic!("expected Assign for Z flag"),
        }

        match &stmts[2] {
            Statement::Assign { place, rvalue, .. } => {
                assert_eq!(place.local, layout.flag_c);
                match rvalue {
                    Rvalue::Use(Operand::Constant(ConstValue::Bool(false))) => {}
                    _ => panic!("expected Bool(false) for C flag, got: {rvalue:?}"),
                }
            }
            _ => panic!("expected Assign for C flag"),
        }
    }

    #[test]
    fn test_effect_mem_write_carries_formulas() {
        let layout = LocalLayout::standard();
        let addr_formula = Formula::Var("addr".into(), trust_types::Sort::BitVec(64));
        let val_formula = Formula::Var("val".into(), trust_types::Sort::BitVec(64));
        let effect = Effect::MemWrite {
            address: addr_formula.clone(),
            value: val_formula.clone(),
            width_bytes: 8,
        };
        let stmts = effect_to_stmts(&effect, &layout, 0x5000).expect("memory write");
        assert_eq!(stmts.len(), 1);
        match &stmts[0] {
            Statement::Assign { place, rvalue, .. } => {
                assert_eq!(place.local, layout.mem_local);
                match rvalue {
                    Rvalue::Use(Operand::Symbolic(Formula::Store(_, addr, val))) => {
                        assert_eq!(addr.as_ref(), &addr_formula);
                        assert_eq!(val.as_ref(), &val_formula);
                    }
                    _ => panic!("expected Symbolic(Store(...)), got: {rvalue:?}"),
                }
            }
            _ => panic!("expected Assign"),
        }
    }

    #[test]
    fn test_effect_pc_update_carries_formula() {
        let layout = LocalLayout::standard();
        let pc_formula = Formula::BvAdd(
            Box::new(Formula::Var("PC".into(), trust_types::Sort::BitVec(64))),
            Box::new(Formula::BitVec { value: 4, width: 64 }),
            64,
        );
        let effect = Effect::PcUpdate { value: pc_formula.clone() };
        let stmts = effect_to_stmts(&effect, &layout, 0x6000).expect("PC update");
        assert_eq!(stmts.len(), 1);
        match &stmts[0] {
            Statement::Assign { place, rvalue, .. } => {
                assert_eq!(place.local, layout.pc_local);
                match rvalue {
                    Rvalue::Use(Operand::Symbolic(f)) => assert_eq!(f, &pc_formula),
                    _ => panic!("expected Symbolic for PC update, got: {rvalue:?}"),
                }
            }
            _ => panic!("expected Assign"),
        }
    }

    // ====================================================================
    // tRust: #573 — End-to-end x86_64 semantic lifting tests
    // ====================================================================

    /// Helper: decode an x86_64 instruction from a byte slice.
    fn decode_x86_64(bytes: &[u8], addr: u64) -> trust_disasm::Instruction {
        trust_disasm::decode_x86_64(bytes, addr).expect("x86_64 decode should succeed")
    }

    /// Helper: decode an AArch64 instruction from a u32 encoding.
    fn decode_aarch64(encoding: u32, addr: u64) -> trust_disasm::Instruction {
        trust_disasm::decode_aarch64(&encoding.to_le_bytes(), addr)
            .expect("AArch64 decode should succeed")
    }

    /// Build a CFG with one entry block containing the given instructions.
    fn cfg_with_block(instructions: Vec<trust_disasm::Instruction>, is_return: bool) -> Cfg {
        let mut cfg = Cfg::new();
        cfg.add_block(LiftedBlock {
            id: 0,
            start_addr: 0x1000,
            instructions,
            successors: vec![],
            is_return,
        });
        cfg
    }

    #[test]
    fn test_lift_cbz_derives_switch_from_pc_update_ite() {
        let mut cfg = Cfg::new();
        cfg.add_block(LiftedBlock {
            id: 0,
            start_addr: 0x1000,
            instructions: vec![decode_aarch64(0xB4000080, 0x1000)], // CBZ X0, #0x10
            successors: vec![0x1004, 0x1010],
            is_return: false,
        });
        cfg.add_block(LiftedBlock {
            id: 1,
            start_addr: 0x1004,
            instructions: vec![],
            successors: vec![],
            is_return: true,
        });
        cfg.add_block(LiftedBlock {
            id: 2,
            start_addr: 0x1010,
            instructions: vec![],
            successors: vec![],
            is_return: true,
        });

        let (blocks, _) =
            lift_cfg_semantic(&cfg, LiftArch::Aarch64).expect("CBZ should lift through PC ITE");
        match &blocks[0].terminator {
            Terminator::SwitchInt { discr, targets, otherwise, .. } => {
                assert!(matches!(discr, Operand::Symbolic(Formula::Eq(_, _))));
                assert_eq!(targets, &vec![(1, BlockId(2))]);
                assert_eq!(*otherwise, BlockId(1));
            }
            other => panic!("expected SwitchInt, got {other:?}"),
        }
    }

    #[test]
    fn test_lift_unsupported_semantics_fails_strict() {
        let cfg = cfg_with_block(
            vec![
                decode_aarch64(0xD53B4200, 0x1000), // MRS X0, NZCV
                decode_aarch64(0xD65F03C0, 0x1004), // RET
            ],
            true,
        );

        let err = lift_cfg_semantic(&cfg, LiftArch::Aarch64).expect_err("MRS is unsupported");
        let message = err.to_string();
        assert!(message.contains("unsupported instruction semantics"));
        assert!(message.contains("Mrs"));
    }

    /// tRust: #573 — x86_64 RET-only function lifts to a single Return block.
    #[test]
    fn test_x86_64_lift_ret_only() {
        let cfg = cfg_with_block(
            vec![decode_x86_64(&[0xC3], 0x1000)], // RET
            true,
        );
        let (blocks, layout) =
            lift_cfg_semantic(&cfg, LiftArch::X86_64).expect("should lift x86_64 RET");
        assert_eq!(blocks.len(), 1);
        assert_eq!(layout.total, 24); // x86_64 layout
        assert!(
            matches!(blocks[0].terminator, Terminator::Return),
            "RET block should have Return terminator"
        );
    }

    /// tRust: #573 — x86_64 MOV produces a register write in tMIR.
    #[test]
    fn test_x86_64_lift_mov_reg_reg() {
        // 48 89 E5 = MOV RBP, RSP
        // C3 = RET
        let cfg = cfg_with_block(
            vec![decode_x86_64(&[0x48, 0x89, 0xE5], 0x1000), decode_x86_64(&[0xC3], 0x1003)],
            true,
        );
        let (blocks, layout) =
            lift_cfg_semantic(&cfg, LiftArch::X86_64).expect("should lift x86_64 MOV");
        assert_eq!(blocks.len(), 1);

        // MOV RBP, RSP should produce an Assign to RBP (index 5 => local gpr(5)).
        let rbp_local = layout.gpr(5);
        let has_rbp_assign = blocks[0]
            .stmts
            .iter()
            .any(|s| matches!(s, Statement::Assign { place, .. } if place.local == rbp_local));
        assert!(has_rbp_assign, "MOV RBP, RSP should write RBP local");
    }

    /// tRust: #573 — x86_64 ADD produces register write and flag updates.
    #[test]
    fn test_x86_64_lift_add_sets_flags() {
        // 48 01 D0 = ADD RAX, RDX
        // C3 = RET
        let cfg = cfg_with_block(
            vec![decode_x86_64(&[0x48, 0x01, 0xD0], 0x1000), decode_x86_64(&[0xC3], 0x1003)],
            true,
        );
        let (blocks, layout) =
            lift_cfg_semantic(&cfg, LiftArch::X86_64).expect("should lift x86_64 ADD");
        assert_eq!(blocks.len(), 1);

        // ADD RAX, RDX writes RAX (index 0 => local gpr(0)).
        let rax_local = layout.gpr(0);
        let has_rax_assign = blocks[0]
            .stmts
            .iter()
            .any(|s| matches!(s, Statement::Assign { place, .. } if place.local == rax_local));
        assert!(has_rax_assign, "ADD RAX, RDX should write RAX local");

        // ADD also sets EFLAGS (CF, ZF, SF, OF).
        let has_cf_assign = blocks[0]
            .stmts
            .iter()
            .any(|s| matches!(s, Statement::Assign { place, .. } if place.local == layout.flag_n));
        assert!(has_cf_assign, "ADD should set flag locals");
    }

    /// tRust: #573 — x86_64 SUB RSP produces SP write.
    #[test]
    fn test_x86_64_lift_sub_rsp() {
        // 48 83 EC 20 = SUB RSP, 0x20
        // C3 = RET
        let cfg = cfg_with_block(
            vec![decode_x86_64(&[0x48, 0x83, 0xEC, 0x20], 0x1000), decode_x86_64(&[0xC3], 0x1004)],
            true,
        );
        let (blocks, layout) =
            lift_cfg_semantic(&cfg, LiftArch::X86_64).expect("should lift x86_64 SUB RSP");
        assert_eq!(blocks.len(), 1);

        // SUB RSP, 0x20 should write the SP local.
        let has_sp_assign = blocks[0].stmts.iter().any(
            |s| matches!(s, Statement::Assign { place, .. } if place.local == layout.sp_local),
        );
        assert!(has_sp_assign, "SUB RSP, 0x20 should write SP local");
    }

    /// tRust: #573 — x86_64 CMP produces flags but no register write.
    #[test]
    fn test_x86_64_lift_cmp_no_writeback() {
        // 48 39 C8 = CMP RAX, RCX
        // C3 = RET
        let cfg = cfg_with_block(
            vec![decode_x86_64(&[0x48, 0x39, 0xC8], 0x1000), decode_x86_64(&[0xC3], 0x1003)],
            true,
        );
        let (blocks, layout) =
            lift_cfg_semantic(&cfg, LiftArch::X86_64).expect("should lift x86_64 CMP");
        assert_eq!(blocks.len(), 1);

        // CMP should NOT write RAX.
        let rax_local = layout.gpr(0);
        let has_rax_assign = blocks[0]
            .stmts
            .iter()
            .any(|s| matches!(s, Statement::Assign { place, .. } if place.local == rax_local));
        assert!(!has_rax_assign, "CMP should not write RAX");

        // CMP should set flags.
        let has_flag_assign = blocks[0]
            .stmts
            .iter()
            .any(|s| matches!(s, Statement::Assign { place, .. } if place.local == layout.flag_z));
        assert!(has_flag_assign, "CMP should set ZF flag");
    }

    /// tRust: #573 — x86_64 XOR EAX, EAX (zero idiom) lifts correctly.
    #[test]
    fn test_x86_64_lift_xor_zero_idiom() {
        // 31 C0 = XOR EAX, EAX
        // C3 = RET
        let cfg = cfg_with_block(
            vec![decode_x86_64(&[0x31, 0xC0], 0x1000), decode_x86_64(&[0xC3], 0x1002)],
            true,
        );
        let (blocks, layout) =
            lift_cfg_semantic(&cfg, LiftArch::X86_64).expect("should lift x86_64 XOR");
        assert_eq!(blocks.len(), 1);

        // XOR EAX, EAX should write EAX (32-bit RegWrite maps to RAX local).
        let rax_local = layout.gpr(0);
        let has_rax_assign = blocks[0]
            .stmts
            .iter()
            .any(|s| matches!(s, Statement::Assign { place, .. } if place.local == rax_local));
        assert!(has_rax_assign, "XOR EAX, EAX should write RAX local");
    }

    /// tRust: #573 — x86_64 PUSH/POP produces SP + MEM writes in tMIR.
    #[test]
    fn test_x86_64_lift_push_pop() {
        // 55 = PUSH RBP
        // 5D = POP RBP
        // C3 = RET
        let cfg = cfg_with_block(
            vec![
                decode_x86_64(&[0x55], 0x1000),
                decode_x86_64(&[0x5D], 0x1001),
                decode_x86_64(&[0xC3], 0x1002),
            ],
            true,
        );
        let (blocks, layout) =
            lift_cfg_semantic(&cfg, LiftArch::X86_64).expect("should lift x86_64 PUSH/POP");
        assert_eq!(blocks.len(), 1);

        // PUSH writes SP and MEM; POP writes SP and RBP.
        let has_sp_assign = blocks[0].stmts.iter().any(
            |s| matches!(s, Statement::Assign { place, .. } if place.local == layout.sp_local),
        );
        let has_mem_assign = blocks[0].stmts.iter().any(
            |s| matches!(s, Statement::Assign { place, .. } if place.local == layout.mem_local),
        );
        let rbp_local = layout.gpr(5);
        let has_rbp_assign = blocks[0]
            .stmts
            .iter()
            .any(|s| matches!(s, Statement::Assign { place, .. } if place.local == rbp_local));
        assert!(has_sp_assign, "PUSH/POP should write SP local");
        assert!(has_mem_assign, "PUSH should write MEM local");
        assert!(has_rbp_assign, "POP should write RBP local");
    }

    /// tRust: #573 — x86_64 typical function prologue lifts end-to-end.
    ///
    /// Tests a realistic sequence: PUSH RBP; MOV RBP, RSP; SUB RSP, 0x20; ... ADD RSP, 0x20; POP RBP; RET
    #[test]
    fn test_x86_64_lift_function_prologue_epilogue() {
        let cfg = cfg_with_block(
            vec![
                decode_x86_64(&[0x55], 0x1000),                   // PUSH RBP
                decode_x86_64(&[0x48, 0x89, 0xE5], 0x1001),       // MOV RBP, RSP
                decode_x86_64(&[0x48, 0x83, 0xEC, 0x20], 0x1004), // SUB RSP, 0x20
                decode_x86_64(&[0x48, 0x83, 0xC4, 0x20], 0x1008), // ADD RSP, 0x20
                decode_x86_64(&[0x5D], 0x100C),                   // POP RBP
                decode_x86_64(&[0xC3], 0x100D),                   // RET
            ],
            true,
        );
        let (blocks, layout) = lift_cfg_semantic(&cfg, LiftArch::X86_64)
            .expect("should lift x86_64 prologue/epilogue");
        assert_eq!(blocks.len(), 1);
        assert_eq!(layout.total, 24);
        assert!(
            matches!(blocks[0].terminator, Terminator::Return),
            "function should terminate with Return"
        );

        // Verify multiple register/SP writes are produced.
        let assign_count =
            blocks[0].stmts.iter().filter(|s| matches!(s, Statement::Assign { .. })).count();
        assert!(
            assign_count >= 6,
            "prologue/epilogue should produce at least 6 Assign statements, got {assign_count}"
        );
    }

    /// tRust: #573 — x86_64 NOP produces only PC advance (no Assign after Nop removal).
    #[test]
    fn test_x86_64_lift_nop_minimal() {
        // 90 = NOP
        // C3 = RET
        let cfg = cfg_with_block(
            vec![decode_x86_64(&[0x90], 0x1000), decode_x86_64(&[0xC3], 0x1001)],
            true,
        );
        let (blocks, layout) =
            lift_cfg_semantic(&cfg, LiftArch::X86_64).expect("should lift x86_64 NOP");
        assert_eq!(blocks.len(), 1);
        assert_eq!(layout.total, 24);

        // NOP produces only a PcUpdate (which becomes an Assign to PC).
        // RET produces MemRead(Nop), SpWrite, Return(empty), PcUpdate -> 2 Assigns.
        // Total non-Nop assigns: at least the PC update from NOP.
        let pc_assigns = blocks[0]
            .stmts
            .iter()
            .filter(
                |s| matches!(s, Statement::Assign { place, .. } if place.local == layout.pc_local),
            )
            .count();
        assert!(pc_assigns >= 1, "NOP should produce at least one PC Assign");
    }
}
