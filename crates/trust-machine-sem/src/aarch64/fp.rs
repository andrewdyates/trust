// trust-machine-sem: AArch64 FP/SIMD instruction semantics
//
// Models floating-point operations using bitvector approximations. Since
// trust-types Formula does not yet have dedicated FP sorts, we model FP
// arithmetic as bitvector operations of the appropriate width. This is an
// over-approximation: the solver treats them as integer bitvector ops, which
// is sufficient for control-flow analysis and memory modeling but not for
// precise FP value reasoning.
//
// Limitation: When Formula gains FP sorts (IEEE 754), BvAdd/BvSub/etc.
// should be replaced with FpAdd/FpSub/etc. for bit-exact FP semantics.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_disasm::Instruction;
use trust_disasm::operand::{Operand, RegKind};
use trust_types::Formula;

use crate::effect::Effect;
use crate::error::SemError;
use crate::state::MachineState;

use super::{Aarch64Semantics, condition_to_formula, extract_condition, pc_advance};

impl Aarch64Semantics {
    // -------------------------------------------------------------------
    // Scalar FP arithmetic: FADD, FSUB, FMUL, FDIV
    // -------------------------------------------------------------------

    /// FADD: Fd = Fn + Fm (FP add, modeled as BvAdd).
    pub(super) fn sem_fadd(
        &self,
        state: &MachineState,
        insn: &Instruction,
    ) -> Result<Vec<Effect>, SemError> {
        self.fp_binop(state, insn, |a, b, w| Formula::BvAdd(Box::new(a), Box::new(b), w))
    }

    /// FSUB: Fd = Fn - Fm (FP subtract, modeled as BvSub).
    pub(super) fn sem_fsub(
        &self,
        state: &MachineState,
        insn: &Instruction,
    ) -> Result<Vec<Effect>, SemError> {
        self.fp_binop(state, insn, |a, b, w| Formula::BvSub(Box::new(a), Box::new(b), w))
    }

    /// FMUL: Fd = Fn * Fm (FP multiply, modeled as BvMul).
    pub(super) fn sem_fmul(
        &self,
        state: &MachineState,
        insn: &Instruction,
    ) -> Result<Vec<Effect>, SemError> {
        self.fp_binop(state, insn, |a, b, w| Formula::BvMul(Box::new(a), Box::new(b), w))
    }

    /// FDIV: Fd = Fn / Fm (FP divide, modeled as BvSDiv).
    pub(super) fn sem_fdiv(
        &self,
        state: &MachineState,
        insn: &Instruction,
    ) -> Result<Vec<Effect>, SemError> {
        self.fp_binop(state, insn, |a, b, w| Formula::BvSDiv(Box::new(a), Box::new(b), w))
    }

    /// Shared implementation for FP binary ops: Fd = op(Fn, Fm).
    fn fp_binop(
        &self,
        state: &MachineState,
        insn: &Instruction,
        op: impl FnOnce(Formula, Formula, u32) -> Formula,
    ) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, width) = extract_fp_dst(insn)?;
        let fn_val = read_fp_operand(state, insn, 1, width)?;
        let fm_val = read_fp_operand(state, insn, 2, width)?;

        let result = op(fn_val, fm_val, width);
        let mut effects = vec![Effect::FpRegWrite { index: dst_idx, width, value: result }];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    // -------------------------------------------------------------------
    // FP compare: FCMP
    // -------------------------------------------------------------------

    /// FCMP: compare Fn and Fm (or Fn and 0.0), set NZCV.
    ///
    /// AArch64 FCMP flag semantics (IEEE 754 comparison):
    /// - Equal:       NZCV = 0110
    /// - Less than:   NZCV = 1000
    /// - Greater than: NZCV = 0010
    /// - Unordered:   NZCV = 0011 (NaN)
    ///
    /// We model this as a bitvector signed comparison (approximation).
    pub(super) fn sem_fcmp(
        &self,
        state: &MachineState,
        insn: &Instruction,
    ) -> Result<Vec<Effect>, SemError> {
        let (rn_idx, width) = extract_fp_reg(insn, 0)?;
        let fn_val = state.read_fpr(rn_idx, width);

        let fm_val = match insn.operand(1) {
            Some(Operand::Imm(0)) => Formula::BitVec { value: 0, width },
            Some(Operand::Reg(r)) if r.kind == RegKind::Simd => {
                state.read_fpr(r.index, u32::from(r.width))
            }
            _ => {
                return Err(SemError::InvalidOperand {
                    opcode: insn.opcode,
                    index: 1,
                    detail: "expected FP register or zero".into(),
                });
            }
        };

        // Model as signed comparison for approximation.
        let is_equal = Formula::Eq(Box::new(fn_val.clone()), Box::new(fm_val.clone()));
        let is_less = Formula::BvSLt(Box::new(fn_val.clone()), Box::new(fm_val.clone()), width);

        // N = 1 if fn < fm (less than)
        let n = is_less.clone();
        // Z = 1 if fn == fm (equal)
        let z = is_equal.clone();
        // C = 1 if fn >= fm (greater or equal) — i.e., NOT less than
        let c = Formula::Not(Box::new(is_less));
        // V = 0 (we cannot model NaN/unordered with bitvectors)
        let v = Formula::Bool(false);

        let mut effects = vec![Effect::FlagUpdate { n, z, c, v }];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    // -------------------------------------------------------------------
    // FP move: FMOV (register and immediate)
    // -------------------------------------------------------------------

    /// FMOV (register): Fd = Fn, or GPR<->FP transfer.
    pub(super) fn sem_fmov_reg(
        &self,
        state: &MachineState,
        insn: &Instruction,
    ) -> Result<Vec<Effect>, SemError> {
        let dst = match insn.operand(0) {
            Some(Operand::Reg(r)) => r,
            _ => {
                return Err(SemError::InvalidOperand {
                    opcode: insn.opcode,
                    index: 0,
                    detail: "expected register".into(),
                });
            }
        };
        let src = match insn.operand(1) {
            Some(Operand::Reg(r)) => r,
            _ => {
                return Err(SemError::InvalidOperand {
                    opcode: insn.opcode,
                    index: 1,
                    detail: "expected register".into(),
                });
            }
        };

        let dst_width = u32::from(dst.width);
        let src_width = u32::from(src.width);

        // Read source value.
        let src_val = match src.kind {
            RegKind::Simd => state.read_fpr(src.index, src_width),
            RegKind::Gpr => state.read_gpr(src.index, src_width),
            RegKind::Zr => Formula::BitVec { value: 0, width: src_width },
            _ => {
                return Err(SemError::InvalidOperand {
                    opcode: insn.opcode,
                    index: 1,
                    detail: format!("unexpected register kind: {:?}", src.kind),
                });
            }
        };

        // Match widths if needed (truncate or zero-extend for bit transfer).
        let value = if src_width == dst_width {
            src_val
        } else if src_width > dst_width {
            Formula::BvExtract { inner: Box::new(src_val), high: dst_width - 1, low: 0 }
        } else {
            Formula::BvZeroExt(Box::new(src_val), dst_width)
        };

        // Write to destination.
        let effect = match dst.kind {
            RegKind::Simd => Effect::FpRegWrite { index: dst.index, width: dst_width, value },
            RegKind::Gpr => Effect::RegWrite { index: dst.index, width: dst_width, value },
            _ => {
                return Err(SemError::InvalidOperand {
                    opcode: insn.opcode,
                    index: 0,
                    detail: format!("unexpected destination kind: {:?}", dst.kind),
                });
            }
        };

        Ok(vec![effect, pc_advance(state, insn)])
    }

    /// FMOV (immediate): Fd = imm8 (expanded to FP constant).
    ///
    /// The 8-bit immediate encodes an FP constant per AArch64 spec.
    /// We store the raw imm8 as a bitvector for now.
    pub(super) fn sem_fmov_imm(
        &self,
        state: &MachineState,
        insn: &Instruction,
    ) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, width) = extract_fp_dst(insn)?;

        let imm8 = match insn.operand(1) {
            Some(Operand::Imm(v)) => *v,
            _ => {
                return Err(SemError::InvalidOperand {
                    opcode: insn.opcode,
                    index: 1,
                    detail: "expected immediate".into(),
                });
            }
        };

        // Expand imm8 to FP constant per AArch64 spec.
        let value = expand_fp_imm8(imm8, width);

        let mut effects = vec![Effect::FpRegWrite { index: dst_idx, width, value }];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    // -------------------------------------------------------------------
    // FP unary: FNEG, FABS, FSQRT
    // -------------------------------------------------------------------

    /// FNEG: Fd = -Fn. Modeled as two's complement negation (BvSub(0, Fn)).
    pub(super) fn sem_fneg(
        &self,
        state: &MachineState,
        insn: &Instruction,
    ) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, width) = extract_fp_dst(insn)?;
        let fn_val = read_fp_operand(state, insn, 1, width)?;

        // FP negate: flip sign bit. For IEEE 754, this is XOR with sign-bit mask.
        let sign_mask = Formula::BvShl(
            Box::new(Formula::BitVec { value: 1, width }),
            Box::new(Formula::BitVec { value: i128::from(width - 1), width }),
            width,
        );
        let result = Formula::BvXor(Box::new(fn_val), Box::new(sign_mask), width);

        let mut effects = vec![Effect::FpRegWrite { index: dst_idx, width, value: result }];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// FABS: Fd = |Fn|. Clear the sign bit.
    pub(super) fn sem_fabs(
        &self,
        state: &MachineState,
        insn: &Instruction,
    ) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, width) = extract_fp_dst(insn)?;
        let fn_val = read_fp_operand(state, insn, 1, width)?;

        // Clear sign bit: AND with ~(1 << (width-1)).
        let sign_mask = Formula::BvShl(
            Box::new(Formula::BitVec { value: 1, width }),
            Box::new(Formula::BitVec { value: i128::from(width - 1), width }),
            width,
        );
        let inv_mask = Formula::BvNot(Box::new(sign_mask), width);
        let result = Formula::BvAnd(Box::new(fn_val), Box::new(inv_mask), width);

        let mut effects = vec![Effect::FpRegWrite { index: dst_idx, width, value: result }];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// FSQRT: Fd = sqrt(Fn). No bitvector equivalent -- model as identity
    /// (the value passes through unchanged). This is an over-approximation
    /// that preserves dataflow without modeling the actual square root.
    pub(super) fn sem_fsqrt(
        &self,
        state: &MachineState,
        insn: &Instruction,
    ) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, width) = extract_fp_dst(insn)?;
        let fn_val = read_fp_operand(state, insn, 1, width)?;

        // Over-approximation: Fd = Fn (preserves dataflow).
        let mut effects = vec![Effect::FpRegWrite { index: dst_idx, width, value: fn_val }];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    // -------------------------------------------------------------------
    // FP conversion: FCVTZS, FCVTZU, SCVTF, UCVTF, FCVT
    // -------------------------------------------------------------------

    /// FCVTZS: Convert FP to signed integer, rounding toward zero.
    /// Modeled as bitvector extraction/sign-extension from FP width to int width.
    pub(super) fn sem_fcvtzs(
        &self,
        state: &MachineState,
        insn: &Instruction,
    ) -> Result<Vec<Effect>, SemError> {
        self.sem_fp_to_int(state, insn, true)
    }

    /// FCVTZU: Convert FP to unsigned integer, rounding toward zero.
    pub(super) fn sem_fcvtzu(
        &self,
        state: &MachineState,
        insn: &Instruction,
    ) -> Result<Vec<Effect>, SemError> {
        self.sem_fp_to_int(state, insn, false)
    }

    /// Shared FP-to-int conversion.
    fn sem_fp_to_int(
        &self,
        state: &MachineState,
        insn: &Instruction,
        _signed: bool,
    ) -> Result<Vec<Effect>, SemError> {
        let dst = match insn.operand(0) {
            Some(Operand::Reg(r)) => r,
            _ => {
                return Err(SemError::InvalidOperand {
                    opcode: insn.opcode,
                    index: 0,
                    detail: "expected register".into(),
                });
            }
        };
        let src = match insn.operand(1) {
            Some(Operand::Reg(r)) => r,
            _ => {
                return Err(SemError::InvalidOperand {
                    opcode: insn.opcode,
                    index: 1,
                    detail: "expected register".into(),
                });
            }
        };

        let dst_width = u32::from(dst.width);
        let src_width = u32::from(src.width);
        let src_val = state.read_fpr(src.index, src_width);

        // Model FP-to-int as bitvector reinterpretation (truncate or extend).
        let value = if src_width == dst_width {
            src_val
        } else if src_width > dst_width {
            Formula::BvExtract { inner: Box::new(src_val), high: dst_width - 1, low: 0 }
        } else {
            Formula::BvZeroExt(Box::new(src_val), dst_width)
        };

        let mut effects = vec![Effect::RegWrite { index: dst.index, width: dst_width, value }];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// SCVTF: Convert signed integer to FP.
    pub(super) fn sem_scvtf(
        &self,
        state: &MachineState,
        insn: &Instruction,
    ) -> Result<Vec<Effect>, SemError> {
        self.sem_int_to_fp(state, insn)
    }

    /// UCVTF: Convert unsigned integer to FP.
    pub(super) fn sem_ucvtf(
        &self,
        state: &MachineState,
        insn: &Instruction,
    ) -> Result<Vec<Effect>, SemError> {
        self.sem_int_to_fp(state, insn)
    }

    /// Shared int-to-FP conversion.
    fn sem_int_to_fp(
        &self,
        state: &MachineState,
        insn: &Instruction,
    ) -> Result<Vec<Effect>, SemError> {
        let dst = match insn.operand(0) {
            Some(Operand::Reg(r)) => r,
            _ => {
                return Err(SemError::InvalidOperand {
                    opcode: insn.opcode,
                    index: 0,
                    detail: "expected register".into(),
                });
            }
        };
        let src = match insn.operand(1) {
            Some(Operand::Reg(r)) => r,
            _ => {
                return Err(SemError::InvalidOperand {
                    opcode: insn.opcode,
                    index: 1,
                    detail: "expected register".into(),
                });
            }
        };

        let dst_width = u32::from(dst.width);
        let src_width = u32::from(src.width);
        let src_val = state.read_gpr(src.index, src_width);

        // Model int-to-FP as bitvector reinterpretation (truncate or extend).
        let value = if src_width == dst_width {
            src_val
        } else if src_width > dst_width {
            Formula::BvExtract { inner: Box::new(src_val), high: dst_width - 1, low: 0 }
        } else {
            Formula::BvZeroExt(Box::new(src_val), dst_width)
        };

        let mut effects = vec![Effect::FpRegWrite { index: dst.index, width: dst_width, value }];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// FCVT: Convert between FP precisions (e.g., S->D, D->S).
    pub(super) fn sem_fcvt(
        &self,
        state: &MachineState,
        insn: &Instruction,
    ) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, dst_width) = extract_fp_dst(insn)?;
        let (src_idx, src_width) = extract_fp_reg(insn, 1)?;
        let src_val = state.read_fpr(src_idx, src_width);

        // Width conversion: truncate or zero-extend.
        let value = if src_width == dst_width {
            src_val
        } else if src_width > dst_width {
            Formula::BvExtract { inner: Box::new(src_val), high: dst_width - 1, low: 0 }
        } else {
            Formula::BvZeroExt(Box::new(src_val), dst_width)
        };

        let mut effects = vec![Effect::FpRegWrite { index: dst_idx, width: dst_width, value }];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    // -------------------------------------------------------------------
    // FP conditional select: FCSEL
    // -------------------------------------------------------------------

    /// FCSEL: Fd = cond ? Fn : Fm.
    pub(super) fn sem_fcsel(
        &self,
        state: &MachineState,
        insn: &Instruction,
    ) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, width) = extract_fp_dst(insn)?;
        let fn_val = read_fp_operand(state, insn, 1, width)?;
        let fm_val = read_fp_operand(state, insn, 2, width)?;
        let cond = extract_condition(insn, 3)?;
        let cond_formula = condition_to_formula(state, cond);

        let result = Formula::Ite(Box::new(cond_formula), Box::new(fn_val), Box::new(fm_val));

        let mut effects = vec![Effect::FpRegWrite { index: dst_idx, width, value: result }];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }
}

// ---------------------------------------------------------------------------
// FP helper functions
// ---------------------------------------------------------------------------

/// Extract FP destination register index and width from operand 0.
fn extract_fp_dst(insn: &Instruction) -> Result<(u8, u32), SemError> {
    match insn.operand(0) {
        Some(Operand::Reg(r)) if r.kind == RegKind::Simd => Ok((r.index, u32::from(r.width))),
        _ => Err(SemError::InvalidOperand {
            opcode: insn.opcode,
            index: 0,
            detail: "expected SIMD/FP register destination".into(),
        }),
    }
}

/// Extract FP register index and width from a given operand position.
fn extract_fp_reg(insn: &Instruction, index: usize) -> Result<(u8, u32), SemError> {
    match insn.operand(index) {
        Some(Operand::Reg(r)) if r.kind == RegKind::Simd => Ok((r.index, u32::from(r.width))),
        _ => Err(SemError::InvalidOperand {
            opcode: insn.opcode,
            index,
            detail: "expected SIMD/FP register".into(),
        }),
    }
}

/// Read an FP operand (register) from the instruction at the given position.
fn read_fp_operand(
    state: &MachineState,
    insn: &Instruction,
    index: usize,
    width: u32,
) -> Result<Formula, SemError> {
    match insn.operand(index) {
        Some(Operand::Reg(r)) if r.kind == RegKind::Simd => Ok(state.read_fpr(r.index, width)),
        _ => Err(SemError::InvalidOperand {
            opcode: insn.opcode,
            index,
            detail: "expected SIMD/FP register operand".into(),
        }),
    }
}

/// Expand an 8-bit FP immediate to a full-width FP constant.
///
/// AArch64 FMOV immediate encoding: imm8 = abcdefgh
///   Single (32-bit): aBbb_bbbc_defg_h000_0000_0000_0000_0000 (where B = NOT b)
///   Double (64-bit): aBbb_bbbb_bbcd_efgh_0...0 (where B = NOT b)
fn expand_fp_imm8(imm8: u64, width: u32) -> Formula {
    let value = if width == 32 {
        let a = (imm8 >> 7) & 1;
        let b = (imm8 >> 6) & 1;
        let c = (imm8 >> 5) & 1;
        let d = (imm8 >> 4) & 1;
        let e = (imm8 >> 3) & 1;
        let f = (imm8 >> 2) & 1;
        let g = (imm8 >> 1) & 1;
        let h = imm8 & 1;

        let sign = a << 31;
        let exp_high = (!b & 1) << 30;
        let exp_mid = if b == 1 { 0x1F << 25 } else { 0 };
        let exp_low = c << 25;
        let mantissa = (d << 22) | (e << 21) | (f << 20) | (g << 19) | (h << 18);

        (sign | exp_high | exp_mid | exp_low | mantissa) as i128
    } else if width == 64 {
        let a = (imm8 >> 7) & 1;
        let b = (imm8 >> 6) & 1;
        let c = (imm8 >> 5) & 1;
        let d = (imm8 >> 4) & 1;
        let e = (imm8 >> 3) & 1;
        let f = (imm8 >> 2) & 1;
        let g = (imm8 >> 1) & 1;
        let h = imm8 & 1;

        let sign = a << 63;
        let exp_high = (!b & 1) << 62;
        let exp_mid = if b == 1 { 0xFFu64 << 54 } else { 0 };
        let exp_low = c << 54;
        let mantissa = (d << 51) | (e << 50) | (f << 49) | (g << 48) | (h << 47);

        (sign | exp_high | exp_mid | exp_low | mantissa) as i128
    } else {
        // For 16-bit half-precision, store raw imm8 as approximation.
        imm8 as i128
    };

    Formula::BitVec { value, width }
}
