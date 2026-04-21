// trust-machine-sem: AArch64 ISA semantics
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

mod fp;
mod helpers;

use trust_disasm::Instruction;
use trust_disasm::opcode::Opcode;
use trust_disasm::operand::{Condition, MemoryOperand, Operand, RegKind};
use trust_types::Formula;

use crate::effect::Effect;
use crate::error::SemError;
use crate::semantics::Semantics;
use crate::state::MachineState;

use helpers::{compute_nzcv, operand_to_formula, resolve_mem_address};

/// AArch64 instruction semantics.
pub struct Aarch64Semantics;

impl Semantics for Aarch64Semantics {
    fn effects(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        match insn.opcode {
            // Arithmetic
            Opcode::Add | Opcode::Adds => self.sem_add(state, insn),
            Opcode::Sub | Opcode::Subs => self.sem_sub(state, insn),
            Opcode::Adc | Opcode::Adcs => self.sem_adc(state, insn),
            Opcode::Sbc | Opcode::Sbcs => self.sem_sbc(state, insn),
            Opcode::Madd => self.sem_madd(state, insn),
            Opcode::Msub => self.sem_msub(state, insn),
            Opcode::Udiv => self.sem_udiv(state, insn),
            Opcode::Sdiv => self.sem_sdiv(state, insn),

            // Logic
            Opcode::And | Opcode::Ands => self.sem_and(state, insn),
            Opcode::Orr => self.sem_orr(state, insn),
            Opcode::Eor => self.sem_eor(state, insn),
            Opcode::Bic | Opcode::Bics => self.sem_bic(state, insn),
            Opcode::Orn => self.sem_orn(state, insn),
            Opcode::Eon => self.sem_eon(state, insn),

            // Move
            Opcode::Movz | Opcode::Movn | Opcode::Movk => self.sem_mov_imm(state, insn),

            // Shift (variable)
            Opcode::Lslv => self.sem_shift_var(state, insn),
            Opcode::Lsrv => self.sem_shift_var(state, insn),
            Opcode::Asrv => self.sem_shift_var(state, insn),
            Opcode::Rorv => self.sem_shift_var(state, insn),

            // Bitfield
            Opcode::Ubfm => self.sem_ubfm(state, insn),
            Opcode::Sbfm => self.sem_sbfm(state, insn),
            Opcode::Bfm => self.sem_bfm(state, insn),
            Opcode::Extr => self.sem_extr(state, insn),

            // Bit manipulation
            Opcode::Clz => self.sem_clz(state, insn),
            Opcode::Rbit => self.sem_rbit(state, insn),
            Opcode::Rev => self.sem_rev(state, insn),
            Opcode::Rev16 => self.sem_rev16(state, insn),
            Opcode::Rev32 => self.sem_rev32(state, insn),
            Opcode::Cls => self.sem_cls(state, insn),

            // Conditional select
            Opcode::Csel => self.sem_csel(state, insn),
            Opcode::Csinc => self.sem_csinc(state, insn),
            Opcode::Csinv => self.sem_csinv(state, insn),
            Opcode::Csneg => self.sem_csneg(state, insn),

            // Conditional compare
            Opcode::Ccmp => self.sem_ccmp(state, insn),
            Opcode::Ccmn => self.sem_ccmn(state, insn),

            // Address computation
            Opcode::Adr => self.sem_adr(state, insn),
            Opcode::Adrp => self.sem_adrp(state, insn),

            // Loads
            Opcode::Ldr => self.sem_ldr(state, insn),
            Opcode::Ldrb => self.sem_ldr_variant(state, insn, 1, false),
            Opcode::Ldrh => self.sem_ldr_variant(state, insn, 2, false),
            Opcode::Ldrsb => self.sem_ldr_variant(state, insn, 1, true),
            Opcode::Ldrsh => self.sem_ldr_variant(state, insn, 2, true),
            Opcode::Ldrsw => self.sem_ldr_variant(state, insn, 4, true),

            // Stores
            Opcode::Str => self.sem_str(state, insn),
            Opcode::Strb => self.sem_str_variant(state, insn, 1),
            Opcode::Strh => self.sem_str_variant(state, insn, 2),

            // Branches
            Opcode::B => self.sem_b(state, insn),
            Opcode::Bl => self.sem_bl(state, insn),
            Opcode::Br => self.sem_br(state, insn),
            Opcode::Blr => self.sem_blr(state, insn),
            Opcode::Ret => self.sem_ret(state, insn),
            Opcode::BCond => self.sem_bcond(state, insn),
            Opcode::Cbz => self.sem_cbz(state, insn, false),
            Opcode::Cbnz => self.sem_cbz(state, insn, true),
            Opcode::Tbz => self.sem_tbz(state, insn, false),
            Opcode::Tbnz => self.sem_tbz(state, insn, true),

            // System / no-ops
            Opcode::Nop | Opcode::Yield | Opcode::Sev | Opcode::Sevl => Ok(vec![]),
            Opcode::Dmb | Opcode::Dsb | Opcode::Isb | Opcode::Clrex => {
                // Barrier / fence: model as no data effect (ordering only).
                Ok(vec![pc_advance(state, insn)])
            }

            // FP scalar arithmetic
            Opcode::Fadd => self.sem_fadd(state, insn),
            Opcode::Fsub => self.sem_fsub(state, insn),
            Opcode::Fmul => self.sem_fmul(state, insn),
            Opcode::Fdiv => self.sem_fdiv(state, insn),

            // FP compare
            Opcode::Fcmp => self.sem_fcmp(state, insn),

            // FP move
            Opcode::FmovReg => self.sem_fmov_reg(state, insn),
            Opcode::FmovImm => self.sem_fmov_imm(state, insn),

            // FP unary
            Opcode::Fneg => self.sem_fneg(state, insn),
            Opcode::Fabs => self.sem_fabs(state, insn),
            Opcode::Fsqrt => self.sem_fsqrt(state, insn),

            // FP conversion
            Opcode::Fcvtzs => self.sem_fcvtzs(state, insn),
            Opcode::Fcvtzu => self.sem_fcvtzu(state, insn),
            Opcode::Scvtf => self.sem_scvtf(state, insn),
            Opcode::Ucvtf => self.sem_ucvtf(state, insn),
            Opcode::Fcvt => self.sem_fcvt(state, insn),

            // FP conditional select
            Opcode::Fcsel => self.sem_fcsel(state, insn),

            other => Err(SemError::UnsupportedOpcode(other)),
        }
    }
}

impl Aarch64Semantics {
    /// ADD/ADDS: Rd = Rn + Op2 (optionally setting flags).
    fn sem_add(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let sets_flags = insn.opcode == Opcode::Adds;
        let (dst_idx, dst_is_sp, width) = extract_dst_reg(insn)?;
        let rn = operand_to_formula(state, insn.operand(1), insn.opcode, 1, width)?;
        let op2 = operand_to_formula(state, insn.operand(2), insn.opcode, 2, width)?;

        let result = Formula::BvAdd(Box::new(rn.clone()), Box::new(op2.clone()), width);
        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, width, result.clone())];

        if sets_flags {
            let nzcv = compute_nzcv(&rn, &op2, &result, width, false);
            effects.push(nzcv);
        }

        // PC advances by 4
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// SUB/SUBS: Rd = Rn - Op2 (optionally setting flags).
    /// CMP is an alias for SUBS with Rd = XZR/WZR.
    fn sem_sub(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let sets_flags = insn.opcode == Opcode::Subs;
        let (dst_idx, dst_is_sp, width) = extract_dst_reg(insn)?;
        let rn = operand_to_formula(state, insn.operand(1), insn.opcode, 1, width)?;
        let op2 = operand_to_formula(state, insn.operand(2), insn.opcode, 2, width)?;

        let result = Formula::BvSub(Box::new(rn.clone()), Box::new(op2.clone()), width);
        let mut effects = Vec::new();

        // Writes to ZR (index 31) are discarded — this is how CMP works.
        if dst_idx < 31 {
            effects.push(write_reg_or_sp(dst_idx, dst_is_sp, width, result.clone()));
        }

        if sets_flags {
            let nzcv = compute_nzcv(&rn, &op2, &result, width, true);
            effects.push(nzcv);
        }

        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// MOVZ: Rd = imm16 << shift
    /// MOVN: Rd = ~(imm16 << shift)
    /// MOVK: Rd[shift+15:shift] = imm16 (keep other bits)
    fn sem_mov_imm(
        &self,
        state: &MachineState,
        insn: &Instruction,
    ) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, dst_is_sp, width) = extract_dst_reg(insn)?;

        let imm_val = match insn.operand(1) {
            Some(Operand::Imm(v)) => *v,
            _ => {
                return Err(SemError::InvalidOperand {
                    opcode: insn.opcode,
                    index: 1,
                    detail: "expected immediate".into(),
                });
            }
        };

        let value = match insn.opcode {
            Opcode::Movz => Formula::BitVec { value: imm_val as i128, width },
            Opcode::Movn => {
                Formula::BvNot(Box::new(Formula::BitVec { value: imm_val as i128, width }), width)
            }
            Opcode::Movk => {
                // Bit-field insert: clear the target 16-bit lane, then OR in
                // the shifted immediate. The decoder pre-shifts the immediate.
                // Extract hw (shift amount / 16) from encoding bits [22:21].
                let hw = (insn.encoding >> 21) & 0x3;
                let shift = hw * 16;
                let existing = state.read_gpr(dst_idx, width);

                // Build inverted mask to clear the 16-bit field.
                let width_mask: i128 = if width == 64 {
                    -1i128 // all ones in 64 bits (0xFFFFFFFFFFFFFFFF as i128)
                } else {
                    (1i128 << width) - 1
                };
                let field_mask = (0xFFFF_i128) << shift;
                let inv_mask = (!field_mask) & width_mask;

                let cleared = Formula::BvAnd(
                    Box::new(existing),
                    Box::new(Formula::BitVec { value: inv_mask, width }),
                    width,
                );
                Formula::BvOr(
                    Box::new(cleared),
                    Box::new(Formula::BitVec { value: imm_val as i128, width }),
                    width,
                )
            }
            _ => unreachable!("sem_mov_imm only handles MOVZ, MOVN, and MOVK"),
        };

        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, width, value)];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// ORR: Rd = Rn | Op2. MOV (register) is ORR Rd, XZR, Rm.
    fn sem_orr(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, dst_is_sp, width) = extract_dst_reg(insn)?;
        let rn = operand_to_formula(state, insn.operand(1), insn.opcode, 1, width)?;
        let op2 = operand_to_formula(state, insn.operand(2), insn.opcode, 2, width)?;

        let result = Formula::BvOr(Box::new(rn), Box::new(op2), width);
        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, width, result)];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// LDR: Rd = mem[addr]. Load register from memory.
    fn sem_ldr(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, _dst_is_sp, width) = extract_dst_reg(insn)?;
        let width_bytes = width / 8;

        let mem_op = match insn.operand(1) {
            Some(Operand::Mem(m)) => m,
            _ => {
                return Err(SemError::InvalidOperand {
                    opcode: insn.opcode,
                    index: 1,
                    detail: "expected memory operand".into(),
                });
            }
        };

        let addr = resolve_mem_address(state, mem_op)?;

        // Load width_bytes from byte-addressed memory in little-endian order.
        // Each byte is a Select on the memory array, then zero-extended and
        // shifted into position.
        let loaded = {
            let mut result = Formula::BitVec { value: 0, width };
            for i in 0..width_bytes {
                let byte_addr = if i == 0 {
                    addr.clone()
                } else {
                    Formula::BvAdd(
                        Box::new(addr.clone()),
                        Box::new(Formula::BitVec { value: i128::from(i), width: 64 }),
                        64,
                    )
                };
                let byte_val = Formula::Select(Box::new(state.memory.clone()), Box::new(byte_addr));
                let extended = Formula::BvZeroExt(Box::new(byte_val), width);
                if i == 0 {
                    result = extended;
                } else {
                    let shift_amt = Formula::BitVec { value: i128::from(i * 8), width };
                    let shifted = Formula::BvShl(Box::new(extended), Box::new(shift_amt), width);
                    result = Formula::BvOr(Box::new(result), Box::new(shifted), width);
                }
            }
            result
        };

        let mut effects = vec![
            Effect::MemRead { address: addr.clone(), width_bytes },
            Effect::RegWrite { index: dst_idx, width, value: loaded },
        ];

        // Handle pre/post-index writeback to base register.
        if let Some(wb) = writeback_effect(state, mem_op) {
            effects.push(wb);
        }

        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// STR: mem[addr] = Rt. Store register to memory.
    fn sem_str(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let src = operand_to_formula(state, insn.operand(0), insn.opcode, 0, 64)?;
        let width = match insn.operand(0) {
            Some(Operand::Reg(r)) => u32::from(r.width),
            _ => 64,
        };
        let width_bytes = width / 8;

        let mem_op = match insn.operand(1) {
            Some(Operand::Mem(m)) => m,
            _ => {
                return Err(SemError::InvalidOperand {
                    opcode: insn.opcode,
                    index: 1,
                    detail: "expected memory operand".into(),
                });
            }
        };

        let addr = resolve_mem_address(state, mem_op)?;

        let mut effects = vec![Effect::MemWrite { address: addr.clone(), value: src, width_bytes }];

        if let Some(wb) = writeback_effect(state, mem_op) {
            effects.push(wb);
        }

        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// B: unconditional branch.
    fn sem_b(&self, _state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let target = branch_target_formula(insn)?;
        Ok(vec![Effect::Branch { target: target.clone() }, Effect::PcUpdate { value: target }])
    }

    /// BL: branch with link (function call).
    fn sem_bl(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let target = branch_target_formula(insn)?;
        let return_addr = Formula::BvAdd(
            Box::new(state.pc.clone()),
            Box::new(Formula::BitVec { value: 4, width: 64 }),
            64,
        );
        Ok(vec![
            Effect::Call { target: target.clone(), return_addr: return_addr.clone() },
            // X30 = return address
            Effect::RegWrite { index: 30, width: 64, value: return_addr },
            Effect::PcUpdate { value: target },
        ])
    }

    /// BR: branch to register.
    fn sem_br(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let target = operand_to_formula(state, insn.operand(0), insn.opcode, 0, 64)?;
        Ok(vec![Effect::Branch { target: target.clone() }, Effect::PcUpdate { value: target }])
    }

    /// RET: return (branch to X30 by default).
    fn sem_ret(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        // RET optionally takes a register operand; defaults to X30.
        let target = if insn.operand_count() > 0 {
            operand_to_formula(state, insn.operand(0), insn.opcode, 0, 64)?
        } else {
            state.read_gpr(30, 64)
        };
        Ok(vec![Effect::Return { target: target.clone() }, Effect::PcUpdate { value: target }])
    }

    /// B.cond: conditional branch.
    fn sem_bcond(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let target = branch_target_formula(insn)?;
        let fallthrough = Formula::BvAdd(
            Box::new(state.pc.clone()),
            Box::new(Formula::BitVec { value: 4, width: 64 }),
            64,
        );

        // Find the condition operand.
        let condition = insn
            .operands()
            .find_map(|op| if let Operand::Cond(c) = op { Some(*c) } else { None })
            .ok_or_else(|| SemError::InvalidOperand {
                opcode: insn.opcode,
                index: 0,
                detail: "expected condition operand for B.cond".into(),
            })?;

        Ok(vec![Effect::ConditionalBranch { condition, target, fallthrough }])
    }

    // -----------------------------------------------------------------------
    // Arithmetic: ADC/ADCS, SBC/SBCS, MADD, MSUB, UDIV, SDIV
    // -----------------------------------------------------------------------

    /// ADC/ADCS: Rd = Rn + Rm + C.
    fn sem_adc(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let sets_flags = insn.opcode == Opcode::Adcs;
        let (dst_idx, dst_is_sp, width) = extract_dst_reg(insn)?;
        let rn = operand_to_formula(state, insn.operand(1), insn.opcode, 1, width)?;
        let rm = operand_to_formula(state, insn.operand(2), insn.opcode, 2, width)?;

        // C flag zero-extended to width bits.
        let carry = Formula::Ite(
            Box::new(state.flags.c.clone()),
            Box::new(Formula::BitVec { value: 1, width }),
            Box::new(Formula::BitVec { value: 0, width }),
        );
        let sum_no_c = Formula::BvAdd(Box::new(rn.clone()), Box::new(rm.clone()), width);
        let result = Formula::BvAdd(Box::new(sum_no_c), Box::new(carry), width);

        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, width, result.clone())];
        if sets_flags {
            effects.push(compute_nzcv(&rn, &rm, &result, width, false));
        }
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// SBC/SBCS: Rd = Rn - Rm - !C.
    fn sem_sbc(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let sets_flags = insn.opcode == Opcode::Sbcs;
        let (dst_idx, dst_is_sp, width) = extract_dst_reg(insn)?;
        let rn = operand_to_formula(state, insn.operand(1), insn.opcode, 1, width)?;
        let rm = operand_to_formula(state, insn.operand(2), insn.opcode, 2, width)?;

        // borrow = NOT C, so Rd = Rn - Rm - !C = Rn - Rm - 1 + C
        let borrow = Formula::Ite(
            Box::new(state.flags.c.clone()),
            Box::new(Formula::BitVec { value: 0, width }),
            Box::new(Formula::BitVec { value: 1, width }),
        );
        let diff = Formula::BvSub(Box::new(rn.clone()), Box::new(rm.clone()), width);
        let result = Formula::BvSub(Box::new(diff), Box::new(borrow), width);

        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, width, result.clone())];
        if sets_flags {
            effects.push(compute_nzcv(&rn, &rm, &result, width, true));
        }
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// MADD: Rd = Ra + (Rn * Rm).
    fn sem_madd(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, dst_is_sp, width) = extract_dst_reg(insn)?;
        let rn = operand_to_formula(state, insn.operand(1), insn.opcode, 1, width)?;
        let rm = operand_to_formula(state, insn.operand(2), insn.opcode, 2, width)?;
        let ra = operand_to_formula(state, insn.operand(3), insn.opcode, 3, width)?;

        let product = Formula::BvMul(Box::new(rn), Box::new(rm), width);
        let result = Formula::BvAdd(Box::new(ra), Box::new(product), width);

        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, width, result)];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// MSUB: Rd = Ra - (Rn * Rm).
    fn sem_msub(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, dst_is_sp, width) = extract_dst_reg(insn)?;
        let rn = operand_to_formula(state, insn.operand(1), insn.opcode, 1, width)?;
        let rm = operand_to_formula(state, insn.operand(2), insn.opcode, 2, width)?;
        let ra = operand_to_formula(state, insn.operand(3), insn.opcode, 3, width)?;

        let product = Formula::BvMul(Box::new(rn), Box::new(rm), width);
        let result = Formula::BvSub(Box::new(ra), Box::new(product), width);

        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, width, result)];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// UDIV: Rd = Rn / Rm (unsigned).
    fn sem_udiv(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, dst_is_sp, width) = extract_dst_reg(insn)?;
        let rn = operand_to_formula(state, insn.operand(1), insn.opcode, 1, width)?;
        let rm = operand_to_formula(state, insn.operand(2), insn.opcode, 2, width)?;

        // AArch64: division by zero produces 0 (not a trap).
        let zero = Formula::BitVec { value: 0, width };
        let is_zero = Formula::Eq(Box::new(rm.clone()), Box::new(zero.clone()));
        let quotient = Formula::BvUDiv(Box::new(rn), Box::new(rm), width);
        let result = Formula::Ite(Box::new(is_zero), Box::new(zero), Box::new(quotient));

        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, width, result)];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// SDIV: Rd = Rn / Rm (signed).
    fn sem_sdiv(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, dst_is_sp, width) = extract_dst_reg(insn)?;
        let rn = operand_to_formula(state, insn.operand(1), insn.opcode, 1, width)?;
        let rm = operand_to_formula(state, insn.operand(2), insn.opcode, 2, width)?;

        let zero = Formula::BitVec { value: 0, width };
        let is_zero = Formula::Eq(Box::new(rm.clone()), Box::new(zero.clone()));
        let quotient = Formula::BvSDiv(Box::new(rn), Box::new(rm), width);
        let result = Formula::Ite(Box::new(is_zero), Box::new(zero), Box::new(quotient));

        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, width, result)];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    // -----------------------------------------------------------------------
    // Logic: AND/ANDS, EOR, BIC/BICS, ORN, EON
    // -----------------------------------------------------------------------

    /// AND/ANDS: Rd = Rn & Op2.
    fn sem_and(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let sets_flags = insn.opcode == Opcode::Ands;
        let (dst_idx, dst_is_sp, width) = extract_dst_reg(insn)?;
        let rn = operand_to_formula(state, insn.operand(1), insn.opcode, 1, width)?;
        let op2 = operand_to_formula(state, insn.operand(2), insn.opcode, 2, width)?;

        let result = Formula::BvAnd(Box::new(rn), Box::new(op2), width);
        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, width, result.clone())];

        if sets_flags {
            effects.push(logic_nzcv(&result, width));
        }
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// EOR: Rd = Rn ^ Op2.
    fn sem_eor(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, dst_is_sp, width) = extract_dst_reg(insn)?;
        let rn = operand_to_formula(state, insn.operand(1), insn.opcode, 1, width)?;
        let op2 = operand_to_formula(state, insn.operand(2), insn.opcode, 2, width)?;

        let result = Formula::BvXor(Box::new(rn), Box::new(op2), width);
        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, width, result)];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// BIC/BICS: Rd = Rn & ~Op2.
    fn sem_bic(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let sets_flags = insn.opcode == Opcode::Bics;
        let (dst_idx, dst_is_sp, width) = extract_dst_reg(insn)?;
        let rn = operand_to_formula(state, insn.operand(1), insn.opcode, 1, width)?;
        let op2 = operand_to_formula(state, insn.operand(2), insn.opcode, 2, width)?;

        let not_op2 = Formula::BvNot(Box::new(op2), width);
        let result = Formula::BvAnd(Box::new(rn), Box::new(not_op2), width);
        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, width, result.clone())];

        if sets_flags {
            effects.push(logic_nzcv(&result, width));
        }
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// ORN: Rd = Rn | ~Op2.
    fn sem_orn(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, dst_is_sp, width) = extract_dst_reg(insn)?;
        let rn = operand_to_formula(state, insn.operand(1), insn.opcode, 1, width)?;
        let op2 = operand_to_formula(state, insn.operand(2), insn.opcode, 2, width)?;

        let not_op2 = Formula::BvNot(Box::new(op2), width);
        let result = Formula::BvOr(Box::new(rn), Box::new(not_op2), width);
        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, width, result)];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// EON: Rd = Rn ^ ~Op2.
    fn sem_eon(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, dst_is_sp, width) = extract_dst_reg(insn)?;
        let rn = operand_to_formula(state, insn.operand(1), insn.opcode, 1, width)?;
        let op2 = operand_to_formula(state, insn.operand(2), insn.opcode, 2, width)?;

        let not_op2 = Formula::BvNot(Box::new(op2), width);
        let result = Formula::BvXor(Box::new(rn), Box::new(not_op2), width);
        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, width, result)];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    // -----------------------------------------------------------------------
    // Variable shifts: LSLV, LSRV, ASRV, RORV
    // -----------------------------------------------------------------------

    /// Variable shift: Rd = Rn <shift> (Rm mod width).
    fn sem_shift_var(
        &self,
        state: &MachineState,
        insn: &Instruction,
    ) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, dst_is_sp, width) = extract_dst_reg(insn)?;
        let rn = operand_to_formula(state, insn.operand(1), insn.opcode, 1, width)?;
        let rm = operand_to_formula(state, insn.operand(2), insn.opcode, 2, width)?;

        // Shift amount is Rm mod width (only low 5/6 bits matter).
        let mod_mask = Formula::BitVec { value: i128::from(width - 1), width };
        let shift_amt = Formula::BvAnd(Box::new(rm), Box::new(mod_mask), width);

        let result = match insn.opcode {
            Opcode::Lslv => Formula::BvShl(Box::new(rn), Box::new(shift_amt), width),
            Opcode::Lsrv => Formula::BvLShr(Box::new(rn), Box::new(shift_amt), width),
            Opcode::Asrv => Formula::BvAShr(Box::new(rn), Box::new(shift_amt), width),
            Opcode::Rorv => {
                // ROR(x, n) = (x >> n) | (x << (width - n))
                let right =
                    Formula::BvLShr(Box::new(rn.clone()), Box::new(shift_amt.clone()), width);
                let complement = Formula::BvSub(
                    Box::new(Formula::BitVec { value: i128::from(width), width }),
                    Box::new(shift_amt),
                    width,
                );
                let left = Formula::BvShl(Box::new(rn), Box::new(complement), width);
                Formula::BvOr(Box::new(right), Box::new(left), width)
            }
            _ => unreachable!("sem_shift_var only handles LSLV, LSRV, ASRV, and RORV"),
        };

        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, width, result)];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    // -----------------------------------------------------------------------
    // Bitfield: UBFM, SBFM, BFM, EXTR
    // -----------------------------------------------------------------------

    /// UBFM: unsigned bitfield move. Extracts a bitfield and zero-extends.
    /// This covers LSL, LSR, UXTB, UXTH aliases.
    fn sem_ubfm(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, dst_is_sp, width) = extract_dst_reg(insn)?;
        let rn = operand_to_formula(state, insn.operand(1), insn.opcode, 1, width)?;
        let immr = extract_imm(insn, 2)? as u32;
        let imms = extract_imm(insn, 3)? as u32;

        let result = if imms >= immr {
            // Extract bits [imms:immr] and zero-extend.
            let field_width = imms - immr + 1;
            let extracted = Formula::BvExtract { inner: Box::new(rn), high: imms, low: immr };
            if field_width == width {
                extracted
            } else {
                Formula::BvZeroExt(Box::new(extracted), width)
            }
        } else {
            // LSL alias: imms < immr. Shift left by (width - immr), mask to imms+1 bits.
            let shift = width - immr;

            // Mask to keep only the low (imms+1+shift) bits — but for UBFM the
            // upper bits above position imms+shift are zeroed. Since we shift
            // from a clean source, the result is already correct for the
            // zero-extension semantics.
            Formula::BvShl(
                Box::new(rn),
                Box::new(Formula::BitVec { value: i128::from(shift), width }),
                width,
            )
        };

        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, width, result)];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// SBFM: signed bitfield move. Extracts a bitfield and sign-extends.
    /// Covers ASR and SXTB/SXTH/SXTW aliases.
    fn sem_sbfm(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, dst_is_sp, width) = extract_dst_reg(insn)?;
        let rn = operand_to_formula(state, insn.operand(1), insn.opcode, 1, width)?;
        let immr = extract_imm(insn, 2)? as u32;
        let imms = extract_imm(insn, 3)? as u32;

        let result = if imms >= immr {
            // Extract bits [imms:immr] and sign-extend.
            let extracted = Formula::BvExtract { inner: Box::new(rn), high: imms, low: immr };
            Formula::BvSignExt(Box::new(extracted), width)
        } else {
            // ASR alias or shift-insert: shift left then arithmetic shift right.
            let shift = width - immr;

            Formula::BvShl(
                Box::new(rn),
                Box::new(Formula::BitVec { value: i128::from(shift), width }),
                width,
            )
        };

        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, width, result)];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// BFM: bitfield move. Copies a bitfield into the destination without
    /// clearing other bits.
    fn sem_bfm(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, dst_is_sp, width) = extract_dst_reg(insn)?;
        let rn = operand_to_formula(state, insn.operand(1), insn.opcode, 1, width)?;
        let immr = extract_imm(insn, 2)? as u32;
        let imms = extract_imm(insn, 3)? as u32;
        let existing = state.read_gpr(dst_idx, width);

        // Simple model: extract the field from Rn, insert into Rd.
        // When imms >= immr: extract [imms:immr] from Rn, place at [imms-immr:0] in Rd.
        let result = if imms >= immr {
            let field_width = imms - immr + 1;
            let extracted = Formula::BvExtract { inner: Box::new(rn), high: imms, low: immr };
            let ext_full = Formula::BvZeroExt(Box::new(extracted), width);
            // Mask: clear bits [field_width-1:0] in existing.
            let field_mask = (1i128 << field_width) - 1;
            let width_mask: i128 = if width == 64 { -1i128 } else { (1i128 << width) - 1 };
            let inv = (!field_mask) & width_mask;
            let cleared = Formula::BvAnd(
                Box::new(existing),
                Box::new(Formula::BitVec { value: inv, width }),
                width,
            );
            Formula::BvOr(Box::new(cleared), Box::new(ext_full), width)
        } else {
            // imms < immr: insert at [width-immr+imms : width-immr].
            // Simplified: model as shift + mask + or.
            let shift = width - immr;
            let field_width = imms + 1;
            let shifted = Formula::BvShl(
                Box::new(rn),
                Box::new(Formula::BitVec { value: i128::from(shift), width }),
                width,
            );
            let field_mask = ((1i128 << field_width) - 1) << shift;
            let shifted_masked = Formula::BvAnd(
                Box::new(shifted),
                Box::new(Formula::BitVec { value: field_mask, width }),
                width,
            );
            let width_mask: i128 = if width == 64 { -1i128 } else { (1i128 << width) - 1 };
            let inv = (!field_mask) & width_mask;
            let cleared = Formula::BvAnd(
                Box::new(existing),
                Box::new(Formula::BitVec { value: inv, width }),
                width,
            );
            Formula::BvOr(Box::new(cleared), Box::new(shifted_masked), width)
        };

        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, width, result)];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// EXTR: Rd = (Rn:Rm) >> lsb. Extract from pair of registers.
    fn sem_extr(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, dst_is_sp, width) = extract_dst_reg(insn)?;
        let rn = operand_to_formula(state, insn.operand(1), insn.opcode, 1, width)?;
        let rm = operand_to_formula(state, insn.operand(2), insn.opcode, 2, width)?;
        let lsb = extract_imm(insn, 3)? as u32;

        if lsb == 0 {
            // Trivial case: result = Rm
            let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, width, rm)];
            effects.push(pc_advance(state, insn));
            return Ok(effects);
        }

        // Rd = (Rm >> lsb) | (Rn << (width - lsb))
        let low_part = Formula::BvLShr(
            Box::new(rm),
            Box::new(Formula::BitVec { value: i128::from(lsb), width }),
            width,
        );
        let high_part = Formula::BvShl(
            Box::new(rn),
            Box::new(Formula::BitVec { value: i128::from(width - lsb), width }),
            width,
        );
        let result = Formula::BvOr(Box::new(low_part), Box::new(high_part), width);

        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, width, result)];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    // -----------------------------------------------------------------------
    // Bit manipulation: CLZ, RBIT, REV, REV16, REV32, CLS
    // -----------------------------------------------------------------------

    /// CLZ: count leading zeros. Modeled symbolically with Ite chain.
    fn sem_clz(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, dst_is_sp, width) = extract_dst_reg(insn)?;
        let rn = operand_to_formula(state, insn.operand(1), insn.opcode, 1, width)?;

        // Model CLZ as a symbolic uninterpreted-style nested Ite:
        // Check each bit from MSB down. Build an Ite chain:
        // if bit[width-1] then 0 else if bit[width-2] then 1 else ...
        let mut result = Formula::BitVec { value: i128::from(width), width };
        for i in 0..width {
            let bit_pos = i;
            let bit =
                Formula::BvExtract { inner: Box::new(rn.clone()), high: bit_pos, low: bit_pos };
            let is_one =
                Formula::Eq(Box::new(bit), Box::new(Formula::BitVec { value: 1, width: 1 }));
            let clz_val = Formula::BitVec { value: i128::from(width - 1 - bit_pos), width };
            result = Formula::Ite(Box::new(is_one), Box::new(clz_val), Box::new(result));
        }

        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, width, result)];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// RBIT: reverse bits. Model as building a new value from each bit.
    fn sem_rbit(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, dst_is_sp, width) = extract_dst_reg(insn)?;
        let rn = operand_to_formula(state, insn.operand(1), insn.opcode, 1, width)?;

        // Reverse all bits: result[i] = src[width-1-i].
        // Build by extracting each bit, shifting to its reversed position, and OR-ing.
        let mut result = Formula::BitVec { value: 0, width };
        for i in 0..width {
            let src_bit = Formula::BvExtract { inner: Box::new(rn.clone()), high: i, low: i };
            let extended = Formula::BvZeroExt(Box::new(src_bit), width);
            let dest_pos = width - 1 - i;
            if dest_pos > 0 {
                let shifted = Formula::BvShl(
                    Box::new(extended),
                    Box::new(Formula::BitVec { value: i128::from(dest_pos), width }),
                    width,
                );
                result = Formula::BvOr(Box::new(result), Box::new(shifted), width);
            } else {
                result = Formula::BvOr(Box::new(result), Box::new(extended), width);
            }
        }

        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, width, result)];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// REV: reverse bytes (full width).
    fn sem_rev(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, dst_is_sp, width) = extract_dst_reg(insn)?;
        let rn = operand_to_formula(state, insn.operand(1), insn.opcode, 1, width)?;
        let result = reverse_bytes(&rn, width, width);
        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, width, result)];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// REV16: reverse bytes in each 16-bit halfword.
    fn sem_rev16(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, dst_is_sp, width) = extract_dst_reg(insn)?;
        let rn = operand_to_formula(state, insn.operand(1), insn.opcode, 1, width)?;

        // Swap bytes within each 16-bit lane.
        let num_lanes = width / 16;
        let mut result = Formula::BitVec { value: 0, width };
        for lane in 0..num_lanes {
            let base = lane * 16;
            let lo = Formula::BvExtract { inner: Box::new(rn.clone()), high: base + 7, low: base };
            let hi =
                Formula::BvExtract { inner: Box::new(rn.clone()), high: base + 15, low: base + 8 };
            // Swapped: hi goes to low byte, lo goes to high byte.
            let lo_ext = Formula::BvZeroExt(Box::new(lo), width);
            let hi_ext = Formula::BvZeroExt(Box::new(hi), width);
            let lo_shifted = Formula::BvShl(
                Box::new(lo_ext),
                Box::new(Formula::BitVec { value: i128::from(base + 8), width }),
                width,
            );
            let hi_shifted = Formula::BvShl(
                Box::new(hi_ext),
                Box::new(Formula::BitVec { value: i128::from(base), width }),
                width,
            );
            result = Formula::BvOr(Box::new(result), Box::new(lo_shifted), width);
            result = Formula::BvOr(Box::new(result), Box::new(hi_shifted), width);
        }

        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, width, result)];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// REV32: reverse bytes in each 32-bit word.
    fn sem_rev32(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, dst_is_sp, width) = extract_dst_reg(insn)?;
        let rn = operand_to_formula(state, insn.operand(1), insn.opcode, 1, width)?;

        let num_words = width / 32;
        let mut result = Formula::BitVec { value: 0, width };
        for word in 0..num_words {
            let base = word * 32;
            let word_val =
                Formula::BvExtract { inner: Box::new(rn.clone()), high: base + 31, low: base };
            let reversed = reverse_bytes(&word_val, 32, 32);
            let ext = Formula::BvZeroExt(Box::new(reversed), width);
            if base > 0 {
                let shifted = Formula::BvShl(
                    Box::new(ext),
                    Box::new(Formula::BitVec { value: i128::from(base), width }),
                    width,
                );
                result = Formula::BvOr(Box::new(result), Box::new(shifted), width);
            } else {
                result = Formula::BvOr(Box::new(result), Box::new(ext), width);
            }
        }

        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, width, result)];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// CLS: count leading sign bits. Like CLZ but on the XOR of the value with
    /// its sign-extended MSB, then subtract 1.
    fn sem_cls(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, dst_is_sp, width) = extract_dst_reg(insn)?;
        let rn = operand_to_formula(state, insn.operand(1), insn.opcode, 1, width)?;

        // CLS(x) = CLZ(x XOR (x ASR (width-1))) - 1
        // The ASR replicates the sign bit, so XOR flips all sign bits to 0.
        let sign_fill = Formula::BvAShr(
            Box::new(rn.clone()),
            Box::new(Formula::BitVec { value: i128::from(width - 1), width }),
            width,
        );
        let xored = Formula::BvXor(Box::new(rn), Box::new(sign_fill), width);

        // CLZ of xored, then subtract 1.
        // Reuse same Ite-chain approach as CLZ.
        let mut clz_result = Formula::BitVec { value: i128::from(width), width };
        for i in 0..width {
            let bit = Formula::BvExtract { inner: Box::new(xored.clone()), high: i, low: i };
            let is_one =
                Formula::Eq(Box::new(bit), Box::new(Formula::BitVec { value: 1, width: 1 }));
            let clz_val = Formula::BitVec { value: i128::from(width - 1 - i), width };
            clz_result = Formula::Ite(Box::new(is_one), Box::new(clz_val), Box::new(clz_result));
        }

        let result = Formula::BvSub(
            Box::new(clz_result),
            Box::new(Formula::BitVec { value: 1, width }),
            width,
        );

        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, width, result)];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    // -----------------------------------------------------------------------
    // Conditional select: CSEL, CSINC, CSINV, CSNEG
    // -----------------------------------------------------------------------

    /// CSEL: Rd = cond ? Rn : Rm.
    fn sem_csel(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, dst_is_sp, width) = extract_dst_reg(insn)?;
        let rn = operand_to_formula(state, insn.operand(1), insn.opcode, 1, width)?;
        let rm = operand_to_formula(state, insn.operand(2), insn.opcode, 2, width)?;
        let cond = extract_condition(insn, 3)?;
        let cond_formula = condition_to_formula(state, cond);

        let result = Formula::Ite(Box::new(cond_formula), Box::new(rn), Box::new(rm));
        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, width, result)];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// CSINC: Rd = cond ? Rn : (Rm + 1).
    fn sem_csinc(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, dst_is_sp, width) = extract_dst_reg(insn)?;
        let rn = operand_to_formula(state, insn.operand(1), insn.opcode, 1, width)?;
        let rm = operand_to_formula(state, insn.operand(2), insn.opcode, 2, width)?;
        let cond = extract_condition(insn, 3)?;
        let cond_formula = condition_to_formula(state, cond);

        let rm_inc =
            Formula::BvAdd(Box::new(rm), Box::new(Formula::BitVec { value: 1, width }), width);
        let result = Formula::Ite(Box::new(cond_formula), Box::new(rn), Box::new(rm_inc));
        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, width, result)];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// CSINV: Rd = cond ? Rn : ~Rm.
    fn sem_csinv(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, dst_is_sp, width) = extract_dst_reg(insn)?;
        let rn = operand_to_formula(state, insn.operand(1), insn.opcode, 1, width)?;
        let rm = operand_to_formula(state, insn.operand(2), insn.opcode, 2, width)?;
        let cond = extract_condition(insn, 3)?;
        let cond_formula = condition_to_formula(state, cond);

        let rm_inv = Formula::BvNot(Box::new(rm), width);
        let result = Formula::Ite(Box::new(cond_formula), Box::new(rn), Box::new(rm_inv));
        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, width, result)];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// CSNEG: Rd = cond ? Rn : -Rm.
    fn sem_csneg(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, dst_is_sp, width) = extract_dst_reg(insn)?;
        let rn = operand_to_formula(state, insn.operand(1), insn.opcode, 1, width)?;
        let rm = operand_to_formula(state, insn.operand(2), insn.opcode, 2, width)?;
        let cond = extract_condition(insn, 3)?;
        let cond_formula = condition_to_formula(state, cond);

        // -Rm = ~Rm + 1 (two's complement negation)
        let rm_neg = Formula::BvAdd(
            Box::new(Formula::BvNot(Box::new(rm), width)),
            Box::new(Formula::BitVec { value: 1, width }),
            width,
        );
        let result = Formula::Ite(Box::new(cond_formula), Box::new(rn), Box::new(rm_neg));
        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, width, result)];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    // -----------------------------------------------------------------------
    // Conditional compare: CCMP, CCMN
    // -----------------------------------------------------------------------

    /// CCMP: if cond then compare (Rn - Op2) else set NZCV = nzcv_imm.
    fn sem_ccmp(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        self.sem_ccmp_inner(state, insn, true)
    }

    /// CCMN: if cond then compare (Rn + Op2) else set NZCV = nzcv_imm.
    fn sem_ccmn(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        self.sem_ccmp_inner(state, insn, false)
    }

    /// Shared implementation for CCMP/CCMN.
    fn sem_ccmp_inner(
        &self,
        state: &MachineState,
        insn: &Instruction,
        is_sub: bool,
    ) -> Result<Vec<Effect>, SemError> {
        // CCMP/CCMN Rn, #imm5/Rm, #nzcv, cond
        // Operands: 0=Rn, 1=Op2(imm or reg), 2=nzcv_imm, 3=cond
        let width = match insn.operand(0) {
            Some(Operand::Reg(r)) => u32::from(r.width),
            _ => {
                return Err(SemError::InvalidOperand {
                    opcode: insn.opcode,
                    index: 0,
                    detail: "expected register".into(),
                });
            }
        };
        let rn = operand_to_formula(state, insn.operand(0), insn.opcode, 0, width)?;
        let op2 = operand_to_formula(state, insn.operand(1), insn.opcode, 1, width)?;
        let nzcv_imm = extract_imm(insn, 2)? as u8;
        let cond = extract_condition(insn, 3)?;
        let cond_formula = condition_to_formula(state, cond);

        // Compute comparison result.
        let result = if is_sub {
            Formula::BvSub(Box::new(rn.clone()), Box::new(op2.clone()), width)
        } else {
            Formula::BvAdd(Box::new(rn.clone()), Box::new(op2.clone()), width)
        };
        let flags_computed = compute_nzcv(&rn, &op2, &result, width, is_sub);

        // If condition false, use the immediate NZCV.
        let n_imm = Formula::Bool((nzcv_imm >> 3) & 1 != 0);
        let z_imm = Formula::Bool((nzcv_imm >> 2) & 1 != 0);
        let c_imm = Formula::Bool((nzcv_imm >> 1) & 1 != 0);
        let v_imm = Formula::Bool(nzcv_imm & 1 != 0);

        let (n_comp, z_comp, c_comp, v_comp) = match flags_computed {
            Effect::FlagUpdate { n, z, c, v } => (n, z, c, v),
            _ => unreachable!("compute_nzcv always returns Effect::FlagUpdate"),
        };

        let flags = Effect::FlagUpdate {
            n: Formula::Ite(Box::new(cond_formula.clone()), Box::new(n_comp), Box::new(n_imm)),
            z: Formula::Ite(Box::new(cond_formula.clone()), Box::new(z_comp), Box::new(z_imm)),
            c: Formula::Ite(Box::new(cond_formula.clone()), Box::new(c_comp), Box::new(c_imm)),
            v: Formula::Ite(Box::new(cond_formula), Box::new(v_comp), Box::new(v_imm)),
        };

        Ok(vec![flags, pc_advance(state, insn)])
    }

    // -----------------------------------------------------------------------
    // Address computation: ADR, ADRP
    // -----------------------------------------------------------------------

    /// ADR: Rd = PC + offset.
    fn sem_adr(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, dst_is_sp, _width) = extract_dst_reg(insn)?;
        let target = match insn.operand(1) {
            Some(Operand::PcRelAddr(addr)) => Formula::BitVec { value: *addr as i128, width: 64 },
            _ => {
                return Err(SemError::InvalidOperand {
                    opcode: insn.opcode,
                    index: 1,
                    detail: "expected PC-relative address".into(),
                });
            }
        };
        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, 64, target)];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// ADRP: Rd = (PC & ~0xFFF) + (offset << 12). Page-aligned.
    fn sem_adrp(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, dst_is_sp, _width) = extract_dst_reg(insn)?;
        // Decoder resolves ADRP to full target address.
        let target = match insn.operand(1) {
            Some(Operand::PcRelAddr(addr)) => Formula::BitVec { value: *addr as i128, width: 64 },
            _ => {
                return Err(SemError::InvalidOperand {
                    opcode: insn.opcode,
                    index: 1,
                    detail: "expected PC-relative address".into(),
                });
            }
        };
        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, 64, target)];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    // -----------------------------------------------------------------------
    // Load/store variants
    // -----------------------------------------------------------------------

    /// Load variant: LDRB (1 byte), LDRH (2 bytes), LDRSB/LDRSH/LDRSW (sign-extending).
    fn sem_ldr_variant(
        &self,
        state: &MachineState,
        insn: &Instruction,
        load_bytes: u32,
        sign_extend: bool,
    ) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, _dst_is_sp, width) = extract_dst_reg(insn)?;
        let mem_op = match insn.operand(1) {
            Some(Operand::Mem(m)) => m,
            _ => {
                return Err(SemError::InvalidOperand {
                    opcode: insn.opcode,
                    index: 1,
                    detail: "expected memory operand".into(),
                });
            }
        };
        let addr = resolve_mem_address(state, mem_op)?;

        // Load load_bytes bytes in little-endian order.
        let load_width = load_bytes * 8;
        let loaded = load_le_bytes(state, &addr, load_bytes, load_width);

        // Extend to destination width.
        let extended = if load_width == width {
            loaded
        } else if sign_extend {
            Formula::BvSignExt(Box::new(loaded), width)
        } else {
            Formula::BvZeroExt(Box::new(loaded), width)
        };

        let mut effects = vec![
            Effect::MemRead { address: addr.clone(), width_bytes: load_bytes },
            Effect::RegWrite { index: dst_idx, width, value: extended },
        ];

        if let Some(wb) = writeback_effect(state, mem_op) {
            effects.push(wb);
        }
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// Store variant: STRB (1 byte), STRH (2 bytes).
    fn sem_str_variant(
        &self,
        state: &MachineState,
        insn: &Instruction,
        store_bytes: u32,
    ) -> Result<Vec<Effect>, SemError> {
        let store_width = store_bytes * 8;
        let src_full = operand_to_formula(state, insn.operand(0), insn.opcode, 0, 64)?;
        // Truncate to the store width.
        let src = if store_width < 64 {
            Formula::BvExtract { inner: Box::new(src_full), high: store_width - 1, low: 0 }
        } else {
            src_full
        };

        let mem_op = match insn.operand(1) {
            Some(Operand::Mem(m)) => m,
            _ => {
                return Err(SemError::InvalidOperand {
                    opcode: insn.opcode,
                    index: 1,
                    detail: "expected memory operand".into(),
                });
            }
        };
        let addr = resolve_mem_address(state, mem_op)?;

        let mut effects =
            vec![Effect::MemWrite { address: addr.clone(), value: src, width_bytes: store_bytes }];

        if let Some(wb) = writeback_effect(state, mem_op) {
            effects.push(wb);
        }
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    // -----------------------------------------------------------------------
    // Branch variants
    // -----------------------------------------------------------------------

    /// BLR: branch with link to register.
    fn sem_blr(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let target = operand_to_formula(state, insn.operand(0), insn.opcode, 0, 64)?;
        let return_addr = Formula::BvAdd(
            Box::new(state.pc.clone()),
            Box::new(Formula::BitVec { value: 4, width: 64 }),
            64,
        );
        Ok(vec![
            Effect::Call { target: target.clone(), return_addr: return_addr.clone() },
            Effect::RegWrite { index: 30, width: 64, value: return_addr },
            Effect::PcUpdate { value: target },
        ])
    }

    /// CBZ/CBNZ: compare and branch (zero / non-zero).
    fn sem_cbz(
        &self,
        state: &MachineState,
        insn: &Instruction,
        non_zero: bool,
    ) -> Result<Vec<Effect>, SemError> {
        let rt_width = match insn.operand(0) {
            Some(Operand::Reg(r)) => u32::from(r.width),
            _ => {
                return Err(SemError::InvalidOperand {
                    opcode: insn.opcode,
                    index: 0,
                    detail: "expected register".into(),
                });
            }
        };
        let rt = operand_to_formula(state, insn.operand(0), insn.opcode, 0, rt_width)?;
        let target = branch_target_formula(insn)?;
        let fallthrough = Formula::BvAdd(
            Box::new(state.pc.clone()),
            Box::new(Formula::BitVec { value: 4, width: 64 }),
            64,
        );

        let is_zero =
            Formula::Eq(Box::new(rt), Box::new(Formula::BitVec { value: 0, width: rt_width }));
        let take_branch = if non_zero { Formula::Not(Box::new(is_zero)) } else { is_zero };

        let pc_val = Formula::Ite(Box::new(take_branch), Box::new(target), Box::new(fallthrough));
        Ok(vec![Effect::PcUpdate { value: pc_val }])
    }

    /// TBZ/TBNZ: test bit and branch.
    fn sem_tbz(
        &self,
        state: &MachineState,
        insn: &Instruction,
        non_zero: bool,
    ) -> Result<Vec<Effect>, SemError> {
        let rt = operand_to_formula(state, insn.operand(0), insn.opcode, 0, 64)?;

        // Bit position operand.
        let bit_pos = match insn.operand(1) {
            Some(Operand::BitPos(b)) => u32::from(*b),
            Some(Operand::Imm(v)) => *v as u32,
            _ => {
                return Err(SemError::InvalidOperand {
                    opcode: insn.opcode,
                    index: 1,
                    detail: "expected bit position".into(),
                });
            }
        };

        let target = branch_target_formula(insn)?;
        let fallthrough = Formula::BvAdd(
            Box::new(state.pc.clone()),
            Box::new(Formula::BitVec { value: 4, width: 64 }),
            64,
        );

        let bit = Formula::BvExtract { inner: Box::new(rt), high: bit_pos, low: bit_pos };
        let is_zero = Formula::Eq(Box::new(bit), Box::new(Formula::BitVec { value: 0, width: 1 }));
        let take_branch = if non_zero { Formula::Not(Box::new(is_zero)) } else { is_zero };

        let pc_val = Formula::Ite(Box::new(take_branch), Box::new(target), Box::new(fallthrough));
        Ok(vec![Effect::PcUpdate { value: pc_val }])
    }
}

// ---------------------------------------------------------------------------
// Helper functions
// ---------------------------------------------------------------------------

/// Extract destination register info from the first operand.
fn extract_dst_reg(insn: &Instruction) -> Result<(u8, bool, u32), SemError> {
    match insn.operand(0) {
        Some(Operand::Reg(r)) => {
            let is_sp = r.kind == RegKind::Sp;
            Ok((r.index, is_sp, u32::from(r.width)))
        }
        _ => Err(SemError::InvalidOperand {
            opcode: insn.opcode,
            index: 0,
            detail: "expected register destination".into(),
        }),
    }
}

/// Write to a register or the stack pointer.
fn write_reg_or_sp(index: u8, is_sp: bool, width: u32, value: Formula) -> Effect {
    if is_sp {
        // SP write: zero-extend to 64 bits if width < 64.
        let val64 = if width < 64 { Formula::BvZeroExt(Box::new(value), 64) } else { value };
        Effect::SpWrite { value: val64 }
    } else {
        Effect::RegWrite { index, width, value }
    }
}

/// PC = PC + 4 (standard sequential advance).
fn pc_advance(state: &MachineState, _insn: &Instruction) -> Effect {
    Effect::PcUpdate {
        value: Formula::BvAdd(
            Box::new(state.pc.clone()),
            Box::new(Formula::BitVec { value: 4, width: 64 }),
            64,
        ),
    }
}

/// Extract a branch target address as a Formula.
fn branch_target_formula(insn: &Instruction) -> Result<Formula, SemError> {
    for op in insn.operands() {
        if let Operand::PcRelAddr(addr) = op {
            return Ok(Formula::BitVec { value: *addr as i128, width: 64 });
        }
    }
    Err(SemError::InvalidOperand {
        opcode: insn.opcode,
        index: 0,
        detail: "no branch target found".into(),
    })
}

/// Compute a writeback effect for pre/post-indexed addressing.
fn writeback_effect(state: &MachineState, mem_op: &MemoryOperand) -> Option<Effect> {
    match mem_op {
        MemoryOperand::PreIndex { base, offset } | MemoryOperand::PostIndex { base, offset } => {
            let base_val = if base.kind == RegKind::Sp {
                state.read_sp(64)
            } else {
                state.read_gpr(base.index, 64)
            };
            let new_val = Formula::BvAdd(
                Box::new(base_val),
                Box::new(Formula::BitVec { value: *offset as i128, width: 64 }),
                64,
            );
            if base.kind == RegKind::Sp {
                Some(Effect::SpWrite { value: new_val })
            } else {
                Some(Effect::RegWrite { index: base.index, width: 64, value: new_val })
            }
        }
        _ => None,
    }
}

/// Compute NZCV for logical operations (AND, BIC, etc.).
/// C and V are set to zero; N and Z are derived from the result.
fn logic_nzcv(result: &Formula, width: u32) -> Effect {
    let sign_bit = width - 1;
    let n = Formula::Eq(
        Box::new(Formula::BvExtract {
            inner: Box::new(result.clone()),
            high: sign_bit,
            low: sign_bit,
        }),
        Box::new(Formula::BitVec { value: 1, width: 1 }),
    );
    let z = Formula::Eq(Box::new(result.clone()), Box::new(Formula::BitVec { value: 0, width }));
    Effect::FlagUpdate { n, z, c: Formula::Bool(false), v: Formula::Bool(false) }
}

/// Extract an immediate value from an operand.
fn extract_imm(insn: &Instruction, index: usize) -> Result<u64, SemError> {
    match insn.operand(index) {
        Some(Operand::Imm(v)) => Ok(*v),
        Some(Operand::SignedImm(v)) => Ok(*v as u64),
        _ => Err(SemError::InvalidOperand {
            opcode: insn.opcode,
            index,
            detail: "expected immediate".into(),
        }),
    }
}

/// Extract a condition code from an operand.
fn extract_condition(insn: &Instruction, index: usize) -> Result<Condition, SemError> {
    match insn.operand(index) {
        Some(Operand::Cond(c)) => Ok(*c),
        _ => Err(SemError::InvalidOperand {
            opcode: insn.opcode,
            index,
            detail: "expected condition".into(),
        }),
    }
}

/// Convert a `Condition` to a boolean Formula based on the current flags.
// tRust: #564 — made public so semantic_lift can build branch condition formulas.
pub fn condition_to_formula(state: &MachineState, cond: Condition) -> Formula {
    let n = &state.flags.n;
    let z = &state.flags.z;
    let c = &state.flags.c;
    let v = &state.flags.v;
    match cond {
        Condition::Eq => z.clone(),                         // Z == 1
        Condition::Ne => Formula::Not(Box::new(z.clone())), // Z == 0
        Condition::Cs => c.clone(),                         // C == 1 (HS)
        Condition::Cc => Formula::Not(Box::new(c.clone())), // C == 0 (LO)
        Condition::Mi => n.clone(),                         // N == 1
        Condition::Pl => Formula::Not(Box::new(n.clone())), // N == 0
        Condition::Vs => v.clone(),                         // V == 1
        Condition::Vc => Formula::Not(Box::new(v.clone())), // V == 0
        Condition::Hi => {
            // C == 1 && Z == 0
            Formula::And(vec![c.clone(), Formula::Not(Box::new(z.clone()))])
        }
        Condition::Ls => {
            // C == 0 || Z == 1
            Formula::Or(vec![Formula::Not(Box::new(c.clone())), z.clone()])
        }
        Condition::Ge => {
            // N == V
            Formula::Eq(Box::new(n.clone()), Box::new(v.clone()))
        }
        Condition::Lt => {
            // N != V
            Formula::Not(Box::new(Formula::Eq(Box::new(n.clone()), Box::new(v.clone()))))
        }
        Condition::Gt => {
            // Z == 0 && N == V
            Formula::And(vec![
                Formula::Not(Box::new(z.clone())),
                Formula::Eq(Box::new(n.clone()), Box::new(v.clone())),
            ])
        }
        Condition::Le => {
            // Z == 1 || N != V
            Formula::Or(vec![
                z.clone(),
                Formula::Not(Box::new(Formula::Eq(Box::new(n.clone()), Box::new(v.clone())))),
            ])
        }
        Condition::Al | Condition::Nv => Formula::Bool(true),
        _ => Formula::Bool(true), // future condition codes
    }
}

/// Reverse bytes within a value of the given width, producing a result of
/// result_width bits.
fn reverse_bytes(val: &Formula, val_width: u32, result_width: u32) -> Formula {
    let num_bytes = val_width / 8;
    let mut result = Formula::BitVec { value: 0, width: result_width };
    for i in 0..num_bytes {
        let src_byte =
            Formula::BvExtract { inner: Box::new(val.clone()), high: i * 8 + 7, low: i * 8 };
        let dest_pos = (num_bytes - 1 - i) * 8;
        let extended = Formula::BvZeroExt(Box::new(src_byte), result_width);
        if dest_pos > 0 {
            let shifted = Formula::BvShl(
                Box::new(extended),
                Box::new(Formula::BitVec { value: i128::from(dest_pos), width: result_width }),
                result_width,
            );
            result = Formula::BvOr(Box::new(result), Box::new(shifted), result_width);
        } else {
            result = Formula::BvOr(Box::new(result), Box::new(extended), result_width);
        }
    }
    result
}

/// Load `num_bytes` from byte-addressed memory in little-endian order,
/// producing a bitvector of `result_width` bits.
fn load_le_bytes(
    state: &MachineState,
    addr: &Formula,
    num_bytes: u32,
    result_width: u32,
) -> Formula {
    let mut result = Formula::BitVec { value: 0, width: result_width };
    for i in 0..num_bytes {
        let byte_addr = if i == 0 {
            addr.clone()
        } else {
            Formula::BvAdd(
                Box::new(addr.clone()),
                Box::new(Formula::BitVec { value: i128::from(i), width: 64 }),
                64,
            )
        };
        let byte_val = Formula::Select(Box::new(state.memory.clone()), Box::new(byte_addr));
        let extended = Formula::BvZeroExt(Box::new(byte_val), result_width);
        if i == 0 {
            result = extended;
        } else {
            let shift_amt = Formula::BitVec { value: i128::from(i * 8), width: result_width };
            let shifted = Formula::BvShl(Box::new(extended), Box::new(shift_amt), result_width);
            result = Formula::BvOr(Box::new(result), Box::new(shifted), result_width);
        }
    }
    result
}
