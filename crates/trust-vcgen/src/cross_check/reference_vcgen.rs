// trust-vcgen/cross_check/reference_vcgen.rs: Independent reference VC generator (#192)
//
// tRust #953: The primary generator (`generate_vcs`) emits safety VCs
// (overflow, divzero, remainder-by-zero, negation-overflow) for callers that
// still invoke it directly (e.g., `real_z4_verification`, `m5_e2e_loop`). The
// reference generator below mirrors those kinds by walking MIR via a
// completely independent code path so cross-check can confirm both generators
// agree on the coarse safety-VC categorisation.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{
    AssertMessage, BinOp, ConstValue, Operand, Rvalue, Statement, Terminator, Ty, UnOp, VcKind,
    VerifiableFunction,
};

/// Independent VC generator that walks MIR directly.
///
/// tRust #953: Emits the same safety VC kinds as the primary `generate_vcs`
/// path under pipeline-v2 (overflow, divzero, remzero, negation-overflow).
/// The walking order and logic are deliberately different from the primary
/// implementation so cross-check catches generator drift.
pub(crate) fn reference_vcgen(func: &VerifiableFunction) -> Vec<VcKind> {
    let mut kinds = Vec::new();

    for block in &func.body.blocks {
        // 1. Overflow VCs: Assert terminators carrying an Overflow message.
        if let Terminator::Assert { msg: AssertMessage::Overflow(op), .. } = &block.terminator
            && let Some((lhs_ty, rhs_ty)) = find_checked_binop_tys(block, *op, func)
        {
            kinds.push(VcKind::ArithmeticOverflow { op: *op, operand_tys: (lhs_ty, rhs_ty) });
        }

        // 2. Div/Rem VCs from BinaryOp statements. Skip constant non-zero
        //    divisors — these cannot produce a zero-divisor VC.
        for stmt in &block.stmts {
            if let Statement::Assign { rvalue, .. } = stmt {
                match rvalue {
                    Rvalue::BinaryOp(BinOp::Div, _, divisor)
                        if !divisor_is_nonzero_constant(divisor) =>
                    {
                        kinds.push(VcKind::DivisionByZero);
                    }
                    Rvalue::BinaryOp(BinOp::Rem, _, divisor)
                        if !divisor_is_nonzero_constant(divisor) =>
                    {
                        kinds.push(VcKind::RemainderByZero);
                    }
                    Rvalue::UnaryOp(UnOp::Neg, operand) => {
                        let ty = operand_ty_owned(operand, func);
                        if ty.is_signed() {
                            kinds.push(VcKind::NegationOverflow { ty });
                        }
                    }
                    _ => {}
                }
            }
        }
    }

    kinds
}

/// If this block contains an `Assign { rvalue: CheckedBinaryOp(op, lhs, rhs) }`
/// statement, return the operand types as `(lhs_ty, rhs_ty)`.
fn find_checked_binop_tys(
    block: &trust_types::BasicBlock,
    op: BinOp,
    func: &VerifiableFunction,
) -> Option<(Ty, Ty)> {
    for stmt in &block.stmts {
        if let Statement::Assign { rvalue: Rvalue::CheckedBinaryOp(stmt_op, lhs, rhs), .. } = stmt
            && *stmt_op == op
        {
            return Some((operand_ty_owned(lhs, func), operand_ty_owned(rhs, func)));
        }
    }
    None
}

/// Return true iff `divisor` is a constant whose numeric value is non-zero.
/// Variable divisors and zero constants conservatively return false.
fn divisor_is_nonzero_constant(divisor: &Operand) -> bool {
    match divisor {
        Operand::Constant(ConstValue::Int(v)) => *v != 0,
        Operand::Constant(ConstValue::Uint(v, _)) => *v != 0,
        _ => false,
    }
}

/// Get the type of an operand by looking up its local declaration.
fn operand_ty_owned(operand: &Operand, func: &VerifiableFunction) -> Ty {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => {
            func.body.locals.get(place.local).map(|decl| decl.ty.clone()).unwrap_or(Ty::Unit)
        }
        Operand::Constant(cv) => match cv {
            ConstValue::Bool(_) => Ty::Bool,
            ConstValue::Int(_) => Ty::Unit,
            ConstValue::Uint(_, _) => Ty::Unit,
            ConstValue::Float(_) => Ty::Unit,
            ConstValue::Unit => Ty::Unit,
            _ => Ty::Unit,
        },
        _ => Ty::Unit,
    }
}
