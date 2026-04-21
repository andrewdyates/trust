// trust-vcgen/cross_check/reference_vcgen.rs: Independent reference VC generator (#192)
//
// tRust #792: overflow, divzero, shifts, casts, float_ops, and asserts checks
// are now handled by zani-lib via the MIR router pipeline. This reference
// generator only checks negation overflow (matching the primary pipeline).
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{Rvalue, Statement, UnOp, VcKind, VerifiableFunction};

/// Independent VC generator that walks MIR directly.
///
/// tRust #792: Only produces NegationOverflow VCs — overflow, divzero, shifts,
/// casts, float_ops, and asserts checks are now in zani-lib. This mirrors
/// the primary pipeline's `generate_vcs()` which only calls
/// `negation::check_negation_overflow` and `rvalue_safety::check_rvalue_safety`.
pub(crate) fn reference_vcgen(func: &VerifiableFunction) -> Vec<VcKind> {
    let mut kinds = Vec::new();

    for block in &func.body.blocks {
        for stmt in &block.stmts {
            if let Statement::Assign { rvalue, .. } = stmt {
                reference_check_rvalue(rvalue, func, &mut kinds);
            }
        }
    }

    kinds
}

/// Check an rvalue for safety-relevant operations.
///
/// tRust #792: Only negation overflow remains in trust-vcgen.
fn reference_check_rvalue(
    rvalue: &Rvalue,
    func: &VerifiableFunction,
    kinds: &mut Vec<VcKind>,
) {
    if let Rvalue::UnaryOp(UnOp::Neg, operand) = rvalue {
        let ty = operand_ty_owned(operand, func);
        if ty.is_signed() {
            kinds.push(VcKind::NegationOverflow { ty });
        }
    }
}

/// Get the type of an operand by looking up its local declaration.
fn operand_ty_owned(operand: &trust_types::Operand, func: &VerifiableFunction) -> trust_types::Ty {
    match operand {
        trust_types::Operand::Copy(place) | trust_types::Operand::Move(place) => {
            func.body
                .locals
                .get(place.local)
                .map(|decl| decl.ty.clone())
                .unwrap_or(trust_types::Ty::Unit)
        }
        trust_types::Operand::Constant(cv) => match cv {
            trust_types::ConstValue::Bool(_) => trust_types::Ty::Bool,
            trust_types::ConstValue::Int(_) => trust_types::Ty::Unit,
            trust_types::ConstValue::Uint(_, _) => trust_types::Ty::Unit,
            trust_types::ConstValue::Float(_) => trust_types::Ty::Unit,
            trust_types::ConstValue::Unit => trust_types::Ty::Unit,
            _ => trust_types::Ty::Unit,
        },
        _ => trust_types::Ty::Unit,
    }
}
