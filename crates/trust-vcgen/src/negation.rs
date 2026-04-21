// trust-vcgen/negation.rs: Signed negation overflow VC generation
//
// Generates VCs for unary negation on signed integers. The only case
// that overflows is `-x` when `x == INT_MIN`, because the two's complement
// representation has one more negative value than positive values.
//
// For `Neg(x)` on an N-bit signed type:
//   Safe condition: x != -(2^(N-1))
//   Violation (VC): x == -(2^(N-1))
//
// Unsigned negation is not applicable (Rust does not allow `-` on unsigned
// types without explicit wrapping).
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::*;

use crate::{operand_to_formula, operand_ty};

/// Check an rvalue for negation operations that could overflow.
pub(crate) fn check_negation_overflow(
    func: &VerifiableFunction,
    _block: &BasicBlock,
    rvalue: &Rvalue,
    stmt_span: &SourceSpan, // tRust: per-statement source span for diagnostics
    vcs: &mut Vec<VerificationCondition>,
) {
    let Rvalue::UnaryOp(UnOp::Neg, operand) = rvalue else {
        return;
    };

    if let Some(vc) = build_negation_overflow_vc(func, operand, stmt_span) {
        vcs.push(vc);
    }
}

fn build_negation_overflow_vc(
    func: &VerifiableFunction,
    operand: &Operand,
    stmt_span: &SourceSpan, // tRust: per-statement source span for diagnostics
) -> Option<VerificationCondition> {
    let ty = operand_ty(func, operand)?;

    // Only signed integer types can overflow on negation
    if !ty.is_signed() {
        return None;
    }

    let width = ty.int_width()?;

    // Check if operand is a constant that is not INT_MIN (trivially safe)
    // tRust: Special-case width 128 to avoid i128 negate overflow.
    let int_min = if width == 128 { i128::MIN } else { -(1i128 << (width - 1)) };
    if is_safe_negation_constant(operand, int_min) {
        return None;
    }

    let val_formula = operand_to_formula(func, operand);

    // Constrain the input to its valid range
    let int_max = if width == 128 { i128::MAX } else { (1i128 << (width - 1)) - 1 };
    let input_in_range = Formula::And(vec![
        Formula::Le(Box::new(Formula::Int(int_min)), Box::new(val_formula.clone())),
        Formula::Le(Box::new(val_formula.clone()), Box::new(Formula::Int(int_max))),
    ]);

    // Violation: value == INT_MIN (negating INT_MIN overflows)
    let is_int_min = Formula::Eq(Box::new(val_formula), Box::new(Formula::Int(int_min)));

    let formula = Formula::And(vec![input_in_range, is_int_min]);

    Some(VerificationCondition {
        kind: VcKind::NegationOverflow { ty },
        function: func.name.clone(),
        location: stmt_span.clone(), // tRust: use per-statement span, not function span
        formula,
        contract_metadata: None,
    })
}

/// Check if the operand is a constant known to not be INT_MIN.
fn is_safe_negation_constant(op: &Operand, int_min: i128) -> bool {
    match op {
        Operand::Constant(ConstValue::Int(n)) => *n != int_min,
        _ => false,
    }
}

#[cfg(all(test, not(feature = "pipeline-v2")))]
mod tests {
    use super::*;

    /// Helper: build a function with a single negation operation.
    fn make_neg_func(ty: Ty, operand: Operand) -> VerifiableFunction {
        let ret_ty = ty.clone();
        VerifiableFunction {
            name: "neg_test".to_string(),
            def_path: "test::neg_test".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: ret_ty.clone(), name: None },
                    LocalDecl { index: 1, ty, name: Some("x".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::UnaryOp(UnOp::Neg, operand),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: ret_ty,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    #[test]
    fn test_negation_i32_variable_generates_vc() {
        // -x on i32 variable: x could be i32::MIN
        let func = make_neg_func(Ty::i32(), Operand::Copy(Place::local(1)));

        let vcs = crate::generate_vcs(&func);
        let neg_vcs: Vec<_> =
            vcs.iter().filter(|vc| matches!(vc.kind, VcKind::NegationOverflow { .. })).collect();

        assert_eq!(neg_vcs.len(), 1, "negation of i32 variable must generate a VC");
        assert_eq!(neg_vcs[0].kind.proof_level(), ProofLevel::L0Safety);
    }

    #[test]
    fn test_negation_i8_variable_generates_vc() {
        // -x on i8 variable: x could be -128
        let func =
            make_neg_func(Ty::Int { width: 8, signed: true }, Operand::Copy(Place::local(1)));

        let vcs = crate::generate_vcs(&func);
        let neg_vcs: Vec<_> =
            vcs.iter().filter(|vc| matches!(vc.kind, VcKind::NegationOverflow { .. })).collect();

        assert_eq!(neg_vcs.len(), 1, "negation of i8 variable must generate a VC");
    }

    #[test]
    fn test_negation_safe_constant() {
        // -42 on i32 is trivially safe (42 != i32::MIN)
        let func = make_neg_func(Ty::i32(), Operand::Constant(ConstValue::Int(42)));

        let vcs = crate::generate_vcs(&func);
        let neg_vcs: Vec<_> =
            vcs.iter().filter(|vc| matches!(vc.kind, VcKind::NegationOverflow { .. })).collect();

        assert!(neg_vcs.is_empty(), "negation of constant 42 is safe");
    }

    #[test]
    fn test_negation_int_min_constant() {
        // operand_ty infers ConstValue::Int as i64 (width 64), so use i64::MIN
        // to trigger the INT_MIN detection for the inferred type
        let func = make_neg_func(
            Ty::isize(), // matches inferred i64 width
            Operand::Constant(ConstValue::Int(i128::from(i64::MIN))),
        );

        let vcs = crate::generate_vcs(&func);
        let neg_vcs: Vec<_> =
            vcs.iter().filter(|vc| matches!(vc.kind, VcKind::NegationOverflow { .. })).collect();

        assert_eq!(neg_vcs.len(), 1, "negation of INT_MIN constant must generate a VC");
    }

    #[test]
    fn test_negation_unsigned_no_vc() {
        // Negation on unsigned types should not generate a VC
        // (Rust does not allow unary minus on unsigned, but if somehow present
        // in MIR we skip it since unsigned negation is not overflow — it's
        // a type error)
        let func = make_neg_func(Ty::u32(), Operand::Copy(Place::local(1)));

        let vcs = crate::generate_vcs(&func);
        let neg_vcs: Vec<_> =
            vcs.iter().filter(|vc| matches!(vc.kind, VcKind::NegationOverflow { .. })).collect();

        assert!(neg_vcs.is_empty(), "unsigned negation should not generate overflow VC");
    }

    #[test]
    fn test_negation_not_on_bool_no_vc() {
        // UnaryOp(Not, ...) is bitwise NOT, not negation — should not generate VC
        let func = VerifiableFunction {
            name: "not_test".to_string(),
            def_path: "test::not_test".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Bool, name: None },
                    LocalDecl { index: 1, ty: Ty::Bool, name: Some("x".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::UnaryOp(UnOp::Not, Operand::Copy(Place::local(1))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: Ty::Bool,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        let vcs = crate::generate_vcs(&func);
        let neg_vcs: Vec<_> =
            vcs.iter().filter(|vc| matches!(vc.kind, VcKind::NegationOverflow { .. })).collect();

        assert!(neg_vcs.is_empty(), "bitwise NOT should not generate negation overflow VC");
    }

    #[test]
    fn test_negation_vc_description() {
        let kind = VcKind::NegationOverflow { ty: Ty::i32() };
        let desc = kind.description();
        assert!(desc.contains("negation overflow"), "description should mention negation overflow");
        assert_eq!(kind.proof_level(), ProofLevel::L0Safety);
    }
}
