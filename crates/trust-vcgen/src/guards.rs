// trust-vcgen/guards.rs: Guard condition extraction and VC assumption threading
//
// Converts GuardCondition (from MIR control flow) into Formula assumptions.
// When a VC is generated inside a guarded block, the guard conditions on
// the path to that block become assumptions: guard => vc_formula.
//
// Part of #21: Guard condition extraction and clause discovery from MIR.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

// Known limitation: path_map() in trust-types uses first-predecessor-wins
// for guard accumulation at join points. A block reachable from multiple
// branches may only have one branch's guards. This is acceptable for
// soundness (guards are assumptions, not proof obligations -- missing a
// guard makes the VC harder to discharge, not unsound), but may cause
// solver timeouts on paths where guards would have simplified the formula.
// See trust-types/src/model.rs path_map() for details.

use trust_types::{
    BasicBlock, BinOp, ConstValue, Formula, GuardCondition, Operand, Rvalue, Sort, Statement,
    Terminator, Ty, VerifiableFunction,
};

#[cfg(test)]
use trust_types::{AssertMessage, LocalDecl, Place, SourceSpan, VerifiableBody};

use crate::range::{type_max_formula, type_min_formula};
use crate::u128_to_formula;
use crate::{operand_to_formula, operand_ty, slice_len_formula};

/// Convert a single GuardCondition into an SMT Formula.
///
/// SwitchIntMatch: discr == value
/// SwitchIntOtherwise: discr != v1 AND discr != v2 AND ...
/// AssertHolds: cond == expected
/// AssertFails: cond != expected (negation of the assert condition)
pub(crate) fn guard_to_formula(func: &VerifiableFunction, guard: &GuardCondition) -> Formula {
    match guard {
        GuardCondition::SwitchIntMatch { discr, value } => {
            if matches!(operand_ty(func, discr), Some(Ty::Bool))
                && let Some(formula) = bool_switch_semantics(func, discr, *value != 0)
            {
                return formula;
            }
            let discr_f = operand_to_formula(func, discr);
            if matches!(operand_ty(func, discr), Some(Ty::Bool)) {
                if *value == 0 { Formula::Not(Box::new(discr_f)) } else { discr_f }
            } else {
                let value_f = u128_to_formula(*value);
                Formula::Eq(Box::new(discr_f), Box::new(value_f))
            }
        }
        GuardCondition::SwitchIntOtherwise { discr, excluded_values } => {
            if matches!(operand_ty(func, discr), Some(Ty::Bool)) {
                let excludes_false = excluded_values.contains(&0);
                let excludes_true = excluded_values.iter().any(|value| *value != 0);
                if let Some(truth_value) = match (excludes_false, excludes_true) {
                    (true, false) => Some(true),
                    (false, true) => Some(false),
                    _ => None,
                } && let Some(formula) = bool_switch_semantics(func, discr, truth_value)
                {
                    return formula;
                }
                let discr_f = operand_to_formula(func, discr);
                return match (excludes_false, excludes_true) {
                    (false, false) => Formula::Bool(true),
                    (true, false) => discr_f,
                    (false, true) => Formula::Not(Box::new(discr_f)),
                    (true, true) => Formula::Bool(false),
                };
            }
            let discr_f = operand_to_formula(func, discr);
            if excluded_values.is_empty() {
                return Formula::Bool(true);
            }
            let not_eqs: Vec<Formula> = excluded_values
                .iter()
                .map(|v| {
                    Formula::Not(Box::new(Formula::Eq(
                        Box::new(discr_f.clone()),
                        Box::new(u128_to_formula(*v)),
                    )))
                })
                .collect();
            if not_eqs.len() == 1 {
                // SAFETY: len == 1 guarantees .next() returns Some.
                not_eqs
                    .into_iter()
                    .next()
                    .unwrap_or_else(|| unreachable!("empty iter despite len == 1"))
            } else {
                Formula::And(not_eqs)
            }
        }
        GuardCondition::AssertHolds { cond, expected } => {
            let cond_f = operand_to_formula(func, cond);
            if *expected {
                // Assert expects true: cond == true
                cond_f
            } else {
                // Assert expects false: cond == false, i.e., NOT cond
                Formula::Not(Box::new(cond_f))
            }
        }
        GuardCondition::AssertFails { cond, expected, .. } => {
            // The assert failed, so cond != expected
            let cond_f = operand_to_formula(func, cond);
            if *expected {
                // Expected true but got false
                Formula::Not(Box::new(cond_f))
            } else {
                // Expected false but got true
                cond_f
            }
        }
        _ => Formula::Bool(false), /* unknown guard condition */
    }
}

fn bool_switch_semantics(
    func: &VerifiableFunction,
    discr: &Operand,
    truth_value: bool,
) -> Option<Formula> {
    let len = is_empty_result_len(func, discr)?;
    Some(if truth_value {
        Formula::Eq(Box::new(len), Box::new(Formula::Int(0)))
    } else {
        Formula::Gt(Box::new(len), Box::new(Formula::Int(0)))
    })
}

fn is_empty_result_len(func: &VerifiableFunction, discr: &Operand) -> Option<Formula> {
    let local = match discr {
        Operand::Copy(place) | Operand::Move(place) if place.projections.is_empty() => place.local,
        _ => return None,
    };
    let (callee, arg) = call_defining_local(func, local)?;
    if !callee.to_lowercase().contains("is_empty") {
        return None;
    }
    slice_len_formula(func, arg)
}

fn call_defining_local<'a>(
    func: &'a VerifiableFunction,
    local: usize,
) -> Option<(&'a str, &'a Operand)> {
    for block in &func.body.blocks {
        let Terminator::Call { func: callee, args, dest, .. } = &block.terminator else {
            continue;
        };
        if dest.local == local && dest.projections.is_empty() {
            return args.first().map(|arg| (callee.as_str(), arg));
        }
    }
    None
}

/// Convert a sequence of guard conditions into a single conjunction Formula.
///
/// An empty guard list yields `true` (no assumptions).
pub(crate) fn guards_to_assumption(
    func: &VerifiableFunction,
    guards: &[GuardCondition],
) -> Formula {
    if guards.is_empty() {
        return Formula::Bool(true);
    }
    let formulas: Vec<Formula> = guards.iter().map(|g| guard_to_formula(func, g)).collect();
    if formulas.len() == 1 {
        // SAFETY: len == 1 guarantees .next() returns Some.
        formulas.into_iter().next().unwrap_or_else(|| unreachable!("empty iter despite len == 1"))
    } else {
        Formula::And(formulas)
    }
}

/// Wrap a VC formula with path guard assumptions.
///
/// Returns: guards => vc_formula
/// If guards is empty (or trivially true), returns the vc_formula unchanged.
#[must_use]
pub(crate) fn guarded_formula(
    func: &VerifiableFunction,
    guards: &[GuardCondition],
    vc_formula: Formula,
) -> Formula {
    if guards.is_empty() {
        return vc_formula;
    }
    let assumption = guards_to_assumption(func, guards);
    // VC convention: formula is SAT iff violation exists.
    // With guards: we only want violations reachable under the guard.
    // So: guard_assumption AND vc_violation_formula
    Formula::And(vec![assumption, vc_formula])
}

/// tRust #621: Extract semantic assert-passed guards from a block.
///
/// When a block contains a CheckedBinaryOp assignment followed by an Assert
/// terminator on the overflow flag, the assert passing implies:
/// 1. A range constraint: the result is in [min, max] for the type
/// 2. A result definition: `_N.0 = lhs op rhs` (the `.0` field equals the
///    mathematical result), which connects the tuple result to its operands
///
/// Returns a (possibly empty) Vec of formulas. The range constraint ensures
/// the solver knows the assert-passed semantics (e.g., hi >= lo for unsigned
/// CheckedSub), while the result definition enables dataflow tracking through
/// subsequent blocks.
///
/// This is different from the syntactic guard (`NOT _flag`) that path_map
/// already propagates: the syntactic guard refers to an unconstrained boolean
/// variable, while the semantic guard encodes the actual arithmetic meaning.
pub(crate) fn extract_assert_passed_semantics(
    func: &VerifiableFunction,
    block: &BasicBlock,
) -> Vec<Formula> {
    // Pattern: Assert { cond: Copy(_N.1), expected: false, target } means
    // "continue to target only if _N.1 is false (no overflow)".
    // We need to find the CheckedBinaryOp that defines _N.
    let Terminator::Assert { cond, expected: false, .. } = &block.terminator else {
        return Vec::new();
    };

    // The cond operand should be a field projection .1 on a tuple local
    // produced by CheckedBinaryOp.
    let cond_place = match cond {
        trust_types::Operand::Copy(p) | trust_types::Operand::Move(p) => p,
        _ => return Vec::new(),
    };

    // Check it's a .1 field projection (the overflow flag)
    if cond_place.projections.len() != 1 {
        return Vec::new();
    }
    let trust_types::Projection::Field(1) = &cond_place.projections[0] else {
        return Vec::new();
    };

    let tuple_local = cond_place.local;

    // Find the CheckedBinaryOp statement that assigns to this local.
    for stmt in &block.stmts {
        let Statement::Assign { place, rvalue, .. } = stmt else {
            continue;
        };
        if place.local != tuple_local || !place.projections.is_empty() {
            continue;
        }
        let Rvalue::CheckedBinaryOp(op, lhs, rhs) = rvalue else {
            continue;
        };

        // Found the pattern. Build the semantic formulas.
        let lhs_f = operand_to_formula(func, lhs);
        let rhs_f = operand_to_formula(func, rhs);
        let Some(lhs_ty) = operand_ty(func, lhs) else {
            return Vec::new();
        };
        let Some(width) = lhs_ty.int_width() else {
            return Vec::new();
        };
        let signed = lhs_ty.is_signed();

        let result = match op {
            BinOp::Add => Formula::Add(Box::new(lhs_f.clone()), Box::new(rhs_f.clone())),
            BinOp::Sub => Formula::Sub(Box::new(lhs_f.clone()), Box::new(rhs_f.clone())),
            BinOp::Mul => Formula::Mul(Box::new(lhs_f.clone()), Box::new(rhs_f.clone())),
            _ => return Vec::new(),
        };

        // No-overflow means result is in [min, max] for the type.
        let min_f = type_min_formula(width, signed);
        let max_f = type_max_formula(width, signed);

        let in_range = Formula::And(vec![
            Formula::Le(Box::new(min_f), Box::new(result.clone())),
            Formula::Le(Box::new(result.clone()), Box::new(max_f)),
        ]);

        // tRust #621: Also define _N.0 = result_formula. This connects the
        // tuple's result field to the actual arithmetic expression, enabling
        // dataflow tracking when _N.0 is read in subsequent blocks.
        let tuple_name = func
            .body
            .locals
            .get(tuple_local)
            .and_then(|d| d.name.as_deref())
            .map_or_else(|| format!("_{tuple_local}"), |n| n.to_string());
        let result_field_name = format!("{tuple_name}.0");
        let result_def =
            Formula::Eq(Box::new(Formula::Var(result_field_name, Sort::Int)), Box::new(result));

        // tRust #621: Include input range constraints for the operands of the
        // CheckedBinaryOp. Without these, variables like `hi` that appear in the
        // semantic guard but not in the downstream VC formula would be unconstrained,
        // allowing the solver to pick out-of-range values (e.g., hi > u64::MAX)
        // that satisfy the guard while still causing a false overflow violation.
        let lhs_range = crate::range::input_range_constraint(&lhs_f, width, signed);
        let rhs_range = crate::range::input_range_constraint(&rhs_f, width, signed);

        return vec![in_range, result_def, lhs_range, rhs_range];
    }

    Vec::new()
}

/// tRust #621: Extract dataflow definitions from a block's assignment statements.
///
/// Each `Assign { place, rvalue }` is converted to `Eq(Var(place_name), rvalue_formula)`.
/// This allows the solver to know that intermediate locals (e.g., `_5 = _4 / 2`)
/// are constrained by their definitions, not free variables.
///
/// CheckedBinaryOp assignments are skipped (handled by `extract_assert_passed_semantics`).
pub(crate) fn extract_block_definitions(
    func: &VerifiableFunction,
    block: &BasicBlock,
) -> Vec<Formula> {
    let mut defs = Vec::new();

    for stmt in &block.stmts {
        let Statement::Assign { place, rvalue, .. } = stmt else {
            continue;
        };

        // Skip CheckedBinaryOp — its result definition is handled by semantic guards.
        if matches!(rvalue, Rvalue::CheckedBinaryOp(..)) {
            continue;
        }

        let dest_name = crate::place_to_var_name(func, place);
        let dest_sort = func
            .body
            .locals
            .get(place.local)
            .map(|decl| match &decl.ty {
                Ty::Int { .. } => Sort::Int,
                ty => Sort::from_ty(ty),
            })
            .unwrap_or(Sort::Int);
        let rvalue_formula = match rvalue {
            Rvalue::Use(operand) => operand_to_formula(func, operand),
            Rvalue::BinaryOp(op, lhs, rhs) => {
                let lhs_ty = operand_ty(func, lhs);
                if lhs_ty.as_ref().is_some_and(|ty| matches!(ty, Ty::Bool)) {
                    let l = operand_to_formula(func, lhs);
                    let r = operand_to_formula(func, rhs);
                    match op {
                        BinOp::BitAnd => Formula::And(vec![l, r]),
                        BinOp::BitOr => Formula::Or(vec![l, r]),
                        BinOp::BitXor => {
                            Formula::Not(Box::new(Formula::Eq(Box::new(l), Box::new(r))))
                        }
                        _ => {
                            // tRust #782: Pass signedness for correct right-shift selection.
                            let width = lhs_ty.as_ref().and_then(|ty| ty.int_width());
                            let signed = lhs_ty.as_ref().is_some_and(|ty| ty.is_signed());
                            crate::chc::binop_to_formula(*op, l, r, width, signed)
                        }
                    }
                } else if let Some(Ty::Float { width }) = lhs_ty {
                    match float_binop_to_formula(func, *op, lhs, rhs, width) {
                        Some(formula) => formula,
                        None => continue,
                    }
                } else {
                    let l = operand_to_formula(func, lhs);
                    let r = operand_to_formula(func, rhs);
                    // tRust #782: Pass signedness for correct right-shift selection.
                    let width = lhs_ty.as_ref().and_then(|ty| ty.int_width());
                    let signed = lhs_ty.as_ref().is_some_and(|ty| ty.is_signed());
                    crate::chc::binop_to_formula(*op, l, r, width, signed)
                }
            }
            Rvalue::UnaryOp(trust_types::UnOp::Neg, op) => {
                Formula::Neg(Box::new(operand_to_formula(func, op)))
            }
            Rvalue::UnaryOp(trust_types::UnOp::Not, op) => {
                Formula::Not(Box::new(operand_to_formula(func, op)))
            }
            Rvalue::UnaryOp(trust_types::UnOp::PtrMetadata, op) => match slice_len_formula(func, op)
            {
                Some(formula) => formula,
                None => continue,
            },
            Rvalue::Cast(op, _ty) => operand_to_formula(func, op),
            // Skip complex rvalues — not needed for basic dataflow tracking.
            _ => continue,
        };

        defs.push(Formula::Eq(
            Box::new(Formula::Var(dest_name, dest_sort)),
            Box::new(rvalue_formula),
        ));
    }

    defs
}

fn float_binop_to_formula(
    func: &VerifiableFunction,
    op: BinOp,
    lhs: &Operand,
    rhs: &Operand,
    width: u32,
) -> Option<Formula> {
    match op {
        BinOp::Eq => Some(float_eq_formula(func, lhs, rhs, width)),
        BinOp::Ne => Some(Formula::Not(Box::new(float_eq_formula(func, lhs, rhs, width)))),
        BinOp::Lt => Some(Formula::BvULt(
            Box::new(float_magnitude_formula(func, lhs, width)),
            Box::new(float_magnitude_formula(func, rhs, width)),
            width - 1,
        )),
        BinOp::Le => Some(Formula::BvULe(
            Box::new(float_magnitude_formula(func, lhs, width)),
            Box::new(float_magnitude_formula(func, rhs, width)),
            width - 1,
        )),
        BinOp::Gt => Some(Formula::BvULt(
            Box::new(float_magnitude_formula(func, rhs, width)),
            Box::new(float_magnitude_formula(func, lhs, width)),
            width - 1,
        )),
        BinOp::Ge => Some(Formula::BvULe(
            Box::new(float_magnitude_formula(func, rhs, width)),
            Box::new(float_magnitude_formula(func, lhs, width)),
            width - 1,
        )),
        _ => None,
    }
}

fn float_eq_formula(
    func: &VerifiableFunction,
    lhs: &Operand,
    rhs: &Operand,
    width: u32,
) -> Formula {
    if float_is_zero_operand(lhs) || float_is_zero_operand(rhs) {
        let nonzero_side = if float_is_zero_operand(lhs) { rhs } else { lhs };
        Formula::Eq(
            Box::new(float_magnitude_formula(func, nonzero_side, width)),
            Box::new(Formula::BitVec { value: 0, width: width - 1 }),
        )
    } else {
        Formula::Eq(
            Box::new(float_operand_formula(func, lhs, width)),
            Box::new(float_operand_formula(func, rhs, width)),
        )
    }
}

fn float_magnitude_formula(func: &VerifiableFunction, operand: &Operand, width: u32) -> Formula {
    Formula::BvExtract {
        inner: Box::new(float_operand_formula(func, operand, width)),
        high: width - 2,
        low: 0,
    }
}

fn float_operand_formula(func: &VerifiableFunction, operand: &Operand, width: u32) -> Formula {
    match operand {
        Operand::Constant(ConstValue::Float(value)) => Formula::BitVec {
            value: match width {
                32 => i128::from(((*value) as f32).to_bits()),
                64 => i128::from(value.to_bits()),
                _ => i128::from(value.to_bits()),
            },
            width,
        },
        _ => operand_to_formula(func, operand),
    }
}

fn float_is_zero_operand(operand: &Operand) -> bool {
    matches!(operand, Operand::Constant(ConstValue::Float(value)) if *value == 0.0)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_func() -> VerifiableFunction {
        VerifiableFunction {
            name: "test".to_string(),
            def_path: "test::test".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Bool, name: Some("ret".into()) },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                    LocalDecl { index: 2, ty: Ty::Bool, name: Some("flag".into()) },
                ],
                blocks: vec![],
                arg_count: 2,
                return_ty: Ty::Bool,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    #[test]
    fn test_guard_switch_int_match_to_formula() {
        let func = test_func();
        let guard =
            GuardCondition::SwitchIntMatch { discr: Operand::Copy(Place::local(1)), value: 42 };
        let formula = guard_to_formula(&func, &guard);
        // tRust #883: Match both Var and SymVar via var_name().
        assert!(
            matches!(&formula, Formula::Eq(lhs, rhs)
                if lhs.var_name() == Some("x")
                && matches!(rhs.as_ref(), Formula::Int(42))
            ),
            "SwitchIntMatch should produce discr == value, got: {formula:?}"
        );
    }

    #[test]
    fn test_guard_switch_int_otherwise_to_formula() {
        let func = test_func();
        let guard = GuardCondition::SwitchIntOtherwise {
            discr: Operand::Copy(Place::local(1)),
            excluded_values: vec![0, 7],
        };
        let formula = guard_to_formula(&func, &guard);
        match &formula {
            Formula::And(clauses) => {
                assert_eq!(clauses.len(), 2);
                assert!(matches!(&clauses[0], Formula::Not(inner)
                    if matches!(inner.as_ref(), Formula::Eq(_, rhs) if matches!(rhs.as_ref(), Formula::Int(0)))
                ));
                assert!(matches!(&clauses[1], Formula::Not(inner)
                    if matches!(inner.as_ref(), Formula::Eq(_, rhs) if matches!(rhs.as_ref(), Formula::Int(7)))
                ));
            }
            other => panic!("expected And, got: {other:?}"),
        }
    }

    #[test]
    fn test_guard_switch_int_otherwise_single_excluded() {
        let func = test_func();
        let guard = GuardCondition::SwitchIntOtherwise {
            discr: Operand::Copy(Place::local(1)),
            excluded_values: vec![5],
        };
        let formula = guard_to_formula(&func, &guard);
        // Single excluded value should produce just Not(Eq(..)), not And([...])
        assert!(matches!(&formula, Formula::Not(_)), "single excluded: {formula:?}");
    }

    #[test]
    fn test_guard_switch_int_otherwise_empty_excluded() {
        let func = test_func();
        let guard = GuardCondition::SwitchIntOtherwise {
            discr: Operand::Copy(Place::local(1)),
            excluded_values: vec![],
        };
        let formula = guard_to_formula(&func, &guard);
        assert_eq!(formula, Formula::Bool(true));
    }

    #[test]
    fn test_guard_assert_holds_expected_true() {
        let func = test_func();
        let guard =
            GuardCondition::AssertHolds { cond: Operand::Copy(Place::local(2)), expected: true };
        let formula = guard_to_formula(&func, &guard);
        // expected=true: cond holds, so formula is just the condition var
        // tRust #883: Formula::var() now creates SymVar; match both Var and SymVar.
        assert!(formula.var_name() == Some("flag"), "expected flag var, got: {formula:?}");
    }

    #[test]
    fn test_guard_assert_holds_expected_false() {
        let func = test_func();
        let guard =
            GuardCondition::AssertHolds { cond: Operand::Copy(Place::local(2)), expected: false };
        let formula = guard_to_formula(&func, &guard);
        // expected=false: assert passes when cond is false, so NOT(cond)
        // tRust #883: Match both Var and SymVar via var_name().
        assert!(
            matches!(&formula, Formula::Not(inner) if inner.var_name() == Some("flag")),
            "expected Not(flag), got: {formula:?}"
        );
    }

    #[test]
    fn test_guard_assert_fails_expected_true() {
        let func = test_func();
        let guard = GuardCondition::AssertFails {
            cond: Operand::Copy(Place::local(2)),
            expected: true,
            msg: AssertMessage::Custom("test".into()),
        };
        let formula = guard_to_formula(&func, &guard);
        // Assert failed: expected true but got false => NOT(cond)
        // tRust #883: Match both Var and SymVar via var_name().
        assert!(
            matches!(&formula, Formula::Not(inner) if inner.var_name() == Some("flag")),
            "expected Not(flag), got: {formula:?}"
        );
    }

    #[test]
    fn test_guards_to_assumption_empty() {
        let func = test_func();
        let assumption = guards_to_assumption(&func, &[]);
        assert_eq!(assumption, Formula::Bool(true));
    }

    #[test]
    fn test_guards_to_assumption_single() {
        let func = test_func();
        let guards = vec![GuardCondition::SwitchIntMatch {
            discr: Operand::Copy(Place::local(1)),
            value: 1,
        }];
        let assumption = guards_to_assumption(&func, &guards);
        // Single guard should not wrap in And
        assert!(matches!(&assumption, Formula::Eq(_, _)), "single guard: {assumption:?}");
    }

    #[test]
    fn test_guards_to_assumption_multiple() {
        let func = test_func();
        let guards = vec![
            GuardCondition::SwitchIntMatch { discr: Operand::Copy(Place::local(1)), value: 1 },
            GuardCondition::AssertHolds { cond: Operand::Copy(Place::local(2)), expected: true },
        ];
        let assumption = guards_to_assumption(&func, &guards);
        match &assumption {
            Formula::And(clauses) => assert_eq!(clauses.len(), 2),
            other => panic!("expected And, got: {other:?}"),
        }
    }

    #[test]
    fn test_guarded_formula_empty_guards() {
        let func = test_func();
        let vc = Formula::Not(Box::new(Formula::Bool(true)));
        let result = guarded_formula(&func, &[], vc.clone());
        assert_eq!(result, vc, "empty guards should return formula unchanged");
    }

    #[test]
    fn test_guarded_formula_with_guards() {
        let func = test_func();
        let guards = vec![GuardCondition::SwitchIntMatch {
            discr: Operand::Copy(Place::local(1)),
            value: 1,
        }];
        let vc = Formula::Not(Box::new(Formula::Bool(true)));
        let result = guarded_formula(&func, &guards, vc);
        // Should be And([guard_assumption, vc_formula])
        assert!(matches!(&result, Formula::And(clauses) if clauses.len() == 2));
    }

    #[test]
    fn test_guard_switch_int_match_u128_above_i128_max() {
        let func = test_func();
        // Value above i128::MAX must not be silently truncated (#373)
        let large_value: u128 = (i128::MAX as u128) + 1;
        let guard = GuardCondition::SwitchIntMatch {
            discr: Operand::Copy(Place::local(1)),
            value: large_value,
        };
        let formula = guard_to_formula(&func, &guard);
        assert!(
            matches!(&formula, Formula::Eq(_, rhs) if matches!(rhs.as_ref(), Formula::UInt(v) if *v == large_value)),
            "u128 value above i128::MAX should use Formula::UInt, got: {formula:?}"
        );
    }

    #[test]
    fn test_guard_switch_int_otherwise_u128_above_i128_max() {
        let func = test_func();
        let large_value: u128 = u128::MAX;
        let guard = GuardCondition::SwitchIntOtherwise {
            discr: Operand::Copy(Place::local(1)),
            excluded_values: vec![large_value],
        };
        let formula = guard_to_formula(&func, &guard);
        // Should produce Not(Eq(discr, UInt(u128::MAX)))
        assert!(
            matches!(&formula, Formula::Not(inner)
                if matches!(inner.as_ref(), Formula::Eq(_, rhs)
                    if matches!(rhs.as_ref(), Formula::UInt(v) if *v == u128::MAX))),
            "u128::MAX excluded value should use Formula::UInt, got: {formula:?}"
        );
    }
}
