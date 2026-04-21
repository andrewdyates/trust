// trust-cegar: IC3 formula priming (variable renaming for next-state)
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{Formula, Sort};

use crate::error::CegarError;

/// Prime a formula: rename all variables by appending a prime suffix.
/// This is used for next-state variables in transition relations.
///
/// Every known `Formula` variant is handled explicitly. Because `Formula` is
/// `#[non_exhaustive]`, the fallback arm returns an error instead of silently
/// producing an unprimed formula when a new variant is added.
/// Fixes #772: the previous catch-all `_ => formula.clone()` silently
/// returned unprimed formulas for BV ops, arrays, quantifiers, etc.,
/// which broke IC3 transition relations.
pub(crate) fn prime_formula(formula: &Formula) -> Result<Formula, CegarError> {
    Ok(match formula {
        // -- Leaves (no variables to prime) --
        Formula::Bool(_) | Formula::Int(_) | Formula::UInt(_) | Formula::BitVec { .. } => {
            formula.clone()
        }

        // -- Variables: prime the name --
        Formula::Var(name, sort) => Formula::Var(format!("{name}'"), sort.clone()),
        Formula::SymVar(sym, sort) => {
            // SymVar uses interned symbols; fall back to String form for priming.
            Formula::Var(format!("{sym}'"), sort.clone())
        }

        // -- Boolean connectives --
        Formula::Not(inner) => Formula::Not(Box::new(prime_formula(inner)?)),
        Formula::And(children) => {
            Formula::And(children.iter().map(prime_formula).collect::<Result<Vec<_>, _>>()?)
        }
        Formula::Or(children) => {
            Formula::Or(children.iter().map(prime_formula).collect::<Result<Vec<_>, _>>()?)
        }
        Formula::Implies(a, b) => {
            Formula::Implies(Box::new(prime_formula(a)?), Box::new(prime_formula(b)?))
        }

        // -- Comparisons --
        Formula::Eq(a, b) => Formula::Eq(Box::new(prime_formula(a)?), Box::new(prime_formula(b)?)),
        Formula::Lt(a, b) => Formula::Lt(Box::new(prime_formula(a)?), Box::new(prime_formula(b)?)),
        Formula::Le(a, b) => Formula::Le(Box::new(prime_formula(a)?), Box::new(prime_formula(b)?)),
        Formula::Gt(a, b) => Formula::Gt(Box::new(prime_formula(a)?), Box::new(prime_formula(b)?)),
        Formula::Ge(a, b) => Formula::Ge(Box::new(prime_formula(a)?), Box::new(prime_formula(b)?)),

        // -- Integer arithmetic --
        Formula::Add(a, b) => {
            Formula::Add(Box::new(prime_formula(a)?), Box::new(prime_formula(b)?))
        }
        Formula::Sub(a, b) => {
            Formula::Sub(Box::new(prime_formula(a)?), Box::new(prime_formula(b)?))
        }
        Formula::Mul(a, b) => {
            Formula::Mul(Box::new(prime_formula(a)?), Box::new(prime_formula(b)?))
        }
        Formula::Div(a, b) => {
            Formula::Div(Box::new(prime_formula(a)?), Box::new(prime_formula(b)?))
        }
        Formula::Rem(a, b) => {
            Formula::Rem(Box::new(prime_formula(a)?), Box::new(prime_formula(b)?))
        }
        Formula::Neg(a) => Formula::Neg(Box::new(prime_formula(a)?)),

        // -- Bitvector arithmetic --
        Formula::BvAdd(a, b, w) => {
            Formula::BvAdd(Box::new(prime_formula(a)?), Box::new(prime_formula(b)?), *w)
        }
        Formula::BvSub(a, b, w) => {
            Formula::BvSub(Box::new(prime_formula(a)?), Box::new(prime_formula(b)?), *w)
        }
        Formula::BvMul(a, b, w) => {
            Formula::BvMul(Box::new(prime_formula(a)?), Box::new(prime_formula(b)?), *w)
        }
        Formula::BvUDiv(a, b, w) => {
            Formula::BvUDiv(Box::new(prime_formula(a)?), Box::new(prime_formula(b)?), *w)
        }
        Formula::BvSDiv(a, b, w) => {
            Formula::BvSDiv(Box::new(prime_formula(a)?), Box::new(prime_formula(b)?), *w)
        }
        Formula::BvURem(a, b, w) => {
            Formula::BvURem(Box::new(prime_formula(a)?), Box::new(prime_formula(b)?), *w)
        }
        Formula::BvSRem(a, b, w) => {
            Formula::BvSRem(Box::new(prime_formula(a)?), Box::new(prime_formula(b)?), *w)
        }
        Formula::BvAnd(a, b, w) => {
            Formula::BvAnd(Box::new(prime_formula(a)?), Box::new(prime_formula(b)?), *w)
        }
        Formula::BvOr(a, b, w) => {
            Formula::BvOr(Box::new(prime_formula(a)?), Box::new(prime_formula(b)?), *w)
        }
        Formula::BvXor(a, b, w) => {
            Formula::BvXor(Box::new(prime_formula(a)?), Box::new(prime_formula(b)?), *w)
        }
        Formula::BvNot(a, w) => Formula::BvNot(Box::new(prime_formula(a)?), *w),
        Formula::BvShl(a, b, w) => {
            Formula::BvShl(Box::new(prime_formula(a)?), Box::new(prime_formula(b)?), *w)
        }
        Formula::BvLShr(a, b, w) => {
            Formula::BvLShr(Box::new(prime_formula(a)?), Box::new(prime_formula(b)?), *w)
        }
        Formula::BvAShr(a, b, w) => {
            Formula::BvAShr(Box::new(prime_formula(a)?), Box::new(prime_formula(b)?), *w)
        }

        // -- Bitvector comparisons --
        Formula::BvULt(a, b, w) => {
            Formula::BvULt(Box::new(prime_formula(a)?), Box::new(prime_formula(b)?), *w)
        }
        Formula::BvULe(a, b, w) => {
            Formula::BvULe(Box::new(prime_formula(a)?), Box::new(prime_formula(b)?), *w)
        }
        Formula::BvSLt(a, b, w) => {
            Formula::BvSLt(Box::new(prime_formula(a)?), Box::new(prime_formula(b)?), *w)
        }
        Formula::BvSLe(a, b, w) => {
            Formula::BvSLe(Box::new(prime_formula(a)?), Box::new(prime_formula(b)?), *w)
        }

        // -- Bitvector conversions --
        Formula::BvToInt(a, w, signed) => {
            Formula::BvToInt(Box::new(prime_formula(a)?), *w, *signed)
        }
        Formula::IntToBv(a, w) => Formula::IntToBv(Box::new(prime_formula(a)?), *w),
        Formula::BvExtract { inner, high, low } => {
            Formula::BvExtract { inner: Box::new(prime_formula(inner)?), high: *high, low: *low }
        }
        Formula::BvConcat(a, b) => {
            Formula::BvConcat(Box::new(prime_formula(a)?), Box::new(prime_formula(b)?))
        }
        Formula::BvZeroExt(a, bits) => Formula::BvZeroExt(Box::new(prime_formula(a)?), *bits),
        Formula::BvSignExt(a, bits) => Formula::BvSignExt(Box::new(prime_formula(a)?), *bits),

        // -- Conditional --
        Formula::Ite(cond, then_f, else_f) => Formula::Ite(
            Box::new(prime_formula(cond)?),
            Box::new(prime_formula(then_f)?),
            Box::new(prime_formula(else_f)?),
        ),

        // -- Quantifiers: prime both bound variables and the body --
        Formula::Forall(bindings, body) => {
            let primed_bindings: Vec<(String, Sort)> =
                bindings.iter().map(|(name, sort)| (format!("{name}'"), sort.clone())).collect();
            Formula::Forall(primed_bindings, Box::new(prime_formula(body)?))
        }
        Formula::Exists(bindings, body) => {
            let primed_bindings: Vec<(String, Sort)> =
                bindings.iter().map(|(name, sort)| (format!("{name}'"), sort.clone())).collect();
            Formula::Exists(primed_bindings, Box::new(prime_formula(body)?))
        }

        // -- Arrays --
        Formula::Select(arr, idx) => {
            Formula::Select(Box::new(prime_formula(arr)?), Box::new(prime_formula(idx)?))
        }
        Formula::Store(arr, idx, val) => Formula::Store(
            Box::new(prime_formula(arr)?),
            Box::new(prime_formula(idx)?),
            Box::new(prime_formula(val)?),
        ),

        // `#[non_exhaustive]` requires a catch-all. If a new `Formula` variant
        // is added, surface a typed error instead of panicking or silently
        // returning an unprimed formula.
        other => return Err(CegarError::UnhandledFormulaVariant { variant: format!("{other:?}") }),
    })
}
