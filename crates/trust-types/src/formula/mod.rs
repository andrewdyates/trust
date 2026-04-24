// trust-types/formula: SMT-level formulas
//
// These are the verification conditions sent to solvers. Backend-agnostic —
// trust-router encodes these into z4/sunder/tla2 specific representations.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

pub(crate) mod borrow_encoding;
pub(crate) mod contracts;
pub(crate) mod smtlib;
pub(crate) mod sort;
pub(crate) mod temporal;
#[cfg(test)]
mod tests;
pub(crate) mod vc;
pub(crate) mod vc_kind;

pub use borrow_encoding::*;
pub use contracts::*;
pub use sort::Sort;
pub use temporal::*;
pub use vc::*;
pub use vc_kind::*;

use crate::fx::FxHashSet;
use serde::{Deserialize, Serialize};

/// SMT-level formula (what solvers receive).
///
/// Formulas are backend-agnostic logical expressions that trust-router
/// encodes into solver-specific representations (z4, sunder, tla2).
///
/// # Examples
///
/// ```
/// use trust_types::{Formula, Sort};
///
/// // Boolean literal
/// let f = Formula::Bool(true);
///
/// // Integer variable
/// let x = Formula::Var("x".into(), Sort::Int);
///
/// // Comparison: x > 0
/// let gt = Formula::Gt(Box::new(x.clone()), Box::new(Formula::Int(0)));
///
/// // Conjunction: x > 0 AND x < 10
/// let range = Formula::And(vec![
///     Formula::Gt(Box::new(x.clone()), Box::new(Formula::Int(0))),
///     Formula::Lt(Box::new(x), Box::new(Formula::Int(10))),
/// ]);
///
/// // Implication: a => b
/// let a = Formula::Var("a".into(), Sort::Bool);
/// let b = Formula::Var("b".into(), Sort::Bool);
/// let imp = Formula::Implies(Box::new(a), Box::new(b));
///
/// // Negation
/// let neg = Formula::Not(Box::new(Formula::Bool(false)));
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum Formula {
    // Literals
    Bool(bool),
    Int(i128),
    UInt(u128),
    BitVec { value: i128, width: u32 },

    // Variables
    Var(String, Sort),
    // tRust #717: Interned variable name variant for reduced heap allocation.
    // SymVar(Symbol, Sort) is semantically identical to Var(String, Sort)
    // but uses a Copy, 4-byte Symbol instead of a heap-allocated String.
    SymVar(crate::Symbol, Sort),

    // Boolean connectives
    Not(Box<Formula>),
    And(Vec<Formula>),
    Or(Vec<Formula>),
    Implies(Box<Formula>, Box<Formula>),

    // Comparisons
    Eq(Box<Formula>, Box<Formula>),
    Lt(Box<Formula>, Box<Formula>),
    Le(Box<Formula>, Box<Formula>),
    Gt(Box<Formula>, Box<Formula>),
    Ge(Box<Formula>, Box<Formula>),

    // Integer arithmetic (mathematical integers, unbounded)
    Add(Box<Formula>, Box<Formula>),
    Sub(Box<Formula>, Box<Formula>),
    Mul(Box<Formula>, Box<Formula>),
    Div(Box<Formula>, Box<Formula>),
    Rem(Box<Formula>, Box<Formula>),
    Neg(Box<Formula>),

    // Bitvector arithmetic (fixed-width, machine semantics)
    BvAdd(Box<Formula>, Box<Formula>, u32),
    BvSub(Box<Formula>, Box<Formula>, u32),
    BvMul(Box<Formula>, Box<Formula>, u32),
    BvUDiv(Box<Formula>, Box<Formula>, u32),
    BvSDiv(Box<Formula>, Box<Formula>, u32),
    BvURem(Box<Formula>, Box<Formula>, u32),
    BvSRem(Box<Formula>, Box<Formula>, u32),
    BvAnd(Box<Formula>, Box<Formula>, u32),
    BvOr(Box<Formula>, Box<Formula>, u32),
    BvXor(Box<Formula>, Box<Formula>, u32),
    BvNot(Box<Formula>, u32),
    BvShl(Box<Formula>, Box<Formula>, u32),
    BvLShr(Box<Formula>, Box<Formula>, u32),
    BvAShr(Box<Formula>, Box<Formula>, u32),

    // Bitvector comparisons
    BvULt(Box<Formula>, Box<Formula>, u32),
    BvULe(Box<Formula>, Box<Formula>, u32),
    BvSLt(Box<Formula>, Box<Formula>, u32),
    BvSLe(Box<Formula>, Box<Formula>, u32),

    // Bitvector conversions
    BvToInt(Box<Formula>, u32, bool),
    IntToBv(Box<Formula>, u32),
    BvExtract { inner: Box<Formula>, high: u32, low: u32 },
    BvConcat(Box<Formula>, Box<Formula>),
    BvZeroExt(Box<Formula>, u32),
    BvSignExt(Box<Formula>, u32),

    // Conditional
    Ite(Box<Formula>, Box<Formula>, Box<Formula>),

    // Quantifiers
    // tRust #883: Bindings use interned Symbol instead of heap-allocated String.
    Forall(Vec<(crate::Symbol, Sort)>, Box<Formula>),
    Exists(Vec<(crate::Symbol, Sort)>, Box<Formula>),

    // Arrays
    Select(Box<Formula>, Box<Formula>),
    Store(Box<Formula>, Box<Formula>, Box<Formula>),
}

impl Formula {
    /// Collect references to all direct sub-formulas.
    #[must_use]
    pub fn children(&self) -> Vec<&Formula> {
        match self {
            // Leaves
            Formula::Bool(_)
            | Formula::Int(_)
            | Formula::UInt(_)
            | Formula::BitVec { .. }
            | Formula::Var(..)
            | Formula::SymVar(..) => {
                vec![]
            }

            // Unary
            Formula::Not(a) | Formula::Neg(a) => vec![a],
            Formula::BvNot(a, _)
            | Formula::BvToInt(a, _, _)
            | Formula::IntToBv(a, _)
            | Formula::BvZeroExt(a, _)
            | Formula::BvSignExt(a, _) => vec![a],
            Formula::BvExtract { inner, .. } => vec![inner],

            // N-ary
            Formula::And(terms) | Formula::Or(terms) => terms.iter().collect(),

            // Binary
            Formula::Implies(a, b)
            | Formula::Eq(a, b)
            | Formula::Lt(a, b)
            | Formula::Le(a, b)
            | Formula::Gt(a, b)
            | Formula::Ge(a, b)
            | Formula::Add(a, b)
            | Formula::Sub(a, b)
            | Formula::Mul(a, b)
            | Formula::Div(a, b)
            | Formula::Rem(a, b)
            | Formula::BvConcat(a, b)
            | Formula::Select(a, b) => vec![a, b],

            // Binary with width
            Formula::BvAdd(a, b, _)
            | Formula::BvSub(a, b, _)
            | Formula::BvMul(a, b, _)
            | Formula::BvUDiv(a, b, _)
            | Formula::BvSDiv(a, b, _)
            | Formula::BvURem(a, b, _)
            | Formula::BvSRem(a, b, _)
            | Formula::BvAnd(a, b, _)
            | Formula::BvOr(a, b, _)
            | Formula::BvXor(a, b, _)
            | Formula::BvShl(a, b, _)
            | Formula::BvLShr(a, b, _)
            | Formula::BvAShr(a, b, _)
            | Formula::BvULt(a, b, _)
            | Formula::BvULe(a, b, _)
            | Formula::BvSLt(a, b, _)
            | Formula::BvSLe(a, b, _) => vec![a, b],

            // Ternary
            Formula::Ite(a, b, c) | Formula::Store(a, b, c) => vec![a, b, c],

            // Quantifiers (body only; bindings are not sub-formulas)
            Formula::Forall(_, body) | Formula::Exists(_, body) => vec![body],
        }
    }

    /// Map over all direct sub-formulas, replacing each via `f`.
    /// Non-formula data (widths, sorts, bindings) is preserved.
    #[must_use]
    pub fn map_children(self, f: &mut impl FnMut(Formula) -> Formula) -> Formula {
        match self {
            // Leaves
            Formula::Bool(_)
            | Formula::Int(_)
            | Formula::UInt(_)
            | Formula::BitVec { .. }
            | Formula::Var(..)
            | Formula::SymVar(..) => self,

            // Unary
            Formula::Not(a) => Formula::Not(Box::new(f(*a))),
            Formula::Neg(a) => Formula::Neg(Box::new(f(*a))),
            Formula::BvNot(a, w) => Formula::BvNot(Box::new(f(*a)), w),
            Formula::BvToInt(a, w, s) => Formula::BvToInt(Box::new(f(*a)), w, s),
            Formula::IntToBv(a, w) => Formula::IntToBv(Box::new(f(*a)), w),
            Formula::BvZeroExt(a, bits) => Formula::BvZeroExt(Box::new(f(*a)), bits),
            Formula::BvSignExt(a, bits) => Formula::BvSignExt(Box::new(f(*a)), bits),
            Formula::BvExtract { inner, high, low } => {
                Formula::BvExtract { inner: Box::new(f(*inner)), high, low }
            }

            // N-ary
            Formula::And(terms) => Formula::And(terms.into_iter().map(&mut *f).collect()),
            Formula::Or(terms) => Formula::Or(terms.into_iter().map(&mut *f).collect()),

            // Binary
            Formula::Implies(a, b) => Formula::Implies(Box::new(f(*a)), Box::new(f(*b))),
            Formula::Eq(a, b) => Formula::Eq(Box::new(f(*a)), Box::new(f(*b))),
            Formula::Lt(a, b) => Formula::Lt(Box::new(f(*a)), Box::new(f(*b))),
            Formula::Le(a, b) => Formula::Le(Box::new(f(*a)), Box::new(f(*b))),
            Formula::Gt(a, b) => Formula::Gt(Box::new(f(*a)), Box::new(f(*b))),
            Formula::Ge(a, b) => Formula::Ge(Box::new(f(*a)), Box::new(f(*b))),
            Formula::Add(a, b) => Formula::Add(Box::new(f(*a)), Box::new(f(*b))),
            Formula::Sub(a, b) => Formula::Sub(Box::new(f(*a)), Box::new(f(*b))),
            Formula::Mul(a, b) => Formula::Mul(Box::new(f(*a)), Box::new(f(*b))),
            Formula::Div(a, b) => Formula::Div(Box::new(f(*a)), Box::new(f(*b))),
            Formula::Rem(a, b) => Formula::Rem(Box::new(f(*a)), Box::new(f(*b))),
            Formula::BvConcat(a, b) => Formula::BvConcat(Box::new(f(*a)), Box::new(f(*b))),
            Formula::Select(a, b) => Formula::Select(Box::new(f(*a)), Box::new(f(*b))),

            // Binary with width
            Formula::BvAdd(a, b, w) => Formula::BvAdd(Box::new(f(*a)), Box::new(f(*b)), w),
            Formula::BvSub(a, b, w) => Formula::BvSub(Box::new(f(*a)), Box::new(f(*b)), w),
            Formula::BvMul(a, b, w) => Formula::BvMul(Box::new(f(*a)), Box::new(f(*b)), w),
            Formula::BvUDiv(a, b, w) => Formula::BvUDiv(Box::new(f(*a)), Box::new(f(*b)), w),
            Formula::BvSDiv(a, b, w) => Formula::BvSDiv(Box::new(f(*a)), Box::new(f(*b)), w),
            Formula::BvURem(a, b, w) => Formula::BvURem(Box::new(f(*a)), Box::new(f(*b)), w),
            Formula::BvSRem(a, b, w) => Formula::BvSRem(Box::new(f(*a)), Box::new(f(*b)), w),
            Formula::BvAnd(a, b, w) => Formula::BvAnd(Box::new(f(*a)), Box::new(f(*b)), w),
            Formula::BvOr(a, b, w) => Formula::BvOr(Box::new(f(*a)), Box::new(f(*b)), w),
            Formula::BvXor(a, b, w) => Formula::BvXor(Box::new(f(*a)), Box::new(f(*b)), w),
            Formula::BvShl(a, b, w) => Formula::BvShl(Box::new(f(*a)), Box::new(f(*b)), w),
            Formula::BvLShr(a, b, w) => Formula::BvLShr(Box::new(f(*a)), Box::new(f(*b)), w),
            Formula::BvAShr(a, b, w) => Formula::BvAShr(Box::new(f(*a)), Box::new(f(*b)), w),
            Formula::BvULt(a, b, w) => Formula::BvULt(Box::new(f(*a)), Box::new(f(*b)), w),
            Formula::BvULe(a, b, w) => Formula::BvULe(Box::new(f(*a)), Box::new(f(*b)), w),
            Formula::BvSLt(a, b, w) => Formula::BvSLt(Box::new(f(*a)), Box::new(f(*b)), w),
            Formula::BvSLe(a, b, w) => Formula::BvSLe(Box::new(f(*a)), Box::new(f(*b)), w),

            // Ternary
            Formula::Ite(a, b, c) => {
                Formula::Ite(Box::new(f(*a)), Box::new(f(*b)), Box::new(f(*c)))
            }
            Formula::Store(a, b, c) => {
                Formula::Store(Box::new(f(*a)), Box::new(f(*b)), Box::new(f(*c)))
            }

            // Quantifiers
            Formula::Forall(bindings, body) => Formula::Forall(bindings, Box::new(f(*body))),
            Formula::Exists(bindings, body) => Formula::Exists(bindings, Box::new(f(*body))),
        }
    }

    /// Recursively visit all sub-formulas depth-first (pre-order).
    pub fn visit(&self, f: &mut impl FnMut(&Formula)) {
        f(self);
        for child in self.children() {
            child.visit(f);
        }
    }

    /// Recursively map all sub-formulas bottom-up (post-order).
    /// Children are transformed first, then `f` is applied to the result.
    #[must_use]
    pub fn map(self, f: &mut impl FnMut(Formula) -> Formula) -> Formula {
        let mapped = self.map_children(&mut |child| child.map(f));
        f(mapped)
    }

    /// Collect all free variable names in this formula.
    /// Variables bound by Forall/Exists are excluded.
    #[must_use]
    pub fn free_variables(&self) -> FxHashSet<String> {
        let mut free = FxHashSet::default();
        self.free_variables_inner(&mut free, &FxHashSet::default());
        free
    }

    fn free_variables_inner(&self, free: &mut FxHashSet<String>, bound: &FxHashSet<String>) {
        match self {
            Formula::Var(name, _) => {
                if !bound.contains(name) {
                    free.insert(name.clone());
                }
            }
            // tRust #717: SymVar uses Symbol; resolve to string for free variable tracking.
            Formula::SymVar(sym, _) => {
                let name = sym.as_str().to_string();
                if !bound.contains(&name) {
                    free.insert(name);
                }
            }
            // tRust #883: Quantifier bindings use Symbol; convert to String for tracking.
            Formula::Forall(bindings, body) | Formula::Exists(bindings, body) => {
                let mut new_bound = bound.clone();
                for (sym, _) in bindings {
                    new_bound.insert(sym.as_str().to_string());
                }
                body.free_variables_inner(free, &new_bound);
            }
            _ => {
                for child in self.children() {
                    child.free_variables_inner(free, bound);
                }
            }
        }
    }

    /// Check if this formula contains bitvector operations or types.
    #[must_use]
    pub fn has_bitvectors(&self) -> bool {
        let mut found = false;
        self.visit(&mut |f| {
            if found {
                return;
            }
            match f {
                Formula::BitVec { .. }
                | Formula::BvAdd(..)
                | Formula::BvSub(..)
                | Formula::BvMul(..)
                | Formula::BvUDiv(..)
                | Formula::BvSDiv(..)
                | Formula::BvURem(..)
                | Formula::BvSRem(..)
                | Formula::BvAnd(..)
                | Formula::BvOr(..)
                | Formula::BvXor(..)
                | Formula::BvNot(..)
                | Formula::BvShl(..)
                | Formula::BvLShr(..)
                | Formula::BvAShr(..)
                | Formula::BvULt(..)
                | Formula::BvULe(..)
                | Formula::BvSLt(..)
                | Formula::BvSLe(..)
                | Formula::BvToInt(..)
                | Formula::IntToBv(..)
                | Formula::BvExtract { .. }
                | Formula::BvConcat(..)
                | Formula::BvZeroExt(..)
                | Formula::BvSignExt(..) => found = true,
                Formula::Var(_, Sort::BitVec(_)) | Formula::SymVar(_, Sort::BitVec(_)) => {
                    found = true;
                }
                _ => {}
            }
        });
        found
    }

    /// Check if this formula contains array theory operations (Select/Store)
    /// or array-typed variables.
    ///
    /// tRust #652: Cheap structural check for sunder translatability.
    #[must_use]
    pub fn has_arrays(&self) -> bool {
        let mut found = false;
        self.visit(&mut |f| {
            if found {
                return;
            }
            match f {
                Formula::Select(..) | Formula::Store(..) => found = true,
                Formula::Var(_, Sort::Array(_, _)) | Formula::SymVar(_, Sort::Array(_, _)) => {
                    found = true;
                }
                _ => {}
            }
        });
        found
    }

    /// Check if this formula contains integer literals outside the i64 range.
    ///
    /// tRust #652: sunder-core uses i64 for integer literals. Formulas with
    /// Int/UInt values that exceed i64 range cannot be translated to PureExpr.
    #[must_use]
    pub fn has_large_integers(&self) -> bool {
        let mut found = false;
        self.visit(&mut |f| {
            if found {
                return;
            }
            match f {
                Formula::Int(n) if i64::try_from(*n).is_err() => {
                    found = true;
                }
                Formula::UInt(n) if i64::try_from(*n).is_err() => {
                    found = true;
                }
                _ => {}
            }
        });
        found
    }

    // tRust #883: Convenience constructors that produce SymVar (interned) instead
    // of Var (heap-allocated String). New code should prefer these over raw
    // Formula::Var(...) to reduce per-variable heap allocations.

    /// Create a variable formula using an interned symbol.
    ///
    /// Create a variable formula from a string name.
    ///
    /// Equivalent to `Formula::Var(name.to_string(), sort)`.
    /// For interned variables, use `var_sym()` with a `Symbol`.
    #[must_use]
    pub fn var(name: &str, sort: Sort) -> Formula {
        Formula::Var(name.to_string(), sort)
    }

    /// Create a variable formula from an owned String.
    ///
    /// Takes ownership of the String to avoid an extra clone when the caller
    /// already has an owned String (e.g. from `format!`).
    #[must_use]
    pub fn var_owned(name: String, sort: Sort) -> Formula {
        Formula::Var(name, sort)
    }

    /// Create a variable formula from an already-interned Symbol.
    #[must_use]
    pub fn var_sym(sym: crate::Symbol, sort: Sort) -> Formula {
        Formula::SymVar(sym, sort)
    }

    /// Return the variable name if this formula is a variable (Var or SymVar).
    ///
    /// Returns `None` for non-variable formulas. The returned `&str` has
    /// `'static` lifetime for SymVar (interned) and borrows `self` for Var.
    #[must_use]
    pub fn var_name(&self) -> Option<&str> {
        match self {
            Formula::Var(name, _) => Some(name.as_str()),
            Formula::SymVar(sym, _) => Some(sym.as_str()),
            _ => None,
        }
    }

    /// Return the sort if this formula is a variable (Var or SymVar).
    #[must_use]
    pub fn var_sort(&self) -> Option<&Sort> {
        match self {
            Formula::Var(_, sort) | Formula::SymVar(_, sort) => Some(sort),
            _ => None,
        }
    }

    // tRust #883: Convenience constructors for quantifiers with interned bindings.

    /// Create a universally quantified formula with interned bindings.
    ///
    /// Accepts `&str` binding names and interns them automatically.
    #[must_use]
    pub fn forall(bindings: &[(&str, Sort)], body: Formula) -> Formula {
        let sym_bindings: Vec<(crate::Symbol, Sort)> = bindings
            .iter()
            .map(|(name, sort)| (crate::Symbol::intern(name), sort.clone()))
            .collect();
        Formula::Forall(sym_bindings, Box::new(body))
    }

    /// Create an existentially quantified formula with interned bindings.
    ///
    /// Accepts `&str` binding names and interns them automatically.
    #[must_use]
    pub fn exists(bindings: &[(&str, Sort)], body: Formula) -> Formula {
        let sym_bindings: Vec<(crate::Symbol, Sort)> = bindings
            .iter()
            .map(|(name, sort)| (crate::Symbol::intern(name), sort.clone()))
            .collect();
        Formula::Exists(sym_bindings, Box::new(body))
    }

    /// Rename a variable throughout the formula.
    #[must_use]
    pub fn rename_var(&self, from: &str, to: &str) -> Formula {
        match self {
            Formula::Var(name, sort) if name == from => Formula::Var(to.to_string(), sort.clone()),
            // tRust #717: SymVar rename resolves symbol, produces new SymVar.
            Formula::SymVar(sym, sort) if sym.as_str() == from => {
                Formula::SymVar(crate::Symbol::intern(to), sort.clone())
            }
            _ => self.clone().map_children(&mut |child| child.rename_var(from, to)),
        }
    }
}

/// Proof level tier, used by the router to select appropriate backends.
///
/// # Examples
///
/// ```
/// use trust_types::ProofLevel;
///
/// // Proof levels are ordered: L0 < L1 < L2
/// assert!(ProofLevel::L0Safety < ProofLevel::L1Functional);
/// assert!(ProofLevel::L1Functional < ProofLevel::L2Domain);
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ProofLevel {
    /// L0: Safety — no panics, no UB (overflow, bounds, div-by-zero).
    L0Safety,
    /// L1: Functional — postconditions hold, contracts satisfied.
    L1Functional,
    /// L2: Domain — temporal properties, distributed protocol correctness.
    L2Domain,
}
