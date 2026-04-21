// trust-types/formula_arena/types.rs: Core types for arena-allocated formulas
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::formula::Sort;

/// Index into a `FormulaArena`. Copy-cheap (4 bytes) alternative to `Box<Formula>`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FormulaRef(pub(crate) u32);

impl FormulaRef {
    /// The raw index into the arena's node vector.
    #[must_use]
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

/// A formula node stored in a `FormulaArena`. Mirrors `Formula` but uses
/// `FormulaRef` indices instead of `Box<Formula>`.
///
/// N-ary nodes (`And`, `Or`) store a start index and count into a separate
/// `refs` vector to avoid per-node Vec allocations.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum FormulaNode {
    // Literals
    Bool(bool),
    Int(i128),
    UInt(u128),
    BitVec {
        value: i128,
        width: u32,
    },

    // Variables
    Var(String, Sort),

    // Boolean connectives
    Not(FormulaRef),
    /// N-ary And: (start_index_in_refs_vec, count).
    And(u32, u32),
    /// N-ary Or: (start_index_in_refs_vec, count).
    Or(u32, u32),
    Implies(FormulaRef, FormulaRef),

    // Comparisons
    Eq(FormulaRef, FormulaRef),
    Lt(FormulaRef, FormulaRef),
    Le(FormulaRef, FormulaRef),
    Gt(FormulaRef, FormulaRef),
    Ge(FormulaRef, FormulaRef),

    // Integer arithmetic
    Add(FormulaRef, FormulaRef),
    Sub(FormulaRef, FormulaRef),
    Mul(FormulaRef, FormulaRef),
    Div(FormulaRef, FormulaRef),
    Rem(FormulaRef, FormulaRef),
    Neg(FormulaRef),

    // Bitvector arithmetic
    BvAdd(FormulaRef, FormulaRef, u32),
    BvSub(FormulaRef, FormulaRef, u32),
    BvMul(FormulaRef, FormulaRef, u32),
    BvUDiv(FormulaRef, FormulaRef, u32),
    BvSDiv(FormulaRef, FormulaRef, u32),
    BvURem(FormulaRef, FormulaRef, u32),
    BvSRem(FormulaRef, FormulaRef, u32),
    BvAnd(FormulaRef, FormulaRef, u32),
    BvOr(FormulaRef, FormulaRef, u32),
    BvXor(FormulaRef, FormulaRef, u32),
    BvNot(FormulaRef, u32),
    BvShl(FormulaRef, FormulaRef, u32),
    BvLShr(FormulaRef, FormulaRef, u32),
    BvAShr(FormulaRef, FormulaRef, u32),

    // Bitvector comparisons
    BvULt(FormulaRef, FormulaRef, u32),
    BvULe(FormulaRef, FormulaRef, u32),
    BvSLt(FormulaRef, FormulaRef, u32),
    BvSLe(FormulaRef, FormulaRef, u32),

    // Bitvector conversions
    BvToInt(FormulaRef, u32, bool),
    IntToBv(FormulaRef, u32),
    BvExtract {
        inner: FormulaRef,
        high: u32,
        low: u32,
    },
    BvConcat(FormulaRef, FormulaRef),
    BvZeroExt(FormulaRef, u32),
    BvSignExt(FormulaRef, u32),

    // Conditional
    Ite(FormulaRef, FormulaRef, FormulaRef),

    // Quantifiers: bindings stored inline, body is a FormulaRef.
    Forall(Vec<(String, Sort)>, FormulaRef),
    Exists(Vec<(String, Sort)>, FormulaRef),

    // Arrays
    Select(FormulaRef, FormulaRef),
    Store(FormulaRef, FormulaRef, FormulaRef),
}
