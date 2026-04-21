// trust-types/formula/sort: SMT sorts for formula variables
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};

use crate::model::Ty;

/// SMT sorts.
///
/// Each formula variable carries a sort indicating its type in the SMT domain.
///
/// # Examples
///
/// ```
/// use trust_types::Sort;
///
/// let int_sort = Sort::Int;
/// let bv32 = Sort::BitVec(32);
/// let arr = Sort::Array(Box::new(Sort::Int), Box::new(Sort::BitVec(8)));
///
/// assert_eq!(int_sort.to_smtlib(), "Int");
/// assert_eq!(bv32.to_smtlib(), "(_ BitVec 32)");
/// assert_eq!(arr.to_smtlib(), "(Array Int (_ BitVec 8))");
/// ```
// tRust: added PartialOrd, Ord, Hash for BTreeSet usage in smtlib_backend
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum Sort {
    Bool,
    Int,
    BitVec(u32),
    Array(Box<Sort>, Box<Sort>),
}

impl Sort {
    /// Convert a trust-types Ty to an SMT sort.
    pub fn from_ty(ty: &Ty) -> Self {
        match ty {
            Ty::Bool => Sort::Bool,
            Ty::Int { width, .. } => Sort::BitVec(*width),
            Ty::Float { .. } => Sort::BitVec(64), // approximate floats as bitvecs
            // tRust #432: Raw pointers map to Sort::Int (same as Ref, pointers are
            // mathematical integers at the SMT level).
            Ty::RawPtr { .. } => Sort::Int,
            _ => Sort::Int, // fallback
        }
    }

    /// Convert this Sort to its SMT-LIB2 text representation.
    #[must_use]
    pub fn to_smtlib(&self) -> String {
        match self {
            Sort::Bool => "Bool".to_string(),
            Sort::Int => "Int".to_string(),
            Sort::BitVec(w) => format!("(_ BitVec {w})"),
            Sort::Array(idx, elem) => {
                format!("(Array {} {})", idx.to_smtlib(), elem.to_smtlib())
            }
        }
    }
}
