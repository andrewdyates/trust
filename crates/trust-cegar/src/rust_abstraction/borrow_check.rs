// trust-cegar: Borrow-check predicates encoding Rust's aliasing rules
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};

use crate::predicate::Predicate;

use super::ownership::{OwnershipAbstraction, OwnershipState};

/// A predicate that encodes Rust's borrow checking / aliasing rules.
///
/// These predicates capture the "aliasing XOR mutability" invariant:
/// - Multiple `&T` (shared references) can coexist
/// - At most one `&mut T` (mutable reference) can exist
/// - `&T` and `&mut T` cannot coexist for the same referent
///
/// These predicates are used during CEGAR refinement to:
/// 1. Prune counterexample paths that violate aliasing rules
/// 2. Generate conflict predicates when an abstract CEX shows illegal aliasing
/// 3. Seed the predicate set with Rust-guaranteed invariants
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum BorrowCheckPredicate {
    /// No mutable borrow exists for the given referent while shared borrows
    /// are active.
    NoMutWhileShared {
        /// The place (variable/path) that is borrowed.
        place: String,
    },

    /// Exclusive mutable access: when a mutable borrow is active, no other
    /// borrows (shared or mutable) exist.
    ExclusiveMut {
        /// The place that has an exclusive mutable borrow.
        place: String,
    },

    /// The borrow on `referent` held by `borrow_var` is still active (not
    /// yet returned). Used to track which borrows are live at a program point.
    BorrowActive {
        /// The variable holding the borrow (the reference).
        borrow_var: String,
        /// The place being borrowed (the referent).
        referent: String,
    },

    /// Two variables do not alias (point to different memory locations).
    NoAlias {
        /// First variable.
        var_a: String,
        /// Second variable.
        var_b: String,
    },

    /// A shared borrow count predicate: the number of active shared borrows
    /// of `place` is within `[0, max_shared]`.
    SharedBorrowCount {
        /// The place being shared-borrowed.
        place: String,
        /// Maximum number of concurrent shared borrows observed.
        max_shared: usize,
    },
}

impl BorrowCheckPredicate {
    /// Convert to a CEGAR `Predicate` for the predicate abstraction framework.
    #[must_use]
    pub fn to_predicate(&self) -> Predicate {
        match self {
            Self::NoMutWhileShared { place } => {
                Predicate::Custom(format!("{place}:no_mut_while_shared"))
            }
            Self::ExclusiveMut { place } => {
                Predicate::Custom(format!("{place}:exclusive_mut"))
            }
            Self::BorrowActive { borrow_var, referent } => {
                Predicate::Custom(format!("{borrow_var}:borrows:{referent}"))
            }
            Self::NoAlias { var_a, var_b } => {
                let (first, second) = if var_a <= var_b {
                    (var_a.as_str(), var_b.as_str())
                } else {
                    (var_b.as_str(), var_a.as_str())
                };
                Predicate::Custom(format!("{first}:no_alias:{second}"))
            }
            Self::SharedBorrowCount { place, max_shared } => {
                Predicate::Custom(format!("{place}:shared_borrow_count:<={max_shared}"))
            }
        }
    }

    /// Check if a counterexample violates this borrow-check predicate.
    #[must_use]
    pub fn is_violated(&self, ownership: &OwnershipAbstraction) -> bool {
        match self {
            Self::NoMutWhileShared { place } => {
                ownership.is_mutably_borrowed(place)
                    && ownership.states.values().any(|s| *s == OwnershipState::SharedBorrow)
            }
            Self::ExclusiveMut { place } => {
                if !ownership.is_mutably_borrowed(place) {
                    return false;
                }
                let borrow_count = ownership.states.values()
                    .filter(|s| {
                        **s == OwnershipState::SharedBorrow
                            || **s == OwnershipState::MutableBorrow
                    })
                    .count();
                borrow_count > 1
            }
            Self::BorrowActive { borrow_var, .. } => {
                ownership.is_moved(borrow_var)
            }
            Self::NoAlias { var_a, var_b } => {
                let _ = (var_a, var_b);
                false
            }
            Self::SharedBorrowCount { .. } => {
                false
            }
        }
    }
}

impl std::fmt::Display for BorrowCheckPredicate {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NoMutWhileShared { place } => {
                write!(f, "no_mut_while_shared({place})")
            }
            Self::ExclusiveMut { place } => {
                write!(f, "exclusive_mut({place})")
            }
            Self::BorrowActive { borrow_var, referent } => {
                write!(f, "borrow_active({borrow_var} -> {referent})")
            }
            Self::NoAlias { var_a, var_b } => {
                write!(f, "no_alias({var_a}, {var_b})")
            }
            Self::SharedBorrowCount { place, max_shared } => {
                write!(f, "shared_borrow_count({place}) <= {max_shared}")
            }
        }
    }
}
