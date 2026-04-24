// trust-cegar: Ownership predicates and abstraction for Rust CEGAR
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

use crate::predicate::Predicate;

// ---------------------------------------------------------------------------
// OwnershipPredicate: encodes ownership/borrowing semantics as predicates
// ---------------------------------------------------------------------------

/// A predicate that encodes Rust ownership and borrowing semantics.
///
/// These predicates are first-class in the CEGAR loop: they participate in
/// abstraction refinement and can rule out infeasible counterexample paths
/// that violate Rust's ownership discipline.
///
/// Unlike generic predicates (e.g., `x >= 0`), ownership predicates encode
/// type-system invariants that always hold in safe Rust. They are:
/// - Seed predicates (added at the start, not discovered through refinement)
/// - Invariant under widening (never dropped by abstraction widening)
/// - Used to prune spurious counterexamples without solver invocation
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum OwnershipPredicate {
    /// The variable is the unique owner of its value.
    /// In safe Rust, only one owner exists at a time.
    IsOwned(String),

    /// The variable holds a shared reference (`&T`).
    /// Implies: the referent is alive, no mutable borrows exist.
    IsSharedRef(String),

    /// The variable holds a mutable reference (`&mut T`).
    /// Implies: the referent is alive, no other borrows (shared or mutable) exist.
    IsMutRef(String),

    /// The variable has been moved and is no longer accessible.
    /// Any path that uses a moved variable is infeasible in safe Rust.
    IsMoved(String),

    /// The value at `var` has been dropped (destructor ran).
    /// Use-after-drop is infeasible.
    IsDropped(String),
}

impl OwnershipPredicate {
    /// Get the variable name this predicate constrains.
    #[must_use]
    pub fn variable(&self) -> &str {
        match self {
            Self::IsOwned(v)
            | Self::IsSharedRef(v)
            | Self::IsMutRef(v)
            | Self::IsMoved(v)
            | Self::IsDropped(v) => v,
        }
    }

    /// Check if this predicate conflicts with another on the same variable.
    ///
    /// Ownership states are mutually exclusive: a variable cannot be both
    /// owned and moved, both shared-ref and mut-ref, etc.
    #[must_use]
    pub fn conflicts_with(&self, other: &Self) -> bool {
        if self.variable() != other.variable() {
            return false;
        }
        // Same variable, different states => conflict
        // (same state is not a conflict, it's redundant)
        std::mem::discriminant(self) != std::mem::discriminant(other)
    }

    /// Convert to a CEGAR `Predicate` for integration with the predicate
    /// abstraction framework.
    #[must_use]
    pub fn to_predicate(&self) -> Predicate {
        match self {
            Self::IsOwned(v) => Predicate::Custom(format!("{v}:ownership:owned")),
            Self::IsSharedRef(v) => Predicate::Custom(format!("{v}:ownership:shared_ref")),
            Self::IsMutRef(v) => Predicate::Custom(format!("{v}:ownership:mut_ref")),
            Self::IsMoved(v) => Predicate::Custom(format!("{v}:moved")),
            Self::IsDropped(v) => Predicate::Custom(format!("{v}:ownership:dropped")),
        }
    }

    /// Check if this predicate makes a variable access infeasible.
    ///
    /// In safe Rust, accessing a moved or dropped variable is impossible.
    #[must_use]
    pub fn blocks_access(&self) -> bool {
        matches!(self, Self::IsMoved(_) | Self::IsDropped(_))
    }
}

impl std::fmt::Display for OwnershipPredicate {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::IsOwned(v) => write!(f, "{v}: owned"),
            Self::IsSharedRef(v) => write!(f, "{v}: &T"),
            Self::IsMutRef(v) => write!(f, "{v}: &mut T"),
            Self::IsMoved(v) => write!(f, "{v}: moved"),
            Self::IsDropped(v) => write!(f, "{v}: dropped"),
        }
    }
}

// ---------------------------------------------------------------------------
// Ownership abstraction
// ---------------------------------------------------------------------------

/// Ownership state of a variable in the abstract domain.
///
/// Models Rust's ownership discipline: each place is either owned, immutably
/// borrowed (shared), mutably borrowed (exclusive), or moved (dead).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum OwnershipState {
    /// The variable owns its value. Can be moved, borrowed, or dropped.
    Owned,
    /// The variable is immutably borrowed (`&T`). Multiple readers, no writers.
    SharedBorrow,
    /// The variable is mutably borrowed (`&mut T`). Exclusive access.
    MutableBorrow,
    /// The variable has been moved. Any use is a compile error in safe Rust,
    /// so paths reaching a use-after-move are infeasible.
    Moved,
}

impl std::fmt::Display for OwnershipState {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Owned => write!(f, "owned"),
            Self::SharedBorrow => write!(f, "&"),
            Self::MutableBorrow => write!(f, "&mut"),
            Self::Moved => write!(f, "moved"),
        }
    }
}

/// Tracks ownership state for each variable in scope.
///
/// Used to prune infeasible paths (e.g., a path that reads a moved variable)
/// and to generate ownership-aware predicates during refinement.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct OwnershipAbstraction {
    /// Per-variable ownership state.
    pub(in crate::rust_abstraction) states: BTreeMap<String, OwnershipState>,
}

impl OwnershipAbstraction {
    /// Create an empty ownership abstraction.
    #[must_use]
    pub fn new() -> Self {
        Self { states: BTreeMap::new() }
    }

    /// Set the ownership state for a variable.
    pub fn set_state(&mut self, var: impl Into<String>, state: OwnershipState) {
        self.states.insert(var.into(), state);
    }

    /// Get the ownership state for a variable.
    #[must_use]
    pub fn get_state(&self, var: &str) -> Option<OwnershipState> {
        self.states.get(var).copied()
    }

    /// Check if a variable is in a moved state (use-after-move is infeasible).
    #[must_use]
    pub fn is_moved(&self, var: &str) -> bool {
        self.states.get(var) == Some(&OwnershipState::Moved)
    }

    /// Check if a variable has an active mutable borrow.
    #[must_use]
    pub fn is_mutably_borrowed(&self, var: &str) -> bool {
        self.states.get(var) == Some(&OwnershipState::MutableBorrow)
    }

    /// Get all variables that are in a moved state.
    #[must_use]
    pub fn moved_variables(&self) -> Vec<&str> {
        self.states
            .iter()
            .filter(|(_, s)| **s == OwnershipState::Moved)
            .map(|(name, _)| name.as_str())
            .collect()
    }

    /// Number of tracked variables.
    #[must_use]
    pub fn len(&self) -> usize {
        self.states.len()
    }

    /// Whether no variables are tracked.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.states.is_empty()
    }

    /// Join two ownership abstractions at a control-flow merge point.
    ///
    /// If both paths agree on a variable's ownership state, keep it.
    /// If they disagree, conservatively mark as Owned (least restrictive).
    /// If only one side tracks a variable, drop it (not guaranteed on both paths).
    #[must_use]
    pub fn join(&self, other: &Self) -> Self {
        let mut result = BTreeMap::new();
        for (var, state_a) in &self.states {
            if let Some(state_b) = other.states.get(var) {
                if state_a == state_b {
                    result.insert(var.clone(), *state_a);
                } else {
                    result.insert(var.clone(), OwnershipState::Owned);
                }
            }
        }
        Self { states: result }
    }

    /// Meet two ownership abstractions (conjunction: both constraints hold).
    ///
    /// If both paths agree, keep. If they disagree, prefer the more restrictive
    /// state (Moved > MutableBorrow > SharedBorrow > Owned).
    #[must_use]
    pub fn meet(&self, other: &Self) -> Self {
        let mut result = self.states.clone();
        for (var, state_b) in &other.states {
            result
                .entry(var.clone())
                .and_modify(|state_a| {
                    *state_a = more_restrictive(*state_a, *state_b);
                })
                .or_insert(*state_b);
        }
        Self { states: result }
    }

    /// Generate predicates from the ownership state.
    ///
    /// Ownership state translates to path feasibility constraints:
    /// - Moved variables generate `var == __moved__` (sentinel for pruning).
    /// - Mutably borrowed variables generate non-aliasing predicates.
    #[must_use]
    pub fn to_predicates(&self) -> Vec<Predicate> {
        let mut preds = Vec::new();
        for (var, state) in &self.states {
            match state {
                OwnershipState::Moved => {
                    preds.push(Predicate::Custom(format!("{var}:moved")));
                }
                OwnershipState::MutableBorrow => {
                    preds.push(Predicate::Custom(format!("{var}:exclusive")));
                }
                OwnershipState::SharedBorrow => {
                    preds.push(Predicate::NonNull(var.clone()));
                }
                OwnershipState::Owned => {
                    // Owned is the default; no special predicate needed.
                }
            }
        }
        preds
    }
}

/// Return the more restrictive of two ownership states.
pub(in crate::rust_abstraction) fn more_restrictive(
    a: OwnershipState,
    b: OwnershipState,
) -> OwnershipState {
    fn rank(s: OwnershipState) -> u8 {
        match s {
            OwnershipState::Owned => 0,
            OwnershipState::SharedBorrow => 1,
            OwnershipState::MutableBorrow => 2,
            OwnershipState::Moved => 3,
        }
    }
    if rank(a) >= rank(b) { a } else { b }
}
