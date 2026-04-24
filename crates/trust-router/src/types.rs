//! Core types for the trust-router crate.
//!
//! Author: Andrew Yates <andrew@andrewdyates.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::formula_arena::{FormulaArena, FormulaRef};
use trust_types::*;

/// tRust: Broad backend role buckets used by routing heuristics.
///
/// These roles let the router prefer a solver family appropriate to a VC
/// before falling back to a general-purpose backend. Future backends can
/// slot into the same ordering without changing call sites.
///
/// # Examples
///
/// ```
/// use trust_router::BackendRole;
///
/// // Each backend advertises its role
/// let role = BackendRole::SmtSolver;
/// assert_ne!(role, BackendRole::General);
///
/// // The router uses roles to rank backends per proof level:
/// // L0Safety prefers SmtSolver > BoundedModelChecker > Cegar > ...
/// // L1Functional prefers Deductive > Cegar > HigherOrder > ...
/// // L2Domain prefers Temporal > HigherOrder > Deductive > ...
/// ```
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BackendRole {
    /// tRust: General-purpose or fallback backend.
    General,
    /// tRust: SMT solver backend.
    SmtSolver,
    /// tRust: Bounded model checking backend.
    BoundedModelChecker,
    /// tRust: Deductive verification backend.
    Deductive,
    /// tRust: Ownership/lifetime backend.
    Ownership,
    /// tRust: Temporal verification backend.
    Temporal,
    /// tRust: Neural verification backend.
    Neural,
    /// tRust: CEGAR predicate abstraction / IC3 backend.
    Cegar,
    /// tRust: Higher-order theorem proving backend (e.g., lean5).
    HigherOrder,
}

/// tRust: Metadata describing one backend in a routed verification plan.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BackendSelection {
    pub index: usize,
    // tRust #907: Interned backend name — small set repeated across all selections.
    pub name: trust_types::Symbol,
    pub role: BackendRole,
    pub can_handle: bool,
}

/// tRust #441: Result from `Router::verify_with_independence`.
///
/// Wraps a `VerificationResult` with metadata about whether constraint
/// independence splitting was applied and how many partitions were created.
#[derive(Debug)]
pub struct IndependenceResult {
    /// The verification result (combined from all partitions if split).
    pub result: VerificationResult,
    /// Whether the formula was split into independent partitions.
    pub was_split: bool,
    /// Number of independent partitions (1 if not split).
    pub partition_count: usize,
}

/// tRust #708: A verification condition bundled with its arena root.
///
/// Pairs a `VerificationCondition` (which holds its formula in `Formula` form
/// for backward compatibility) with a `FormulaRef` root pointing into a shared
/// `FormulaArena`. Backends that override `verify_arena` can use the arena
/// reference for zero-allocation formula traversal.
#[derive(Debug, Clone)]
pub struct ArenaVc {
    /// The classic VC (formula field holds the materialized `Formula`).
    pub vc: VerificationCondition,
    /// Root index into the shared `FormulaArena`.
    pub root: FormulaRef,
}

impl ArenaVc {
    /// Intern a batch of VCs into a shared arena.
    ///
    /// Returns `(arena, arena_vcs)` where each `ArenaVc` holds a
    /// `FormulaRef` root into the returned arena. The VC's `formula`
    /// field is preserved for backward-compatible routing and
    /// `can_handle` checks.
    #[must_use]
    pub fn intern_batch(vcs: &[VerificationCondition]) -> (FormulaArena, Vec<ArenaVc>) {
        let mut arena = FormulaArena::with_capacity(vcs.len() * 8, vcs.len() * 4);
        let arena_vcs = vcs
            .iter()
            .map(|vc| {
                let root = arena.intern(&vc.formula);
                ArenaVc { vc: vc.clone(), root }
            })
            .collect();
        (arena, arena_vcs)
    }

    /// Create a single `ArenaVc` from a VC, interning into the given arena.
    pub fn intern(vc: &VerificationCondition, arena: &mut FormulaArena) -> Self {
        let root = arena.intern(&vc.formula);
        ArenaVc { vc: vc.clone(), root }
    }
}
