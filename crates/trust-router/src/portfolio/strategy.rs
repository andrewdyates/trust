// trust-router/portfolio/strategy.rs: Strategy selection functions
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::VerificationCondition;

use crate::classifier::{self, QueryClass};

use super::types::{PortfolioStrategy, StateSpaceEstimate};

/// tRust: Select strategies adaptively based on state space estimate.
///
/// Returns a prioritized list of strategies appropriate for the estimated
/// state space size. All strategies are included but ordering varies.
#[must_use]
pub fn select_strategies(estimate: StateSpaceEstimate) -> Vec<PortfolioStrategy> {
    match estimate {
        StateSpaceEstimate::Small => vec![
            PortfolioStrategy::Bfs,
            PortfolioStrategy::Structural,
            PortfolioStrategy::Bmc,
            PortfolioStrategy::KInduction,
            PortfolioStrategy::Ic3Pdr,
        ],
        StateSpaceEstimate::Medium => vec![
            PortfolioStrategy::Bmc,
            PortfolioStrategy::Bfs,
            PortfolioStrategy::Ic3Pdr,
            PortfolioStrategy::KInduction,
            PortfolioStrategy::Structural,
        ],
        StateSpaceEstimate::Large => vec![
            PortfolioStrategy::Ic3Pdr,
            PortfolioStrategy::KInduction,
            PortfolioStrategy::Bmc,
            PortfolioStrategy::Structural,
            PortfolioStrategy::Bfs,
        ],
        StateSpaceEstimate::Unknown => vec![
            PortfolioStrategy::Bmc,
            PortfolioStrategy::Ic3Pdr,
            PortfolioStrategy::Bfs,
            PortfolioStrategy::KInduction,
            PortfolioStrategy::Structural,
        ],
    }
}

// ---------------------------------------------------------------------------
// tRust #446: Connect QueryClass classifier to portfolio strategy selection
// ---------------------------------------------------------------------------

/// tRust #446: Select portfolio strategies based on `QueryClass` from the
/// classifier.
///
/// Maps the structural classification of a VC formula (linear arithmetic,
/// bitvector, quantified, etc.) to a prioritized list of verification
/// strategies. This enables the portfolio racer to front-load the strategy
/// most likely to succeed for a given formula type, reducing average solve
/// time.
///
/// Strategy rationale:
/// - **EasyLinear**: BMC finds counterexamples fast; k-induction proves
///   inductively. IC3/PDR and BFS are fallbacks.
/// - **BitVector**: BMC excels on bounded BV reasoning. k-induction is
///   effective for BV induction. Structural analysis is rarely useful.
/// - **Quantified**: IC3/PDR handles quantifier instantiation via CHC.
///   k-induction can prove universal properties. BMC is a fallback.
/// - **HardNonlinear**: IC3/PDR with nonlinear CHC encoding. k-induction
///   for inductive reasoning. BMC is bounded fallback.
/// - **ArrayTheory**: IC3/PDR handles array axioms well. BMC for bounded
///   reasoning. Structural is unlikely to help.
/// - **Mixed**: All strategies are viable; BMC first for fast counterexamples.
/// - **Ownership**: Structural checks (ownership invariants) first, then
///   BMC and IC3/PDR for deeper reasoning.
#[must_use]
pub fn select_strategies_for_query(class: QueryClass) -> Vec<PortfolioStrategy> {
    match class {
        QueryClass::EasyLinear => vec![
            PortfolioStrategy::Bmc,
            PortfolioStrategy::KInduction,
            PortfolioStrategy::Ic3Pdr,
            PortfolioStrategy::Structural,
            PortfolioStrategy::Bfs,
        ],
        QueryClass::BitVector => vec![
            PortfolioStrategy::Bmc,
            PortfolioStrategy::KInduction,
            PortfolioStrategy::Ic3Pdr,
            PortfolioStrategy::Bfs,
            PortfolioStrategy::Structural,
        ],
        QueryClass::Quantified => vec![
            PortfolioStrategy::Ic3Pdr,
            PortfolioStrategy::StrongestPostcondition,
            PortfolioStrategy::KInduction,
            PortfolioStrategy::Bmc,
            PortfolioStrategy::Bfs,
            PortfolioStrategy::Structural,
        ],
        QueryClass::HardNonlinear => vec![
            PortfolioStrategy::Ic3Pdr,
            PortfolioStrategy::KInduction,
            PortfolioStrategy::Bmc,
            PortfolioStrategy::Structural,
            PortfolioStrategy::Bfs,
        ],
        QueryClass::ArrayTheory => vec![
            PortfolioStrategy::Ic3Pdr,
            PortfolioStrategy::Bmc,
            PortfolioStrategy::KInduction,
            PortfolioStrategy::Bfs,
            PortfolioStrategy::Structural,
        ],
        QueryClass::Mixed => vec![
            PortfolioStrategy::Bmc,
            PortfolioStrategy::Ic3Pdr,
            PortfolioStrategy::KInduction,
            PortfolioStrategy::Bfs,
            PortfolioStrategy::Structural,
        ],
        QueryClass::Ownership => vec![
            PortfolioStrategy::Structural,
            PortfolioStrategy::Bmc,
            PortfolioStrategy::Ic3Pdr,
            PortfolioStrategy::KInduction,
            PortfolioStrategy::Bfs,
        ],
    }
}

/// tRust #446: Classify a VC and return prioritized portfolio strategies.
///
/// Convenience function that runs the classifier on a VC and then selects
/// strategies appropriate for the detected query class. Returns both the
/// detected `QueryClass` and the strategy list so callers can log the
/// classification decision.
#[must_use]
pub fn classify_and_select_strategies(
    vc: &VerificationCondition,
) -> (QueryClass, Vec<PortfolioStrategy>) {
    let class = classifier::classify_vc(vc);
    let strategies = select_strategies_for_query(class);
    (class, strategies)
}

/// tRust #446: Select backend roles for a VC using `QueryClass`-aware routing.
///
/// Combines the `QueryClass` from the formula classifier with the
/// `ProofLevel`-based `solver_selection()` to produce a more informed
/// backend role ordering. The `QueryClass` influences which solver families
/// are prioritized:
/// - Linear arithmetic -> SmtSolver first (z4 excels here)
/// - Bitvector -> BoundedModelChecker first (zani excels here)
/// - Quantified -> HigherOrder first (lean5 handles quantifier induction)
/// - Ownership -> Ownership first (certus)
///
/// The result is a de-duplicated list of `BackendRole` values that callers
/// can use to filter and order their backend pool.
#[must_use]
pub fn classified_solver_selection(
    vc: &VerificationCondition,
) -> (QueryClass, Vec<crate::BackendRole>) {
    use crate::BackendRole;

    let class = classifier::classify_vc(vc);

    // Start with class-specific role preferences.
    let class_roles: Vec<BackendRole> = match class {
        QueryClass::EasyLinear => {
            vec![BackendRole::SmtSolver, BackendRole::BoundedModelChecker, BackendRole::General]
        }
        QueryClass::BitVector => {
            vec![BackendRole::BoundedModelChecker, BackendRole::SmtSolver, BackendRole::General]
        }
        QueryClass::Quantified => vec![
            BackendRole::HigherOrder,
            BackendRole::Deductive,
            BackendRole::SmtSolver,
            BackendRole::General,
        ],
        QueryClass::HardNonlinear => vec![
            BackendRole::SmtSolver,
            BackendRole::Deductive,
            BackendRole::HigherOrder,
            BackendRole::General,
        ],
        QueryClass::ArrayTheory => {
            vec![BackendRole::SmtSolver, BackendRole::Deductive, BackendRole::General]
        }
        QueryClass::Mixed => vec![
            BackendRole::SmtSolver,
            BackendRole::BoundedModelChecker,
            BackendRole::Deductive,
            BackendRole::General,
        ],
        QueryClass::Ownership => vec![
            BackendRole::Ownership,
            BackendRole::SmtSolver,
            BackendRole::Deductive,
            BackendRole::General,
        ],
    };

    // Merge with ProofLevel-based selection, de-duplicating while preserving
    // the class-specific ordering as primary.
    let level_roles = solver_selection(vc);
    let mut merged = class_roles;
    for role in level_roles {
        if !merged.contains(&role) {
            merged.push(role);
        }
    }

    (class, merged)
}

/// tRust #446: Suggested per-solver timeout in milliseconds based on QueryClass.
///
/// Returns a timeout that reflects the expected difficulty of the query class.
/// Simple boolean/linear queries get short timeouts; quantified/nonlinear
/// queries get longer ones. This prevents easy queries from wasting time
/// on slow solver paths while giving hard queries enough room to converge.
#[must_use]
pub fn suggested_timeout_ms(class: QueryClass) -> u64 {
    match class {
        QueryClass::EasyLinear => 5_000,     // 5s — should be fast
        QueryClass::BitVector => 10_000,     // 10s — BV solving can be moderate
        QueryClass::ArrayTheory => 15_000,   // 15s — array reasoning needs time
        QueryClass::HardNonlinear => 30_000, // 30s — nonlinear is expensive
        QueryClass::Quantified => 60_000,    // 60s — quantifier instantiation
        QueryClass::Mixed => 30_000,         // 30s — multiple theories
        QueryClass::Ownership => 15_000,     // 15s — ownership checks
    }
}

/// tRust: Select which solvers to include in a portfolio based on VC type.
///
/// Returns a list of `BackendRole` values appropriate for the given VC's
/// proof level and kind. Callers filter their available backends by these
/// roles to build the portfolio lane list.
#[must_use]
pub fn solver_selection(vc: &VerificationCondition) -> Vec<crate::BackendRole> {
    use crate::BackendRole;
    use trust_types::ProofLevel;

    let level = vc.kind.proof_level();

    match level {
        ProofLevel::L0Safety => vec![
            BackendRole::SmtSolver,
            BackendRole::BoundedModelChecker,
            BackendRole::Cegar,
            BackendRole::General,
        ],
        ProofLevel::L1Functional => vec![
            BackendRole::Deductive,
            BackendRole::SmtSolver,
            BackendRole::Cegar,
            BackendRole::BoundedModelChecker,
            BackendRole::General,
        ],
        ProofLevel::L2Domain => vec![
            BackendRole::Temporal,
            BackendRole::Deductive,
            BackendRole::Cegar,
            BackendRole::SmtSolver,
            BackendRole::General,
        ],
        _ => vec![BackendRole::General],
    }
}
