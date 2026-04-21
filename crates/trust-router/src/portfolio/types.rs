// trust-router/portfolio/types.rs: Core portfolio types and enums
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::sync::Arc;

use trust_types::{ProofStrength, VerificationResult};

use crate::VerificationBackend;

/// tRust: Verification strategy for portfolio racing.
///
/// Each strategy represents a different verification approach. The portfolio
/// racer spawns one thread per strategy, racing them against each other.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum PortfolioStrategy {
    /// Bounded Model Checking via z4 — fast counterexamples for safety properties.
    Bmc,
    /// Explicit-state BFS (tla2) — exhaustive for small state spaces.
    Bfs,
    /// IC3/PDR via z4-chc — unbounded safety proofs (AG !bad).
    ///
    /// tRust #194: Proves safety only. Does NOT prove termination or liveness.
    Ic3Pdr,
    /// k-Induction via z4 — inductive safety proofs (AG !bad).
    ///
    /// tRust #194: Proves safety only. Does NOT prove termination or liveness.
    KInduction,
    /// Structural analysis (siphon/trap) — zero-cost proofs.
    Structural,
    /// Strongest-postcondition deductive verification via sunder.
    StrongestPostcondition,
}

impl PortfolioStrategy {
    /// Human-readable name for diagnostics and `ProofStrength` attribution.
    #[must_use]
    pub fn name(self) -> &'static str {
        match self {
            PortfolioStrategy::Bmc => "bmc",
            PortfolioStrategy::Bfs => "bfs",
            PortfolioStrategy::Ic3Pdr => "ic3pdr",
            PortfolioStrategy::KInduction => "k-induction",
            PortfolioStrategy::Structural => "structural",
            PortfolioStrategy::StrongestPostcondition => "sp",
        }
    }

    /// Map a strategy to the `ProofStrength` it produces when successful.
    #[must_use]
    pub fn proof_strength(self) -> ProofStrength {
        match self {
            PortfolioStrategy::Bmc => ProofStrength::bounded(0), // depth filled by backend
            PortfolioStrategy::Bfs => ProofStrength::bounded(0),
            PortfolioStrategy::Ic3Pdr => ProofStrength::inductive(),
            PortfolioStrategy::KInduction => ProofStrength::inductive(),
            PortfolioStrategy::Structural => ProofStrength::deductive(),
            PortfolioStrategy::StrongestPostcondition => ProofStrength::deductive(),
        }
    }
}

/// tRust: A lane in the portfolio: pairs a strategy with its backend.
pub struct PortfolioLane {
    pub strategy: PortfolioStrategy,
    pub backend: Arc<dyn VerificationBackend>,
}

/// tRust: Result from a portfolio race, including which strategy won.
#[derive(Debug, Clone)]
pub struct PortfolioResult {
    /// The verification result from the winning strategy.
    pub result: VerificationResult,
    /// Which strategy produced the result.
    pub winning_strategy: PortfolioStrategy,
    /// Wall-clock time for the entire race in milliseconds.
    pub race_time_ms: u64,
    /// Number of strategies that were racing.
    pub total_lanes: usize,
    /// tRust #476: Whether the winning strategy came from a proof replay cache hit.
    /// `Some(true)` = cache hit and the replayed strategy succeeded.
    /// `Some(false)` = cache hit but the replayed strategy failed (fell back to race).
    /// `None` = no cache lookup was performed.
    pub replay_hit: Option<bool>,
}

impl PortfolioResult {
    /// True if the winning result is definitive (Proved or Failed/Counterexample).
    #[must_use]
    pub fn is_definitive(&self) -> bool {
        self.result.is_proved() || self.result.is_failed()
    }
}

/// tRust: Estimate of state space size for adaptive strategy selection.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum StateSpaceEstimate {
    /// Fewer than 100K states — BFS is viable.
    Small,
    /// 100K to 10M states — parallel BFS or BMC preferred.
    Medium,
    /// Over 10M states — symbolic methods required.
    Large,
    /// Unknown size — use all available strategies.
    Unknown,
}

/// tRust: High-level dispatch mode for portfolio verification.
///
/// Controls *how* the portfolio runner uses its backends for a given VC.
/// - `Race`: spawn all backends in parallel, first conclusive result wins.
/// - `Cascade`: try backends in priority order, stop on conclusive result.
/// - `Selective`: route to the best backend based on `VcKind`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum DispatchMode {
    /// tRust: Race all backends in parallel. First Proved/Counterexample wins,
    /// remaining threads are cancelled via `AtomicBool`.
    Race,
    /// tRust: Try backends sequentially in priority order. Stop as soon as
    /// a conclusive result (Proved or Failed) is obtained.
    Cascade,
    /// tRust: Route each VC to the single best backend for its `VcKind`,
    /// using the router's `BackendRole` preference ranking.
    Selective,
}

/// Sentinel result when no backend is available.
pub(crate) fn no_backend_result() -> VerificationResult {
    VerificationResult::Unknown {
        solver: "none".to_string(),
        time_ms: 0,
        reason: "no backend available".to_string(),
    }
}
