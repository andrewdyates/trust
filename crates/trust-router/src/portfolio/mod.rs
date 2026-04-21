// trust-router/portfolio/mod.rs: Portfolio racing for parallel verification strategies
//
// tRust: Races multiple verification strategies (BMC, BFS, IC3/PDR, etc.) in
// parallel. First definitive result (Proved or Counterexample) wins; remaining
// strategies are cancelled. This maximizes coverage across different verification
// techniques for temporal and safety properties.
//
// Split into sub-modules for readability (#455):
//   types.rs         — Core types: PortfolioStrategy, PortfolioLane, etc.
//   strategy.rs      — Strategy selection (adaptive, query-class-aware)
//   racing.rs        — Race execution: race(), PortfolioRacer, PortfolioRunner
//   solver_pool.rs   — SolverPool, RaceStrategy, RaceResult, SolverStatistics
//   cached.rs        — CachedPortfolioRacer, TimeoutFallbackChain
//   reconciliation.rs — ResultPolicy, reconciliation, PortfolioStats
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

mod cached;
mod racing;
mod reconciliation;
mod solver_pool;
mod strategy;
mod types;

// Re-export all public items for backward compatibility.
// Existing code uses `use crate::portfolio::{...}` and must continue to work.

// --- types.rs ---
#[allow(unused_imports)]
pub use types::{
    DispatchMode, PortfolioLane, PortfolioResult, PortfolioStrategy, StateSpaceEstimate,
};
// no_backend_result is pub(crate) — re-export at crate visibility

// --- strategy.rs ---
#[allow(unused_imports)]
pub use strategy::{
    classify_and_select_strategies, classified_solver_selection, select_strategies,
    select_strategies_for_query, solver_selection, suggested_timeout_ms,
};

// --- racing.rs ---
#[allow(unused_imports)]
pub use racing::{PortfolioRacer, PortfolioRunner, race, vc_to_strategy_key};

// --- solver_pool.rs ---
#[allow(unused_imports)]
pub use solver_pool::{
    PortfolioConfig, RaceResult, RaceStrategy, SolverEntry, SolverPool, SolverStatistics,
};

// --- cached.rs ---
#[allow(unused_imports)]
pub use cached::{BackendConfig, CachedPortfolioRacer, TimeoutFallbackChain};

// --- reconciliation.rs ---
#[allow(unused_imports)]
pub use reconciliation::{
    PortfolioStats, ReconciliationOutcome, ResultPolicy, run_portfolio,
    run_portfolio_reconciled,
};
#[allow(unused_imports)]
pub(crate) use reconciliation::reconcile_results;

#[cfg(test)]
mod tests;
