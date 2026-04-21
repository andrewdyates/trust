// trust-router/portfolio/solver_pool.rs: Enhanced portfolio types — SolverPool, stats
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, mpsc};
use std::thread;
use std::time::Instant;

use trust_types::{VerificationCondition, VerificationResult};

use crate::VerificationBackend;

use super::types::no_backend_result;
use trust_types::fx::FxHashMap;

/// tRust: Strategy for how a portfolio race selects its winner.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
#[derive(Default)]
pub enum RaceStrategy {
    /// First solver to return a proof (Proved) wins. Failed/Unknown results
    /// are kept as fallbacks only if no solver proves the property.
    FirstSat,
    /// First solver to return any definitive result (Proved or Failed) wins.
    /// This is the classic portfolio approach.
    #[default]
    FirstResult,
    /// Wait for all solvers and pick the result with the highest proof strength.
    /// Falls back to first definitive result if no Proved results arrive.
    BestStrength,
}


/// tRust: Configuration for portfolio racing.
#[derive(Debug, Clone)]
pub struct PortfolioConfig {
    /// Which strategy to use for picking the winner.
    pub strategy: RaceStrategy,
    /// Per-solver timeout in milliseconds (0 = no timeout).
    pub solver_timeout_ms: u64,
    /// Maximum number of solvers to run in parallel.
    pub max_parallel: usize,
}

impl Default for PortfolioConfig {
    fn default() -> Self {
        Self {
            strategy: RaceStrategy::FirstResult,
            solver_timeout_ms: 0,
            max_parallel: 8,
        }
    }
}

/// tRust: A named solver entry in a portfolio pool.
#[derive(Clone)]
pub struct SolverEntry {
    /// Human-readable solver name (e.g., "z4", "zani", "sunder").
    pub name: String,
    /// The backend implementation.
    pub backend: Arc<dyn VerificationBackend>,
}

impl std::fmt::Debug for SolverEntry {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SolverEntry")
            .field("name", &self.name)
            .finish()
    }
}

/// tRust: Pool of solver instances with availability tracking.
///
/// Maintains a set of named solvers and tracks which are currently
/// available for use (vs. busy in a race).
pub struct SolverPool {
    /// All registered solver entries.
    entries: Vec<SolverEntry>,
    /// Configuration for races.
    config: PortfolioConfig,
}

impl SolverPool {
    /// Create a pool from solver entries and config.
    #[must_use]
    pub fn new(entries: Vec<SolverEntry>, config: PortfolioConfig) -> Self {
        Self { entries, config }
    }

    /// Create a pool with default config.
    #[must_use]
    pub fn with_defaults(entries: Vec<SolverEntry>) -> Self {
        Self::new(entries, PortfolioConfig::default())
    }

    /// Number of registered solvers.
    #[must_use]
    pub fn solver_count(&self) -> usize {
        self.entries.len()
    }

    /// Get solver names.
    #[must_use]
    pub fn solver_names(&self) -> Vec<&str> {
        self.entries.iter().map(|e| e.name.as_str()).collect()
    }

    /// The portfolio config.
    #[must_use]
    pub fn config(&self) -> &PortfolioConfig {
        &self.config
    }

    /// Race all solvers on a single VC, returning the enriched result.
    #[must_use]
    pub fn race(&self, vc: &VerificationCondition) -> RaceResult {
        if self.entries.is_empty() {
            return RaceResult {
                winner_result: no_backend_result(),
                winner_solver: "none".to_string(),
                race_time_ms: 0,
                solver_statuses: Vec::new(),
                strategy_used: self.config.strategy,
            };
        }

        let start = Instant::now();
        let cancelled = Arc::new(AtomicBool::new(false));
        let (tx, rx) = mpsc::channel();

        let max_threads = self.config.max_parallel.min(self.entries.len()).max(1);
        let mut handles = Vec::with_capacity(max_threads);

        for entry in self.entries.iter().take(max_threads) {
            let backend = Arc::clone(&entry.backend);
            let vc = vc.clone();
            let cancelled = Arc::clone(&cancelled);
            let tx = tx.clone();
            let solver_name = entry.name.clone();

            handles.push(thread::spawn(move || {
                if cancelled.load(Ordering::Relaxed) {
                    let _ = tx.send((solver_name, None, 0u64));
                    return;
                }
                let solver_start = Instant::now();
                let result = backend.verify(&vc);
                let solver_time = solver_start.elapsed().as_millis() as u64;
                let _ = tx.send((solver_name, Some(result), solver_time));
            }));
        }
        drop(tx);

        let mut solver_statuses = Vec::new();
        let mut winner: Option<(String, VerificationResult)> = None;
        let mut best_strength: Option<(String, VerificationResult)> = None;

        for (solver_name, maybe_result, solver_time) in rx {
            match maybe_result {
                Some(result) => {
                    let is_proved = result.is_proved();
                    let is_failed = result.is_failed();
                    let is_definitive = is_proved || is_failed;

                    solver_statuses.push((
                        solver_name.clone(),
                        crate::adaptive::SolverStatus::Completed { time_ms: solver_time },
                    ));

                    match self.config.strategy {
                        RaceStrategy::FirstResult => {
                            if is_definitive && winner.is_none() {
                                cancelled.store(true, Ordering::Relaxed);
                                winner = Some((solver_name, result));
                            } else if winner.is_none() {
                                winner = Some((solver_name, result));
                            }
                        }
                        RaceStrategy::FirstSat => {
                            if is_proved && winner.is_none() {
                                cancelled.store(true, Ordering::Relaxed);
                                winner = Some((solver_name, result));
                            } else if winner.is_none() {
                                winner = Some((solver_name, result));
                            }
                        }
                        RaceStrategy::BestStrength => {
                            // tRust #424: Compare proof strengths; keep the
                            // strongest proved result, not just the last one.
                            if is_proved {
                                let dominated = best_strength
                                    .as_ref()
                                    .is_none_or(|(_, existing)| {
                                        let existing_order = match existing {
                                            VerificationResult::Proved { strength, .. } => {
                                                strength.assurance.strength_order()
                                            }
                                            _ => 0,
                                        };
                                        let new_order = match &result {
                                            VerificationResult::Proved { strength, .. } => {
                                                strength.assurance.strength_order()
                                            }
                                            _ => 0,
                                        };
                                        new_order > existing_order
                                    });
                                if dominated {
                                    best_strength = Some((solver_name, result));
                                }
                            } else if winner.is_none() {
                                winner = Some((solver_name, result));
                            }
                        }
                    }
                }
                None => {
                    solver_statuses
                        .push((solver_name, crate::adaptive::SolverStatus::Cancelled));
                }
            }
        }

        for handle in handles {
            let _ = handle.join();
        }

        let race_time_ms = start.elapsed().as_millis() as u64;

        // For BestStrength, prefer the best proved result
        let final_winner = best_strength.or(winner);
        let (winner_solver, winner_result) = final_winner.unwrap_or_else(|| {
            ("none".to_string(), no_backend_result())
        });

        RaceResult {
            winner_result,
            winner_solver,
            race_time_ms,
            solver_statuses,
            strategy_used: self.config.strategy,
        }
    }

    /// Race on multiple VCs.
    #[must_use]
    pub fn race_all(
        &self,
        vcs: &[VerificationCondition],
    ) -> Vec<(VerificationCondition, RaceResult)> {
        vcs.iter().map(|vc| (vc.clone(), self.race(vc))).collect()
    }
}

/// tRust: Result from an enhanced portfolio race.
///
/// Contains the winning result plus per-solver status and timing.
#[derive(Debug, Clone)]
pub struct RaceResult {
    /// The verification result from the winning solver.
    pub winner_result: VerificationResult,
    /// Name of the solver that produced the winning result.
    pub winner_solver: String,
    /// Wall-clock time for the entire race in milliseconds.
    pub race_time_ms: u64,
    /// Per-solver status: (solver_name, status).
    pub solver_statuses: Vec<(String, crate::adaptive::SolverStatus)>,
    /// Which strategy was used.
    pub strategy_used: RaceStrategy,
}

impl RaceResult {
    /// Whether the winning result is definitive.
    #[must_use]
    pub fn is_definitive(&self) -> bool {
        self.winner_result.is_proved() || self.winner_result.is_failed()
    }

    /// Number of solvers that participated.
    #[must_use]
    pub fn solver_count(&self) -> usize {
        self.solver_statuses.len()
    }
}

/// tRust: Accumulated statistics on solver performance across races.
#[derive(Debug, Clone, Default)]
pub struct SolverStatistics {
    /// Per-solver: (total_races, wins, cumulative_time_ms).
    stats: FxHashMap<String, (u64, u64, u64)>,
}

impl SolverStatistics {
    /// Create empty statistics.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Record a race result for a solver.
    pub fn record_race(&mut self, solver: &str, won: bool, time_ms: u64) {
        let entry = self.stats.entry(solver.to_string()).or_insert((0, 0, 0));
        entry.0 += 1;
        if won {
            entry.1 += 1;
        }
        entry.2 += time_ms;
    }

    /// Win rate for a solver.
    #[must_use]
    pub fn win_rate(&self, solver: &str) -> f64 {
        self.stats
            .get(solver)
            .map(|(races, wins, _)| {
                if *races == 0 { 0.0 } else { *wins as f64 / *races as f64 }
            })
            .unwrap_or(0.0)
    }

    /// Average time for a solver.
    #[must_use]
    pub fn avg_time_ms(&self, solver: &str) -> f64 {
        self.stats
            .get(solver)
            .map(|(races, _, total_time)| {
                if *races == 0 {
                    0.0
                } else {
                    *total_time as f64 / *races as f64
                }
            })
            .unwrap_or(0.0)
    }

    /// Total races recorded.
    #[must_use]
    pub fn total_races(&self) -> u64 {
        self.stats.values().map(|(races, _, _)| *races).sum()
    }

    /// All tracked solver names.
    #[must_use]
    pub fn solver_names(&self) -> Vec<&str> {
        self.stats.keys().map(String::as_str).collect()
    }
}
