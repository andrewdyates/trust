// trust-router/portfolio/reconciliation.rs: ResultPolicy, reconciliation, PortfolioStats
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, mpsc};
use std::thread;

use trust_types::{VerificationCondition, VerificationResult};

use crate::VerificationBackend;

use super::types::no_backend_result;
use trust_types::fx::FxHashMap;

/// tRust: Policy for how a portfolio race determines its winning result.
///
/// This enum controls the acceptance criteria for the first result that
/// terminates the portfolio race. Unlike `RaceStrategy` (which controls
/// the racing mechanism), `ResultPolicy` controls what *kind* of result
/// is accepted as the winner.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
#[derive(Default)]
pub enum ResultPolicy {
    /// Accept the first solver that returns Proved (SAT from the prover's
    /// perspective — the property is satisfiable/holds).
    FirstSat,
    /// Accept the first solver that returns Failed (UNSAT from the prover's
    /// perspective — the property does not hold, counterexample found).
    FirstUnsat,
    /// Accept the first solver that returns any definitive result
    /// (Proved or Failed). This is the default portfolio behavior.
    #[default]
    FirstAny,
    /// Wait for all solvers and accept the majority verdict. If there is
    /// a tie, prefer Proved over Failed over Unknown.
    Majority,
    /// tRust #423: Wait for all solvers and reconcile conflicting results.
    ///
    /// If any solver says Proved and another says Failed (counterexample),
    /// returns a `ReconciliationOutcome::Conflict` instead of silently
    /// picking one. If all definitive results agree, returns the agreed
    /// result. This prevents soundness issues from solver disagreements.
    Reconciled,
}

/// tRust #423: Outcome of cross-solver reconciliation.
///
/// When `ResultPolicy::Reconciled` is used, this enum captures whether all
/// solvers agree or whether a conflict (Proved vs Failed) was detected.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum ReconciliationOutcome {
    /// All definitive solvers agreed. Contains the agreed result and solver name.
    Agreed { result: VerificationResult, solver: String },
    /// At least one solver said Proved and another said Failed.
    /// This indicates a potential soundness issue (solver bug or
    /// differing assumptions) and requires investigation.
    Conflict {
        /// All (solver_name, result) pairs collected during the race.
        results: Vec<(String, VerificationResult)>,
        /// Solvers that returned Proved.
        proved_solvers: Vec<String>,
        /// Solvers that returned Failed (counterexample).
        failed_solvers: Vec<String>,
    },
    /// No solver returned a definitive result. Contains the best
    /// non-definitive result as a fallback.
    Inconclusive { result: VerificationResult, solver: String },
}

impl ReconciliationOutcome {
    /// True if there is a Proved-vs-Failed conflict.
    #[must_use]
    pub fn is_conflict(&self) -> bool {
        matches!(self, ReconciliationOutcome::Conflict { .. })
    }

    /// True if all definitive solvers agreed.
    #[must_use]
    pub fn is_agreed(&self) -> bool {
        matches!(self, ReconciliationOutcome::Agreed { .. })
    }

    /// True if no solver returned a definitive result.
    #[must_use]
    pub fn is_inconclusive(&self) -> bool {
        matches!(self, ReconciliationOutcome::Inconclusive { .. })
    }

    /// Extract the primary verification result.
    ///
    /// For `Agreed`, returns the agreed result.
    /// For `Conflict`, returns `VerificationResult::Unknown` with a
    /// conflict description (callers should inspect the conflict details).
    /// For `Inconclusive`, returns the fallback result.
    #[must_use]
    pub fn into_result(self) -> VerificationResult {
        match self {
            ReconciliationOutcome::Agreed { result, .. } => result,
            ReconciliationOutcome::Conflict { proved_solvers, failed_solvers, .. } => {
                VerificationResult::Unknown {
                    solver: "portfolio-reconciler".to_string(),
                    time_ms: 0,
                    reason: format!(
                        "cross-solver conflict: proved by [{}], failed by [{}]",
                        proved_solvers.join(", "),
                        failed_solvers.join(", "),
                    ),
                }
            }
            ReconciliationOutcome::Inconclusive { result, .. } => result,
        }
    }
}

/// tRust: Accumulated statistics on portfolio solver performance.
///
/// Tracks per-solver win rates, total races, and timing across
/// multiple portfolio invocations. Useful for adaptive solver selection.
#[derive(Debug, Clone, Default)]
pub struct PortfolioStats {
    /// Per-solver: (total_participations, wins, total_time_ms).
    per_solver: FxHashMap<String, SolverRecord>,
    /// Total portfolio races executed.
    total_races: u64,
}

/// tRust: Per-solver record in PortfolioStats.
#[derive(Debug, Clone, Default)]
struct SolverRecord {
    participations: u64,
    wins: u64,
    total_time_ms: u64,
}

impl PortfolioStats {
    /// Create empty statistics.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Record that a solver participated in a race, optionally winning.
    pub fn record(&mut self, solver: &str, won: bool, time_ms: u64) {
        let entry = self.per_solver.entry(solver.to_string()).or_default();
        entry.participations += 1;
        if won {
            entry.wins += 1;
        }
        entry.total_time_ms += time_ms;
    }

    /// Record the completion of an entire portfolio race.
    pub fn record_race(&mut self) {
        self.total_races += 1;
    }

    /// Win rate for a solver (0.0 to 1.0).
    #[must_use]
    pub fn win_rate(&self, solver: &str) -> f64 {
        self.per_solver
            .get(solver)
            .map(
                |r| {
                    if r.participations == 0 {
                        0.0
                    } else {
                        r.wins as f64 / r.participations as f64
                    }
                },
            )
            .unwrap_or(0.0)
    }

    /// Average time in ms for a solver across all participations.
    #[must_use]
    pub fn avg_time_ms(&self, solver: &str) -> f64 {
        self.per_solver
            .get(solver)
            .map(|r| {
                if r.participations == 0 {
                    0.0
                } else {
                    r.total_time_ms as f64 / r.participations as f64
                }
            })
            .unwrap_or(0.0)
    }

    /// Total portfolio races recorded.
    #[must_use]
    pub fn total_races(&self) -> u64 {
        self.total_races
    }

    /// Number of wins for a solver.
    #[must_use]
    pub fn wins(&self, solver: &str) -> u64 {
        self.per_solver.get(solver).map_or(0, |r| r.wins)
    }

    /// All tracked solver names.
    #[must_use]
    pub fn solver_names(&self) -> Vec<&str> {
        self.per_solver.keys().map(String::as_str).collect()
    }

    /// Return a sorted list of (solver_name, win_rate) pairs, best first.
    #[must_use]
    pub fn ranking(&self) -> Vec<(&str, f64)> {
        let mut pairs: Vec<(&str, f64)> = self
            .per_solver
            .iter()
            .map(|(name, r)| {
                let rate = if r.participations == 0 {
                    0.0
                } else {
                    r.wins as f64 / r.participations as f64
                };
                (name.as_str(), rate)
            })
            .collect();
        // Sort by win rate descending; break ties alphabetically.
        pairs.sort_by(|a, b| {
            b.1.partial_cmp(&a.1).unwrap_or(std::cmp::Ordering::Equal).then_with(|| a.0.cmp(b.0))
        });
        pairs
    }
}

/// tRust: One-shot portfolio verification with a result policy.
///
/// Races the given backends on a single VC, applying `policy` to select
/// the winning result. Returns the verification result and the name of
/// the winning solver.
///
/// This is a convenience function for callers that do not need the full
/// `PortfolioRunner` or `SolverPool` infrastructure.
#[must_use]
pub fn run_portfolio(
    vc: &VerificationCondition,
    backends: &[Arc<dyn VerificationBackend>],
    policy: ResultPolicy,
) -> (VerificationResult, String) {
    if backends.is_empty() {
        return (no_backend_result(), "none".to_string());
    }

    let cancelled = Arc::new(AtomicBool::new(false));
    let (tx, rx) = mpsc::channel();
    let mut handles = Vec::with_capacity(backends.len());

    for backend in backends {
        let backend = Arc::clone(backend);
        let vc = vc.clone();
        let cancelled = Arc::clone(&cancelled);
        let tx = tx.clone();

        handles.push(thread::spawn(move || {
            if cancelled.load(Ordering::Relaxed) {
                return;
            }
            let result = backend.verify(&vc);
            let solver_name = backend.name().to_string();
            let _ = tx.send((solver_name, result));
        }));
    }
    drop(tx);

    let mut all_results: Vec<(String, VerificationResult)> = Vec::new();
    let mut winner: Option<(String, VerificationResult)> = None;

    let early_exit = matches!(
        policy,
        ResultPolicy::FirstSat | ResultPolicy::FirstUnsat | ResultPolicy::FirstAny
    );

    for (solver_name, result) in rx {
        let dominated = match policy {
            ResultPolicy::FirstSat => result.is_proved(),
            ResultPolicy::FirstUnsat => result.is_failed(),
            ResultPolicy::FirstAny => result.is_proved() || result.is_failed(),
            ResultPolicy::Majority | ResultPolicy::Reconciled => false,
        };

        if early_exit && dominated && winner.is_none() {
            cancelled.store(true, Ordering::Relaxed);
            winner = Some((solver_name.clone(), result.clone()));
        }

        all_results.push((solver_name, result));

        if winner.is_some() && early_exit {
            break;
        }
    }

    for handle in handles {
        let _ = handle.join();
    }

    // tRust #804 P1-7: Detect panicked backends. If any thread panicked,
    // all_results.len() < backends.len(). For Majority/Reconciled policies
    // that require quorum, missing results are a correctness risk.
    let expected_count = backends.len();
    let actual_count = all_results.len();
    if actual_count < expected_count
        && matches!(policy, ResultPolicy::Majority | ResultPolicy::Reconciled)
    {
        return (
            VerificationResult::Unknown {
                solver: "portfolio".to_string(),
                time_ms: 0,
                reason: format!(
                    "only {actual_count}/{expected_count} backends responded (possible panic); cannot establish quorum"
                ),
            },
            "portfolio".to_string(),
        );
    }

    // For Majority policy, tally votes.
    if matches!(policy, ResultPolicy::Majority) {
        let mut proved_count = 0u64;
        let mut failed_count = 0u64;
        let mut proved_winner: Option<(String, VerificationResult)> = None;
        let mut failed_winner: Option<(String, VerificationResult)> = None;

        for (name, result) in &all_results {
            if result.is_proved() {
                proved_count += 1;
                if proved_winner.is_none() {
                    proved_winner = Some((name.clone(), result.clone()));
                }
            } else if result.is_failed() {
                failed_count += 1;
                if failed_winner.is_none() {
                    failed_winner = Some((name.clone(), result.clone()));
                }
            }
        }

        // tRust #803 P0-1: True majority requires strictly more than half the
        // total votes. Unknown/Timeout votes count toward the total. When both
        // Proved and Failed appear (conflict), return Unknown regardless of counts.
        let total = all_results.len() as u64;
        let half = total / 2;

        // Conflict: both Proved and Failed present => Unknown.
        if proved_count > 0 && failed_count > 0 {
            return (
                VerificationResult::Unknown {
                    solver: "portfolio-majority".to_string(),
                    time_ms: 0,
                    reason: format!(
                        "majority conflict: {} proved vs {} failed out of {} total",
                        proved_count, failed_count, total
                    ),
                },
                "portfolio-majority".to_string(),
            );
        }

        // Strict majority: winning class must have > half the total votes.
        if proved_count > half && let Some((name, result)) = proved_winner {
            return (result, name);
        }
        if failed_count > half && let Some((name, result)) = failed_winner {
            return (result, name);
        }

        // No strict majority reached — return Unknown.
        return (
            VerificationResult::Unknown {
                solver: "portfolio-majority".to_string(),
                time_ms: 0,
                reason: format!(
                    "no majority: {} proved, {} failed out of {} total",
                    proved_count, failed_count, total
                ),
            },
            "portfolio-majority".to_string(),
        );
    }

    // tRust #423: For Reconciled policy, detect Proved vs Failed conflicts.
    if matches!(policy, ResultPolicy::Reconciled) {
        let outcome = reconcile_results(all_results);
        let solver = match &outcome {
            ReconciliationOutcome::Agreed { solver, .. } => solver.clone(),
            ReconciliationOutcome::Conflict { .. } => "portfolio-reconciler".to_string(),
            ReconciliationOutcome::Inconclusive { solver, .. } => solver.clone(),
        };
        return (outcome.into_result(), solver);
    }

    // Return the first matching result for early-exit policies.
    if let Some((name, result)) = winner {
        return (result, name);
    }

    // Fallback: return the first result if available.
    if let Some((name, result)) = all_results.into_iter().next() {
        return (result, name);
    }

    (no_backend_result(), "none".to_string())
}

/// tRust #423: Reconcile a set of solver results, detecting Proved vs Failed conflicts.
///
/// This is the core reconciliation logic used by `ResultPolicy::Reconciled`
/// and `run_portfolio_reconciled`.
#[must_use]
pub(crate) fn reconcile_results(
    all_results: Vec<(String, VerificationResult)>,
) -> ReconciliationOutcome {
    let mut proved_solvers = Vec::new();
    let mut failed_solvers = Vec::new();
    let mut first_proved: Option<(String, VerificationResult)> = None;
    let mut first_failed: Option<(String, VerificationResult)> = None;
    let mut first_any: Option<(String, VerificationResult)> = None;

    for (name, result) in &all_results {
        if first_any.is_none() {
            first_any = Some((name.clone(), result.clone()));
        }
        if result.is_proved() {
            proved_solvers.push(name.clone());
            if first_proved.is_none() {
                first_proved = Some((name.clone(), result.clone()));
            }
        } else if result.is_failed() {
            failed_solvers.push(name.clone());
            if first_failed.is_none() {
                first_failed = Some((name.clone(), result.clone()));
            }
        }
    }

    // tRust #423: Conflict detection — Proved vs Failed disagreement.
    if !proved_solvers.is_empty() && !failed_solvers.is_empty() {
        return ReconciliationOutcome::Conflict {
            results: all_results,
            proved_solvers,
            failed_solvers,
        };
    }

    // All definitive results agree (or only one type of definitive result).
    if let Some((name, result)) = first_proved {
        return ReconciliationOutcome::Agreed { result, solver: name };
    }
    if let Some((name, result)) = first_failed {
        return ReconciliationOutcome::Agreed { result, solver: name };
    }

    // No definitive results — inconclusive.
    match first_any {
        Some((name, result)) => ReconciliationOutcome::Inconclusive { result, solver: name },
        None => ReconciliationOutcome::Inconclusive {
            result: no_backend_result(),
            solver: "none".to_string(),
        },
    }
}

/// tRust #423: One-shot portfolio verification with cross-solver reconciliation.
///
/// Like `run_portfolio`, but returns a `ReconciliationOutcome` that exposes
/// conflicts between solvers. This is the recommended entry point for callers
/// that need to detect soundness issues from solver disagreements.
///
/// Waits for all solvers to complete (or be cancelled by overall timeout),
/// then reconciles the results. If one solver says Proved and another says
/// Failed, returns `ReconciliationOutcome::Conflict`.
#[must_use]
pub fn run_portfolio_reconciled(
    vc: &VerificationCondition,
    backends: &[Arc<dyn VerificationBackend>],
) -> ReconciliationOutcome {
    if backends.is_empty() {
        return ReconciliationOutcome::Inconclusive {
            result: no_backend_result(),
            solver: "none".to_string(),
        };
    }

    let (tx, rx) = mpsc::channel();
    let mut handles = Vec::with_capacity(backends.len());

    for backend in backends {
        let backend = Arc::clone(backend);
        let vc = vc.clone();
        let tx = tx.clone();

        handles.push(thread::spawn(move || {
            let result = backend.verify(&vc);
            let solver_name = backend.name().to_string();
            let _ = tx.send((solver_name, result));
        }));
    }
    drop(tx);

    let all_results: Vec<(String, VerificationResult)> = rx.into_iter().collect();

    for handle in handles {
        let _ = handle.join();
    }

    // tRust #804 (P1-7): If a sending thread panicked, tx.send() was never
    // called, so the channel closed with fewer results than backends. Return
    // Inconclusive to prevent reconciling on partial data.
    if all_results.len() < backends.len() {
        let expected = backends.len();
        let actual = all_results.len();
        return ReconciliationOutcome::Inconclusive {
            result: VerificationResult::Unknown {
                solver: "portfolio-reconciler".to_string(),
                time_ms: 0,
                reason: format!(
                    "only {actual}/{expected} backends responded (possible panic); cannot reconcile"
                ),
            },
            solver: "portfolio-reconciler".to_string(),
        };
    }

    reconcile_results(all_results)
}
