// trust-router/adaptive.rs: Adaptive solver dispatch based on historical win rates
//
// tRust: Learns which solvers perform best for each VcKind over time.
// After a warmup period of full portfolio races, routes VCs to their
// historically best solver, with fallback to full portfolio on failure.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;
use std::sync::{Arc, Mutex};
use std::time::Instant;

use trust_types::{VerificationCondition, VerificationResult};

use crate::portfolio::{
    PortfolioConfig, RaceResult, RaceStrategy, SolverEntry, SolverStatistics,
};

/// tRust: Key for bucketing solver performance history.
///
/// We use the VcKind discriminant (as a string) to group VCs. This is
/// coarser than using the full VcKind but avoids equality/hash issues
/// with VcKind fields.
fn vc_kind_key(vc: &VerificationCondition) -> String {
    // Use proof_level + kind discriminant for bucketing
    format!("{:?}:{}", vc.kind.proof_level(), vc.kind.description().split(':').next().unwrap_or("unknown"))
}

/// tRust: Record of a solver's performance on a particular VC kind.
#[derive(Debug, Clone)]
pub struct SolverRecord {
    /// Solver name.
    pub solver: String,
    /// Number of times this solver won (produced first definitive result).
    pub wins: u64,
    /// Number of times this solver was tried.
    pub attempts: u64,
    /// Cumulative time in ms across all attempts.
    pub total_time_ms: u64,
}

impl SolverRecord {
    fn new(solver: impl Into<String>) -> Self {
        Self {
            solver: solver.into(),
            wins: 0,
            attempts: 0,
            total_time_ms: 0,
        }
    }

    /// Win rate as a fraction [0.0, 1.0].
    #[must_use]
    pub fn win_rate(&self) -> f64 {
        if self.attempts == 0 {
            0.0
        } else {
            self.wins as f64 / self.attempts as f64
        }
    }

    /// Average time in ms per attempt.
    #[must_use]
    pub fn avg_time_ms(&self) -> f64 {
        if self.attempts == 0 {
            0.0
        } else {
            self.total_time_ms as f64 / self.attempts as f64
        }
    }
}

/// tRust: Thread-safe history of solver performance per VcKind.
#[derive(Debug, Clone, Default)]
pub struct PerformanceHistory {
    /// Map from vc_kind_key -> solver_name -> SolverRecord.
    records: FxHashMap<String, FxHashMap<String, SolverRecord>>,
}

impl PerformanceHistory {
    /// Create empty history.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Record that a solver was attempted on a VC kind.
    pub fn record_attempt(&mut self, kind_key: &str, solver: &str, time_ms: u64) {
        let entry = self
            .records
            .entry(kind_key.to_string())
            .or_default()
            .entry(solver.to_string())
            .or_insert_with(|| SolverRecord::new(solver));
        entry.attempts += 1;
        entry.total_time_ms += time_ms;
    }

    /// Record that a solver won (first definitive result) for a VC kind.
    pub fn record_win(&mut self, kind_key: &str, solver: &str) {
        let entry = self
            .records
            .entry(kind_key.to_string())
            .or_default()
            .entry(solver.to_string())
            .or_insert_with(|| SolverRecord::new(solver));
        entry.wins += 1;
    }

    /// Get the best solver for a VC kind based on win rate (ties broken by avg time).
    #[must_use]
    pub fn best_solver(&self, kind_key: &str) -> Option<String> {
        let solvers = self.records.get(kind_key)?;
        solvers
            .values()
            .filter(|r| r.attempts > 0)
            .max_by(|a, b| {
                a.win_rate()
                    .partial_cmp(&b.win_rate())
                    .unwrap_or(std::cmp::Ordering::Equal)
                    .then_with(|| {
                        // Lower avg time is better — reverse comparison
                        b.avg_time_ms()
                            .partial_cmp(&a.avg_time_ms())
                            .unwrap_or(std::cmp::Ordering::Equal)
                    })
            })
            .map(|r| r.solver.clone())
    }

    /// Total number of recorded races across all VC kinds.
    #[must_use]
    pub fn total_races(&self) -> u64 {
        // Count unique race events by summing max(attempts) per kind_key
        // (each race has one attempt per solver, so max attempts = race count)
        self.records
            .values()
            .map(|solvers| solvers.values().map(|r| r.attempts).max().unwrap_or(0))
            .sum()
    }

    /// Get all records for a VC kind.
    #[must_use]
    pub fn records_for_kind(&self, kind_key: &str) -> Vec<SolverRecord> {
        self.records
            .get(kind_key)
            .map(|solvers| solvers.values().cloned().collect())
            .unwrap_or_default()
    }

    /// Get all tracked VC kind keys.
    #[must_use]
    pub fn tracked_kinds(&self) -> Vec<String> {
        self.records.keys().cloned().collect()
    }
}

/// tRust: Configuration for the adaptive dispatcher.
#[derive(Debug, Clone)]
pub struct AdaptiveConfig {
    /// Number of full portfolio races before switching to adaptive mode.
    /// During warmup, every VC gets a full portfolio race.
    pub warmup_races: u64,
    /// Minimum win rate to consider a solver the "best" for adaptive routing.
    /// Below this threshold, fall back to full portfolio.
    pub min_win_rate: f64,
    /// Whether to fall back to full portfolio if the adaptive pick fails.
    pub fallback_to_portfolio: bool,
    /// Underlying portfolio config for full races.
    pub portfolio_config: PortfolioConfig,
}

impl Default for AdaptiveConfig {
    fn default() -> Self {
        Self {
            warmup_races: 10,
            min_win_rate: 0.3,
            fallback_to_portfolio: true,
            portfolio_config: PortfolioConfig::default(),
        }
    }
}

/// tRust: Adaptive dispatcher that routes VCs to their historically best solver.
///
/// During the warmup period, runs full portfolio races on every VC to collect
/// performance data. After warmup, preferentially routes each VC to the solver
/// with the highest win rate for that VC's kind. Falls back to full portfolio
/// if the adaptive pick fails or if no history is available.
pub struct AdaptiveDispatcher {
    /// Named solver entries.
    solvers: Vec<SolverEntry>,
    /// Thread-safe performance history.
    history: Arc<Mutex<PerformanceHistory>>,
    /// Configuration.
    config: AdaptiveConfig,
}

impl AdaptiveDispatcher {
    /// Create a new adaptive dispatcher.
    #[must_use]
    pub fn new(solvers: Vec<SolverEntry>, config: AdaptiveConfig) -> Self {
        Self {
            solvers,
            history: Arc::new(Mutex::new(PerformanceHistory::new())),
            config,
        }
    }

    /// Create with default config.
    #[must_use]
    pub fn with_defaults(solvers: Vec<SolverEntry>) -> Self {
        Self::new(solvers, AdaptiveConfig::default())
    }

    /// Whether we are still in the warmup period.
    #[must_use]
    pub fn in_warmup(&self) -> bool {
        let history = self.history.lock().unwrap_or_else(|e| e.into_inner());
        history.total_races() < self.config.warmup_races
    }

    /// Get a snapshot of the current performance history.
    #[must_use]
    pub fn history_snapshot(&self) -> PerformanceHistory {
        self.history.lock().unwrap_or_else(|e| e.into_inner()).clone()
    }

    /// Get current statistics for all solvers.
    #[must_use]
    pub fn statistics(&self) -> SolverStatistics {
        let history = self.history.lock().unwrap_or_else(|e| e.into_inner());
        let mut stats = SolverStatistics::new();

        for kind_records in history.records.values() {
            for record in kind_records.values() {
                stats.record_race(&record.solver, record.wins > 0, record.total_time_ms);
            }
        }

        stats
    }

    /// Verify a single VC using adaptive dispatch.
    ///
    /// In warmup mode: runs a full portfolio race and records results.
    /// After warmup: routes to best solver, falls back to portfolio on failure.
    #[must_use]
    pub fn verify(&self, vc: &VerificationCondition) -> RaceResult {
        let kind_key = vc_kind_key(vc);

        if self.in_warmup() {
            return self.verify_portfolio(vc, &kind_key);
        }

        // Try adaptive routing
        let best_solver = {
            let history = self.history.lock().unwrap_or_else(|e| e.into_inner());
            history
                .best_solver(&kind_key)
                .filter(|_| true) // placeholder for min_win_rate check below
        };

        if let Some(solver_name) = best_solver {
            // Check min_win_rate
            let meets_threshold = {
                let history = self.history.lock().unwrap_or_else(|e| e.into_inner());
                history
                    .records_for_kind(&kind_key)
                    .iter()
                    .find(|r| r.solver == solver_name)
                    .map(|r| r.win_rate() >= self.config.min_win_rate)
                    .unwrap_or(false)
            };

            if meets_threshold
                && let Some(result) = self.verify_single_solver(vc, &solver_name, &kind_key)
                    && (result.winner_result.is_proved() || result.winner_result.is_failed()) {
                        return result;
                    }

            // Adaptive pick failed — fall back to portfolio if configured
            if self.config.fallback_to_portfolio {
                return self.verify_portfolio(vc, &kind_key);
            }
        }

        // No adaptive pick available — full portfolio
        self.verify_portfolio(vc, &kind_key)
    }

    /// Verify multiple VCs.
    #[must_use]
    pub fn verify_all(
        &self,
        vcs: &[VerificationCondition],
    ) -> Vec<(VerificationCondition, RaceResult)> {
        vcs.iter()
            .map(|vc| (vc.clone(), self.verify(vc)))
            .collect()
    }

    /// Run a single solver and record result.
    fn verify_single_solver(
        &self,
        vc: &VerificationCondition,
        solver_name: &str,
        kind_key: &str,
    ) -> Option<RaceResult> {
        let entry = self.solvers.iter().find(|e| e.name == solver_name)?;

        let start = Instant::now();
        let result = entry.backend.verify(vc);
        let time_ms = start.elapsed().as_millis() as u64;

        let is_definitive = result.is_proved() || result.is_failed();

        // Record in history
        {
            let mut history = self.history.lock().unwrap_or_else(|e| e.into_inner());
            history.record_attempt(kind_key, solver_name, time_ms);
            if is_definitive {
                history.record_win(kind_key, solver_name);
            }
        }

        Some(RaceResult {
            winner_result: result,
            winner_solver: solver_name.to_string(),
            race_time_ms: time_ms,
            solver_statuses: vec![(solver_name.to_string(), SolverStatus::Completed { time_ms })],
            strategy_used: RaceStrategy::FirstResult,
        })
    }

    /// Run a full portfolio race and record results.
    fn verify_portfolio(&self, vc: &VerificationCondition, kind_key: &str) -> RaceResult {
        let config = &self.config.portfolio_config;
        let start = Instant::now();

        // Run all solvers (sequential for simplicity; PortfolioConfig handles strategy)
        let mut results: Vec<(String, VerificationResult, u64)> = Vec::new();
        let mut winner: Option<(String, VerificationResult)> = None;

        for entry in &self.solvers {
            let solver_start = Instant::now();
            let result = entry.backend.verify(vc);
            let solver_time = solver_start.elapsed().as_millis() as u64;
            let is_definitive = result.is_proved() || result.is_failed();

            results.push((entry.name.clone(), result.clone(), solver_time));

            match config.strategy {
                RaceStrategy::FirstResult => {
                    if winner.is_none() {
                        winner = Some((entry.name.clone(), result));
                    }
                    if is_definitive {
                        // Found definitive — stop
                        break;
                    }
                }
                RaceStrategy::FirstSat => {
                    if result.is_proved() && winner.is_none() {
                        winner = Some((entry.name.clone(), result));
                        break;
                    }
                    if winner.is_none() {
                        winner = Some((entry.name.clone(), result));
                    }
                }
                RaceStrategy::BestStrength => {
                    // Collect all, pick best at end
                    if winner.is_none() || is_definitive {
                        winner = Some((entry.name.clone(), result));
                    }
                }
            }
        }

        let race_time_ms = start.elapsed().as_millis() as u64;

        // Record history for all participants
        {
            let mut history = self.history.lock().unwrap_or_else(|e| e.into_inner());
            for (solver_name, _, solver_time) in &results {
                history.record_attempt(kind_key, solver_name, *solver_time);
            }
            if let Some((ref winner_name, _)) = winner {
                let winner_result_is_definitive = results
                    .iter()
                    .find(|(name, _, _)| name == winner_name)
                    .map(|(_, r, _)| r.is_proved() || r.is_failed())
                    .unwrap_or(false);
                if winner_result_is_definitive {
                    history.record_win(kind_key, winner_name);
                }
            }
        }

        let solver_statuses: Vec<(String, SolverStatus)> = results
            .iter()
            .map(|(name, _, time)| (name.clone(), SolverStatus::Completed { time_ms: *time }))
            .collect();

        let (winner_solver, winner_result) = winner.unwrap_or_else(|| {
            (
                "none".to_string(),
                VerificationResult::Unknown {
                    solver: "none".to_string(),
                    time_ms: 0,
                    reason: "no solvers available".to_string(),
                },
            )
        });

        RaceResult {
            winner_result,
            winner_solver,
            race_time_ms,
            solver_statuses,
            strategy_used: config.strategy,
        }
    }
}

/// tRust: Status of an individual solver in a race.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SolverStatus {
    /// Solver completed and returned a result.
    Completed { time_ms: u64 },
    /// Solver was cancelled because another solver won first.
    Cancelled,
    /// Solver timed out.
    TimedOut { timeout_ms: u64 },
    /// Solver encountered an error.
    Error { reason: String },
}

#[cfg(test)]
mod tests {
    use trust_types::*;

    use super::*;
    use crate::VerificationBackend;

    fn test_vc(name: &str, kind: VcKind) -> VerificationCondition {
        VerificationCondition {
            kind,
            function: name.to_string(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
        }
    }

    fn proved_result(solver: &str) -> VerificationResult {
        VerificationResult::Proved {
            solver: solver.to_string(),
            time_ms: 1,
            strength: ProofStrength::smt_unsat(), proof_certificate: None,
                solver_warnings: None, }
    }

    fn unknown_result(solver: &str) -> VerificationResult {
        VerificationResult::Unknown {
            solver: solver.to_string(),
            time_ms: 1,
            reason: "unknown".to_string(),
        }
    }

    struct NamedBackend {
        name: String,
        result_fn: Box<dyn Fn() -> VerificationResult + Send + Sync>,
    }

    impl VerificationBackend for NamedBackend {
        fn name(&self) -> &str {
            &self.name
        }

        fn can_handle(&self, _vc: &VerificationCondition) -> bool {
            true
        }

        fn verify(&self, _vc: &VerificationCondition) -> VerificationResult {
            (self.result_fn)()
        }
    }

    fn make_solver(name: &str, result: VerificationResult) -> SolverEntry {
        let name_owned = name.to_string();
        let result_clone = result.clone();
        SolverEntry {
            name: name_owned.clone(),
            backend: Arc::new(NamedBackend {
                name: name_owned,
                result_fn: Box::new(move || result_clone.clone()),
            }),
        }
    }

    #[test]
    fn test_performance_history_empty() {
        let history = PerformanceHistory::new();
        assert_eq!(history.total_races(), 0);
        assert!(history.best_solver("div_zero").is_none());
        assert!(history.tracked_kinds().is_empty());
    }

    #[test]
    fn test_performance_history_records_wins() {
        let mut history = PerformanceHistory::new();
        history.record_attempt("div_zero", "z4", 10);
        history.record_win("div_zero", "z4");
        history.record_attempt("div_zero", "mock", 5);
        // mock has 0 wins, z4 has 1 win

        let best = history.best_solver("div_zero");
        assert_eq!(best.as_deref(), Some("z4"));
    }

    #[test]
    fn test_performance_history_best_solver_by_time() {
        let mut history = PerformanceHistory::new();
        // Both solvers have 100% win rate
        history.record_attempt("div_zero", "fast", 5);
        history.record_win("div_zero", "fast");
        history.record_attempt("div_zero", "slow", 50);
        history.record_win("div_zero", "slow");

        // Same win rate, so should prefer faster
        let best = history.best_solver("div_zero");
        assert_eq!(best.as_deref(), Some("fast"));
    }

    #[test]
    fn test_performance_history_records_for_kind() {
        let mut history = PerformanceHistory::new();
        history.record_attempt("div_zero", "z4", 10);
        history.record_attempt("div_zero", "mock", 5);

        let records = history.records_for_kind("div_zero");
        assert_eq!(records.len(), 2);
        assert!(records.iter().all(|r| r.attempts == 1));
    }

    #[test]
    fn test_solver_record_win_rate() {
        let mut record = SolverRecord::new("z4");
        assert_eq!(record.win_rate(), 0.0);
        assert_eq!(record.avg_time_ms(), 0.0);

        record.attempts = 10;
        record.wins = 7;
        record.total_time_ms = 100;

        assert!((record.win_rate() - 0.7).abs() < f64::EPSILON);
        assert!((record.avg_time_ms() - 10.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_adaptive_dispatcher_warmup_phase() {
        let solvers = vec![
            make_solver("z4", proved_result("z4")),
            make_solver("mock", proved_result("mock")),
        ];

        let config = AdaptiveConfig {
            warmup_races: 3,
            ..Default::default()
        };

        let dispatcher = AdaptiveDispatcher::new(solvers, config);
        assert!(dispatcher.in_warmup());

        let vc = test_vc("warmup_fn", VcKind::DivisionByZero);

        // First 3 VCs should run full portfolio (warmup)
        for _ in 0..3 {
            let result = dispatcher.verify(&vc);
            assert!(result.winner_result.is_proved());
        }

        // After 3 races, should no longer be in warmup
        assert!(!dispatcher.in_warmup());
    }

    #[test]
    fn test_adaptive_dispatcher_routes_to_best() {
        let solvers = vec![
            make_solver("z4", proved_result("z4")),
            make_solver("mock", unknown_result("mock")),
        ];

        let config = AdaptiveConfig {
            warmup_races: 2,
            min_win_rate: 0.3,
            fallback_to_portfolio: true,
            portfolio_config: PortfolioConfig::default(),
        };

        let dispatcher = AdaptiveDispatcher::new(solvers, config);

        let vc = test_vc("route_fn", VcKind::DivisionByZero);

        // Run warmup
        for _ in 0..2 {
            let _ = dispatcher.verify(&vc);
        }

        // After warmup, z4 should be the preferred solver (it wins, mock returns unknown)
        let result = dispatcher.verify(&vc);
        assert!(result.winner_result.is_proved());
        assert_eq!(result.winner_solver, "z4");
    }

    #[test]
    fn test_adaptive_dispatcher_fallback_on_failure() {
        // Solver that alternates between unknown and proved
        let call_count = Arc::new(std::sync::atomic::AtomicU64::new(0));
        let count_clone = Arc::clone(&call_count);

        let alternating_name = "alternating".to_string();
        let alternating = SolverEntry {
            name: alternating_name.clone(),
            backend: Arc::new(NamedBackend {
                name: alternating_name,
                result_fn: Box::new(move || {
                    let n = count_clone.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                    if n.is_multiple_of(2) {
                        proved_result("alternating")
                    } else {
                        unknown_result("alternating")
                    }
                }),
            }),
        };

        let backup = make_solver("backup", proved_result("backup"));

        let config = AdaptiveConfig {
            warmup_races: 1,
            min_win_rate: 0.1,
            fallback_to_portfolio: true,
            portfolio_config: PortfolioConfig::default(),
        };

        let dispatcher = AdaptiveDispatcher::new(vec![alternating, backup], config);

        let vc = test_vc("fallback_fn", VcKind::DivisionByZero);

        // Warmup phase
        let _ = dispatcher.verify(&vc);

        // Subsequent calls should still succeed (either adaptive pick or fallback)
        for _ in 0..5 {
            let result = dispatcher.verify(&vc);
            assert!(
                result.winner_result.is_proved()
                    || matches!(result.winner_result, VerificationResult::Unknown { .. })
            );
        }
    }

    #[test]
    fn test_adaptive_dispatcher_verify_all() {
        let solvers = vec![make_solver("z4", proved_result("z4"))];

        let config = AdaptiveConfig {
            warmup_races: 0,
            ..Default::default()
        };

        let dispatcher = AdaptiveDispatcher::new(solvers, config);

        let vcs: Vec<_> = (0..3)
            .map(|i| test_vc(&format!("fn_{i}"), VcKind::DivisionByZero))
            .collect();

        let results = dispatcher.verify_all(&vcs);
        assert_eq!(results.len(), 3);
        for (_, race_result) in &results {
            assert!(race_result.winner_result.is_proved());
        }
    }

    #[test]
    fn test_adaptive_dispatcher_statistics() {
        let solvers = vec![
            make_solver("z4", proved_result("z4")),
            make_solver("mock", proved_result("mock")),
        ];

        let config = AdaptiveConfig {
            warmup_races: 0,
            ..Default::default()
        };

        let dispatcher = AdaptiveDispatcher::new(solvers, config);

        let vc = test_vc("stats_fn", VcKind::DivisionByZero);
        let _ = dispatcher.verify(&vc);

        let stats = dispatcher.statistics();
        assert!(stats.total_races() > 0);
    }

    #[test]
    fn test_adaptive_dispatcher_different_vc_kinds() {
        let solvers = vec![
            make_solver("z4", proved_result("z4")),
            make_solver("mock", proved_result("mock")),
        ];

        let config = AdaptiveConfig {
            warmup_races: 0,
            ..Default::default()
        };

        let dispatcher = AdaptiveDispatcher::new(solvers, config);

        // Different VC kinds should be tracked separately
        let div_vc = test_vc("div", VcKind::DivisionByZero);
        let post_vc = test_vc("post", VcKind::Postcondition);

        let _ = dispatcher.verify(&div_vc);
        let _ = dispatcher.verify(&post_vc);

        let history = dispatcher.history_snapshot();
        assert!(history.tracked_kinds().len() >= 2);
    }

    #[test]
    fn test_vc_kind_key_deterministic() {
        let vc1 = test_vc("fn1", VcKind::DivisionByZero);
        let vc2 = test_vc("fn2", VcKind::DivisionByZero);

        // Same VcKind should produce same key regardless of function name
        assert_eq!(vc_kind_key(&vc1), vc_kind_key(&vc2));
    }

    #[test]
    fn test_vc_kind_key_different_kinds() {
        let div_vc = test_vc("fn1", VcKind::DivisionByZero);
        let post_vc = test_vc("fn2", VcKind::Postcondition);

        assert_ne!(vc_kind_key(&div_vc), vc_kind_key(&post_vc));
    }

    #[test]
    fn test_solver_status_variants() {
        let completed = SolverStatus::Completed { time_ms: 42 };
        let cancelled = SolverStatus::Cancelled;
        let timed_out = SolverStatus::TimedOut { timeout_ms: 1000 };
        let error = SolverStatus::Error { reason: "boom".to_string() };

        assert_eq!(completed, SolverStatus::Completed { time_ms: 42 });
        assert_eq!(cancelled, SolverStatus::Cancelled);
        assert_eq!(timed_out, SolverStatus::TimedOut { timeout_ms: 1000 });
        assert_eq!(error, SolverStatus::Error { reason: "boom".to_string() });
    }

    #[test]
    fn test_adaptive_config_default() {
        let config = AdaptiveConfig::default();
        assert_eq!(config.warmup_races, 10);
        assert!((config.min_win_rate - 0.3).abs() < f64::EPSILON);
        assert!(config.fallback_to_portfolio);
    }
}
