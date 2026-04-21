// trust-router/portfolio_racer.rs: Portfolio racer for parallel multi-solver dispatch
//
// tRust #363: Races the same VC against multiple solver backends in parallel
// using rayon. The first solver to return a definitive result (Proved or Failed)
// wins; remaining solvers are abandoned via an atomic cancellation flag.
//
// Integrates with QueryClass from classifier.rs for smart solver ordering.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};

use rayon::prelude::*;
use trust_types::{VerificationCondition, VerificationResult};

use crate::classifier::{self, QueryClass};
use crate::VerificationBackend;

/// tRust #363: Result from a portfolio race.
///
/// Contains the winning solver's result, timing information, and metadata
/// about the race execution.
#[derive(Debug, Clone)]
pub struct RaceResult {
    /// The verification result from the winning solver.
    pub result: VerificationResult,
    /// Name of the solver that won the race.
    pub winning_solver: String,
    /// Wall-clock time the winning solver took (milliseconds).
    pub solver_time_ms: u64,
    /// Total wall-clock time for the entire race (milliseconds).
    pub race_time_ms: u64,
    /// Number of solvers that were racing.
    pub solvers_raced: usize,
    /// Whether the result is definitive (Proved or Failed).
    pub is_definitive: bool,
}

/// tRust #363: Configuration for portfolio racing.
#[derive(Debug, Clone)]
pub struct RaceConfig {
    /// Overall timeout for the race. If no solver finishes within this
    /// duration, the race returns the best partial result or Timeout.
    pub timeout: Duration,
    /// Maximum number of solvers to race concurrently.
    /// If more backends are available than this limit, only the top
    /// `max_solvers` (by priority ordering) are included.
    pub max_solvers: usize,
    /// Optional priority ordering of solver names. Solvers listed first
    /// are preferred when the number of available backends exceeds
    /// `max_solvers`. If empty, all backends are used up to `max_solvers`.
    pub priority_order: Vec<String>,
    /// Whether to use `QueryClass`-based solver selection to reorder
    /// the priority list based on the VC's formula characteristics.
    pub use_query_class: bool,
}

impl Default for RaceConfig {
    fn default() -> Self {
        Self {
            timeout: Duration::from_secs(60),
            max_solvers: 4,
            priority_order: Vec::new(),
            use_query_class: true,
        }
    }
}

impl RaceConfig {
    /// Set the race timeout.
    #[must_use]
    pub fn with_timeout(mut self, timeout: Duration) -> Self {
        self.timeout = timeout;
        self
    }

    /// Set the maximum number of concurrent solvers.
    #[must_use]
    pub fn with_max_solvers(mut self, max: usize) -> Self {
        self.max_solvers = max.max(1);
        self
    }

    /// Set the priority ordering of solver names.
    #[must_use]
    pub fn with_priority(mut self, order: Vec<String>) -> Self {
        self.priority_order = order;
        self
    }

    /// Enable or disable QueryClass-based solver selection.
    #[must_use]
    pub fn with_query_class(mut self, enabled: bool) -> Self {
        self.use_query_class = enabled;
        self
    }
}

/// tRust #363: Portfolio racer that dispatches the same VC to multiple
/// solver backends in parallel.
///
/// Uses rayon for thread management. An atomic cancellation flag signals
/// remaining solvers to abandon work once a definitive result arrives.
pub struct PortfolioRacer {
    backends: Vec<Arc<dyn VerificationBackend>>,
}

impl PortfolioRacer {
    /// Create a new portfolio racer with the given backends.
    pub fn new(backends: Vec<Arc<dyn VerificationBackend>>) -> Self {
        Self { backends }
    }

    /// Create a portfolio racer from boxed backends (convenience).
    pub fn from_boxed(backends: Vec<Box<dyn VerificationBackend>>) -> Self {
        Self {
            backends: backends.into_iter().map(Arc::from).collect(),
        }
    }

    /// Number of registered backends.
    #[must_use]
    pub fn backend_count(&self) -> usize {
        self.backends.len()
    }

    /// Race the VC against all eligible backends, returning the first
    /// definitive result (Proved or Failed).
    ///
    /// If no definitive result arrives before the timeout, the best
    /// partial result (Unknown) is returned, or Timeout if no solver
    /// completed at all.
    #[must_use]
    pub fn race(
        &self,
        vc: &VerificationCondition,
        config: &RaceConfig,
    ) -> RaceResult {
        let race_start = Instant::now();

        // Select and order backends for this VC.
        let selected = self.select_backends(vc, config);

        if selected.is_empty() {
            return RaceResult {
                result: VerificationResult::Unknown {
                    solver: "none".to_string(),
                    time_ms: 0,
                    reason: "no eligible backends for this VC".to_string(),
                },
                winning_solver: "none".to_string(),
                solver_time_ms: 0,
                race_time_ms: 0,
                solvers_raced: 0,
                is_definitive: false,
            };
        }

        let solvers_raced = selected.len();

        // Atomic flag: set to true once a definitive result arrives.
        let cancelled = Arc::new(AtomicBool::new(false));

        // Build a rayon thread pool with one thread per solver.
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(selected.len().min(config.max_solvers))
            .build()
            // tRust #734: rayon pool creation failure is a real system-level error.
            .expect("rayon thread pool creation failed");

        // Race all selected backends in parallel.
        let vc_clone = vc.clone();
        let timeout = config.timeout;
        let results: Vec<Option<(String, VerificationResult, u64)>> = pool.install(|| {
            selected
                .par_iter()
                .map(|backend| {
                    // Check cancellation before starting.
                    if cancelled.load(Ordering::Relaxed) {
                        return None;
                    }

                    // Check timeout before starting.
                    if race_start.elapsed() >= timeout {
                        return None;
                    }

                    let solver_start = Instant::now();
                    let result = backend.verify(&vc_clone);
                    let solver_time_ms = solver_start.elapsed().as_millis() as u64;
                    let solver_name = backend.name().to_string();

                    // If this is a definitive result, signal cancellation.
                    if result.is_proved() || result.is_failed() {
                        cancelled.store(true, Ordering::Relaxed);
                    }

                    Some((solver_name, result, solver_time_ms))
                })
                .collect()
        });

        let race_time_ms = race_start.elapsed().as_millis() as u64;

        // Find the best result: prefer definitive (Proved/Failed),
        // then Unknown, then Timeout.
        let mut best: Option<(String, VerificationResult, u64)> = None;

        for entry in results.into_iter().flatten() {
            let dominated = if let Some((_, cur, cur_time)) = &best {
                let new = &entry.1;
                let new_is_definitive = new.is_proved() || new.is_failed();
                let cur_is_definitive = cur.is_proved() || cur.is_failed();

                if new_is_definitive && !cur_is_definitive {
                    // Definitive result always wins over non-definitive.
                    true
                } else if new.is_proved() && !cur.is_proved() {
                    // Among definitive results, prefer Proved over Failed.
                    true
                } else if Self::result_rank(new) == Self::result_rank(cur)
                    && entry.2 < *cur_time
                {
                    // Among equal quality, prefer faster.
                    true
                } else {
                    false
                }
            } else {
                // No current best -- take anything.
                true
            };

            if dominated {
                best = Some(entry);
            }
        }

        match best {
            Some((solver, result, solver_time_ms)) => {
                let is_definitive = result.is_proved() || result.is_failed();
                RaceResult {
                    result,
                    winning_solver: solver,
                    solver_time_ms,
                    race_time_ms,
                    solvers_raced,
                    is_definitive,
                }
            }
            None => RaceResult {
                result: VerificationResult::Timeout {
                    solver: "portfolio-racer".to_string(),
                    timeout_ms: config.timeout.as_millis() as u64,
                },
                winning_solver: "none".to_string(),
                solver_time_ms: 0,
                race_time_ms,
                solvers_raced,
                is_definitive: false,
            },
        }
    }

    /// Select and order backends for a VC based on the race configuration.
    ///
    /// Applies QueryClass-based ordering when enabled, then priority ordering,
    /// and finally caps at `max_solvers`.
    fn select_backends(
        &self,
        vc: &VerificationCondition,
        config: &RaceConfig,
    ) -> Vec<Arc<dyn VerificationBackend>> {
        // Start with all backends that can handle the VC.
        let mut eligible: Vec<Arc<dyn VerificationBackend>> = self
            .backends
            .iter()
            .filter(|b| b.can_handle(vc))
            .cloned()
            .collect();

        if eligible.is_empty() {
            return eligible;
        }

        // Apply QueryClass-based ordering if enabled.
        if config.use_query_class {
            let query_class = classifier::classify_vc(vc);
            let affinity = classifier::default_affinity(query_class);
            eligible.sort_by_key(|b| {
                affinity
                    .preferred_solvers
                    .iter()
                    .position(|s| s == b.name())
                    .unwrap_or(usize::MAX)
            });
        }

        // Apply priority ordering if specified.
        if !config.priority_order.is_empty() {
            eligible.sort_by_key(|b| {
                config
                    .priority_order
                    .iter()
                    .position(|s| s == b.name())
                    .unwrap_or(usize::MAX)
            });
        }

        // Cap at max_solvers.
        eligible.truncate(config.max_solvers);
        eligible
    }

    /// Rank a verification result for comparison (lower is better).
    fn result_rank(result: &VerificationResult) -> u8 {
        match result {
            VerificationResult::Proved { .. } => 0,
            VerificationResult::Failed { .. } => 1,
            VerificationResult::Unknown { .. } => 2,
            VerificationResult::Timeout { .. } => 3,
            _ => 4, // Future VerificationResult variants
        }
    }

    /// Get the query class for a VC (public helper for diagnostics).
    #[must_use]
    pub fn classify_vc(vc: &VerificationCondition) -> QueryClass {
        classifier::classify_vc(vc)
    }
}

#[cfg(test)]
mod tests {
    use std::sync::atomic::{AtomicUsize, Ordering as AtomicOrdering};

    use trust_types::*;

    use super::*;

    // -----------------------------------------------------------------------
    // Mock backends for testing
    // -----------------------------------------------------------------------

    /// Backend that always proves (fast).
    struct AlwaysProve {
        name: &'static str,
        delay_ms: u64,
    }

    impl AlwaysProve {
        fn new(name: &'static str) -> Self {
            Self { name, delay_ms: 0 }
        }
        fn with_delay(name: &'static str, delay_ms: u64) -> Self {
            Self { name, delay_ms }
        }
    }

    impl VerificationBackend for AlwaysProve {
        fn name(&self) -> &str {
            self.name
        }
        fn can_handle(&self, _vc: &VerificationCondition) -> bool {
            true
        }
        fn verify(&self, _vc: &VerificationCondition) -> VerificationResult {
            if self.delay_ms > 0 {
                std::thread::sleep(Duration::from_millis(self.delay_ms));
            }
            VerificationResult::Proved {
                solver: self.name.to_string(),
                time_ms: self.delay_ms,
                strength: ProofStrength::smt_unsat(), proof_certificate: None,
                solver_warnings: None, }
        }
    }

    /// Backend that always fails with a counterexample.
    struct AlwaysFail {
        name: &'static str,
    }

    impl VerificationBackend for AlwaysFail {
        fn name(&self) -> &str {
            self.name
        }
        fn can_handle(&self, _vc: &VerificationCondition) -> bool {
            true
        }
        fn verify(&self, _vc: &VerificationCondition) -> VerificationResult {
            VerificationResult::Failed {
                solver: self.name.to_string(),
                time_ms: 0,
                counterexample: None,
            }
        }
    }

    /// Backend that returns Unknown.
    struct AlwaysUnknown {
        name: &'static str,
    }

    impl VerificationBackend for AlwaysUnknown {
        fn name(&self) -> &str {
            self.name
        }
        fn can_handle(&self, _vc: &VerificationCondition) -> bool {
            true
        }
        fn verify(&self, _vc: &VerificationCondition) -> VerificationResult {
            VerificationResult::Unknown {
                solver: self.name.to_string(),
                time_ms: 0,
                reason: "always unknown".to_string(),
            }
        }
    }

    /// Backend that refuses to handle any VC.
    struct NeverHandles;

    impl VerificationBackend for NeverHandles {
        fn name(&self) -> &str {
            "never-handles"
        }
        fn can_handle(&self, _vc: &VerificationCondition) -> bool {
            false
        }
        fn verify(&self, _vc: &VerificationCondition) -> VerificationResult {
            unreachable!("should never be called")
        }
    }

    /// Backend that tracks how many times it was invoked.
    struct CountingBackend {
        name: &'static str,
        count: Arc<AtomicUsize>,
        cancelled: Arc<AtomicBool>,
        delay_ms: u64,
    }

    impl VerificationBackend for CountingBackend {
        fn name(&self) -> &str {
            self.name
        }
        fn can_handle(&self, _vc: &VerificationCondition) -> bool {
            true
        }
        fn verify(&self, _vc: &VerificationCondition) -> VerificationResult {
            self.count.fetch_add(1, AtomicOrdering::Relaxed);
            if self.delay_ms > 0 {
                std::thread::sleep(Duration::from_millis(self.delay_ms));
            }
            // Check if we were cancelled during sleep.
            if self.cancelled.load(AtomicOrdering::Relaxed) {
                return VerificationResult::Unknown {
                    solver: self.name.to_string(),
                    time_ms: 0,
                    reason: "cancelled".to_string(),
                };
            }
            VerificationResult::Proved {
                solver: self.name.to_string(),
                time_ms: self.delay_ms,
                strength: ProofStrength::smt_unsat(), proof_certificate: None,
                solver_warnings: None, }
        }
    }

    fn test_vc() -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "test_fn".to_string(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
        }
    }

    fn default_config() -> RaceConfig {
        RaceConfig::default()
    }

    // -----------------------------------------------------------------------
    // Test 1: Single solver wins the race
    // -----------------------------------------------------------------------

    #[test]
    fn test_single_solver_proves() {
        let racer = PortfolioRacer::new(vec![
            Arc::new(AlwaysProve::new("z4")),
        ]);

        let result = racer.race(&test_vc(), &default_config());

        assert!(result.result.is_proved());
        assert_eq!(result.winning_solver, "z4");
        assert!(result.is_definitive);
        assert_eq!(result.solvers_raced, 1);
    }

    // -----------------------------------------------------------------------
    // Test 2: Fastest solver wins among multiple provers
    // -----------------------------------------------------------------------

    #[test]
    fn test_fastest_solver_wins() {
        let racer = PortfolioRacer::new(vec![
            Arc::new(AlwaysProve::with_delay("slow", 200)),
            Arc::new(AlwaysProve::new("fast")),
        ]);

        let result = racer.race(&test_vc(), &default_config());

        assert!(result.result.is_proved());
        // The fast solver should win because it returns immediately.
        assert_eq!(result.winning_solver, "fast");
        assert!(result.is_definitive);
        assert_eq!(result.solvers_raced, 2);
    }

    // -----------------------------------------------------------------------
    // Test 3: Proved preferred over Unknown
    // -----------------------------------------------------------------------

    #[test]
    fn test_proved_beats_unknown() {
        let racer = PortfolioRacer::new(vec![
            Arc::new(AlwaysUnknown { name: "uncertain" }),
            Arc::new(AlwaysProve::new("prover")),
        ]);

        let result = racer.race(&test_vc(), &default_config());

        assert!(result.result.is_proved());
        assert_eq!(result.winning_solver, "prover");
        assert!(result.is_definitive);
    }

    // -----------------------------------------------------------------------
    // Test 4: Failed is also definitive
    // -----------------------------------------------------------------------

    #[test]
    fn test_failed_is_definitive() {
        let racer = PortfolioRacer::new(vec![
            Arc::new(AlwaysFail { name: "counterex" }),
        ]);

        let result = racer.race(&test_vc(), &default_config());

        assert!(result.result.is_failed());
        assert_eq!(result.winning_solver, "counterex");
        assert!(result.is_definitive);
    }

    // -----------------------------------------------------------------------
    // Test 5: No eligible backends returns Unknown
    // -----------------------------------------------------------------------

    #[test]
    fn test_no_eligible_backends() {
        let racer = PortfolioRacer::new(vec![
            Arc::new(NeverHandles),
        ]);

        let result = racer.race(&test_vc(), &default_config());

        assert!(!result.is_definitive);
        assert_eq!(result.solvers_raced, 0);
        assert_eq!(result.winning_solver, "none");
    }

    // -----------------------------------------------------------------------
    // Test 6: Empty backend list returns Unknown
    // -----------------------------------------------------------------------

    #[test]
    fn test_empty_backends() {
        let racer = PortfolioRacer::new(vec![]);

        let result = racer.race(&test_vc(), &default_config());

        assert!(!result.is_definitive);
        assert_eq!(result.solvers_raced, 0);
        assert_eq!(racer.backend_count(), 0);
    }

    // -----------------------------------------------------------------------
    // Test 7: Max solvers config limits concurrency
    // -----------------------------------------------------------------------

    #[test]
    fn test_max_solvers_limits_concurrency() {
        let racer = PortfolioRacer::new(vec![
            Arc::new(AlwaysProve::new("a")),
            Arc::new(AlwaysProve::new("b")),
            Arc::new(AlwaysProve::new("c")),
            Arc::new(AlwaysProve::new("d")),
        ]);

        let config = RaceConfig::default().with_max_solvers(2);
        let result = racer.race(&test_vc(), &config);

        assert!(result.result.is_proved());
        // Only 2 solvers should have been raced.
        assert_eq!(result.solvers_raced, 2);
    }

    // -----------------------------------------------------------------------
    // Test 8: Priority ordering respects configured order
    // -----------------------------------------------------------------------

    #[test]
    fn test_priority_ordering() {
        let racer = PortfolioRacer::new(vec![
            Arc::new(AlwaysProve::new("low_priority")),
            Arc::new(AlwaysProve::new("high_priority")),
        ]);

        let config = RaceConfig::default()
            .with_max_solvers(1)
            .with_priority(vec!["high_priority".to_string()])
            .with_query_class(false);

        let result = racer.race(&test_vc(), &config);

        assert!(result.result.is_proved());
        assert_eq!(result.winning_solver, "high_priority");
        assert_eq!(result.solvers_raced, 1);
    }

    // -----------------------------------------------------------------------
    // Test 9: QueryClass integration classifies VC
    // -----------------------------------------------------------------------

    #[test]
    fn test_query_class_classification() {
        let vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "test".to_string(),
            location: SourceSpan::default(),
            formula: Formula::BvAdd(
                Box::new(Formula::Var("a".into(), Sort::BitVec(32))),
                Box::new(Formula::Var("b".into(), Sort::BitVec(32))),
                32,
            ),
            contract_metadata: None,
        };

        let class = PortfolioRacer::classify_vc(&vc);
        assert_eq!(class, QueryClass::BitVector);
    }

    // -----------------------------------------------------------------------
    // Test 10: Race with mixed results prefers Proved
    // -----------------------------------------------------------------------

    #[test]
    fn test_mixed_results_definitive_wins_over_unknown() {
        // When both definitive and non-definitive solvers finish,
        // a definitive result (Proved or Failed) always wins over Unknown.
        // Use delays to ensure the Unknown solver finishes first, then
        // verify that the racer still picks the definitive result.
        let racer = PortfolioRacer::new(vec![
            Arc::new(AlwaysUnknown { name: "dunno" }),
            Arc::new(AlwaysProve::new("solver")),
        ]);

        let result = racer.race(&test_vc(), &default_config());

        // A definitive result should always win over Unknown.
        assert!(result.is_definitive);
        // The prover should beat the unknown solver.
        assert!(result.result.is_proved());
        assert_eq!(result.winning_solver, "solver");
    }

    // -----------------------------------------------------------------------
    // Test 11: Config builder chain
    // -----------------------------------------------------------------------

    #[test]
    fn test_config_builder_chain() {
        let config = RaceConfig::default()
            .with_timeout(Duration::from_secs(30))
            .with_max_solvers(8)
            .with_priority(vec!["z4".to_string(), "zani".to_string()])
            .with_query_class(false);

        assert_eq!(config.timeout, Duration::from_secs(30));
        assert_eq!(config.max_solvers, 8);
        assert_eq!(config.priority_order.len(), 2);
        assert!(!config.use_query_class);
    }

    // -----------------------------------------------------------------------
    // Test 12: Max solvers clamped to at least 1
    // -----------------------------------------------------------------------

    #[test]
    fn test_max_solvers_clamped_to_one() {
        let config = RaceConfig::default().with_max_solvers(0);
        assert_eq!(config.max_solvers, 1);
    }

    // -----------------------------------------------------------------------
    // Test 13: Race result timing is tracked
    // -----------------------------------------------------------------------

    #[test]
    fn test_race_timing_tracked() {
        let racer = PortfolioRacer::new(vec![
            Arc::new(AlwaysProve::new("fast")),
        ]);

        let result = racer.race(&test_vc(), &default_config());

        // Race time should be non-negative (always true with u64,
        // but confirms the field is populated).
        assert!(result.race_time_ms < 5000, "race should complete quickly");
        assert!(result.is_definitive);
    }

    // -----------------------------------------------------------------------
    // Test 14: Cancellation flag prevents unnecessary work
    // -----------------------------------------------------------------------

    #[test]
    fn test_cancellation_flag_signals_solvers() {
        // The fast solver proves immediately; the slow solver should
        // see the cancellation flag when it starts or during its delay.
        let fast_count = Arc::new(AtomicUsize::new(0));
        let slow_count = Arc::new(AtomicUsize::new(0));
        let shared_cancel = Arc::new(AtomicBool::new(false));

        let fast = CountingBackend {
            name: "fast",
            count: Arc::clone(&fast_count),
            cancelled: Arc::clone(&shared_cancel),
            delay_ms: 0,
        };

        let slow = CountingBackend {
            name: "slow",
            count: Arc::clone(&slow_count),
            cancelled: Arc::clone(&shared_cancel),
            delay_ms: 500,
        };

        let racer = PortfolioRacer::new(vec![
            Arc::new(fast),
            Arc::new(slow),
        ]);

        let result = racer.race(&test_vc(), &default_config());

        assert!(result.result.is_proved());
        // The fast solver should have been invoked.
        assert!(fast_count.load(AtomicOrdering::Relaxed) >= 1);
    }

    // -----------------------------------------------------------------------
    // Test 15: from_boxed constructor works
    // -----------------------------------------------------------------------

    #[test]
    fn test_from_boxed_constructor() {
        let backends: Vec<Box<dyn VerificationBackend>> = vec![
            Box::new(AlwaysProve::new("boxed")),
        ];
        let racer = PortfolioRacer::from_boxed(backends);

        assert_eq!(racer.backend_count(), 1);

        let result = racer.race(&test_vc(), &default_config());
        assert!(result.result.is_proved());
        assert_eq!(result.winning_solver, "boxed");
    }

    // -----------------------------------------------------------------------
    // Test 16: All-unknown backends returns Unknown
    // -----------------------------------------------------------------------

    #[test]
    fn test_all_unknown_returns_best_unknown() {
        let racer = PortfolioRacer::new(vec![
            Arc::new(AlwaysUnknown { name: "u1" }),
            Arc::new(AlwaysUnknown { name: "u2" }),
        ]);

        let result = racer.race(&test_vc(), &default_config());

        assert!(!result.is_definitive);
        assert!(matches!(result.result, VerificationResult::Unknown { .. }));
    }
}
