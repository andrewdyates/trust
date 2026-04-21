// trust-router/portfolio/tests.rs: Tests for portfolio racing and verification dispatch
//
// Extracted from mod.rs for readability (#736).
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::sync::Arc;
use std::time::Duration;

use trust_types::*;

use super::*;
use crate::classifier::QueryClass;

/// Helper: create a test VC.
fn test_vc(name: &str) -> VerificationCondition {
    VerificationCondition {
        kind: VcKind::Temporal { property: "always safe".to_string() },
        function: name.to_string(),
        location: SourceSpan::default(),
        formula: Formula::Bool(false),
        contract_metadata: None,
    }
}

/// A mock backend that returns a specific result after a configurable delay.
struct DelayedBackend {
    name: &'static str,
    delay: Duration,
    result_fn: Box<dyn Fn() -> VerificationResult + Send + Sync>,
}

impl crate::VerificationBackend for DelayedBackend {
    fn name(&self) -> &str {
        self.name
    }

    fn role(&self) -> crate::BackendRole {
        crate::BackendRole::Temporal
    }

    fn can_handle(&self, _vc: &VerificationCondition) -> bool {
        true
    }

    fn verify(&self, _vc: &VerificationCondition) -> VerificationResult {
        std::thread::sleep(self.delay);
        (self.result_fn)()
    }
}

fn proved_result(solver: &str) -> VerificationResult {
    VerificationResult::Proved {
        solver: solver.to_string(),
        time_ms: 0,
        strength: ProofStrength::inductive(), proof_certificate: None,
            solver_warnings: None, }
}

fn failed_result(solver: &str) -> VerificationResult {
    VerificationResult::Failed {
        solver: solver.to_string(),
        time_ms: 0,
        counterexample: None,
    }
}

fn unknown_result(solver: &str) -> VerificationResult {
    VerificationResult::Unknown {
        solver: solver.to_string(),
        time_ms: 0,
        reason: "unknown".to_string(),
    }
}

#[test]
fn test_portfolio_race_fastest_wins() {
    // Fast backend proves in 10ms, slow backend in 200ms.
    let fast: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "fast-prover",
        delay: Duration::from_millis(10),
        result_fn: Box::new(|| proved_result("fast-prover")),
    });
    let slow: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "slow-prover",
        delay: Duration::from_millis(200),
        result_fn: Box::new(|| proved_result("slow-prover")),
    });

    let lanes = vec![
        PortfolioLane { strategy: PortfolioStrategy::Bmc, backend: fast },
        PortfolioLane { strategy: PortfolioStrategy::Ic3Pdr, backend: slow },
    ];

    let result = race(&test_vc("race_test"), lanes).expect("should get a result");
    assert!(result.is_definitive());
    assert_eq!(result.winning_strategy, PortfolioStrategy::Bmc);
    assert_eq!(result.result.solver_name(), "fast-prover");
    assert_eq!(result.total_lanes, 2);
}

#[test]
fn test_portfolio_race_counterexample_wins() {
    // One backend finds a counterexample fast, another would prove it slowly.
    let cex: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "bmc-cex",
        delay: Duration::from_millis(10),
        result_fn: Box::new(|| failed_result("bmc-cex")),
    });
    let prover: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "slow-ic3",
        delay: Duration::from_millis(200),
        result_fn: Box::new(|| proved_result("slow-ic3")),
    });

    let lanes = vec![
        PortfolioLane { strategy: PortfolioStrategy::Bmc, backend: cex },
        PortfolioLane { strategy: PortfolioStrategy::Ic3Pdr, backend: prover },
    ];

    let result = race(&test_vc("cex_test"), lanes).expect("should get a result");
    assert!(result.result.is_failed());
    assert_eq!(result.winning_strategy, PortfolioStrategy::Bmc);
}

#[test]
fn test_portfolio_race_unknown_fallback() {
    // All backends return Unknown — should still get a result.
    let b1: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "unk1",
        delay: Duration::from_millis(5),
        result_fn: Box::new(|| unknown_result("unk1")),
    });
    let b2: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "unk2",
        delay: Duration::from_millis(10),
        result_fn: Box::new(|| unknown_result("unk2")),
    });

    let lanes = vec![
        PortfolioLane { strategy: PortfolioStrategy::Bfs, backend: b1 },
        PortfolioLane { strategy: PortfolioStrategy::KInduction, backend: b2 },
    ];

    let result = race(&test_vc("unk_test"), lanes).expect("should get fallback");
    assert!(!result.is_definitive());
    assert!(matches!(result.result, VerificationResult::Unknown { .. }));
}

#[test]
fn test_portfolio_race_empty_lanes() {
    let result = race(&test_vc("empty"), vec![]);
    assert!(result.is_none());
}

#[test]
fn test_portfolio_race_single_lane() {
    let backend: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "solo",
        delay: Duration::ZERO,
        result_fn: Box::new(|| proved_result("solo")),
    });

    let lanes = vec![PortfolioLane {
        strategy: PortfolioStrategy::Structural,
        backend,
    }];

    let result = race(&test_vc("solo_test"), lanes).expect("should get a result");
    assert!(result.is_definitive());
    assert_eq!(result.winning_strategy, PortfolioStrategy::Structural);
    assert_eq!(result.total_lanes, 1);
}

#[test]
fn test_portfolio_racer_struct() {
    let backend: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "racer-backend",
        delay: Duration::ZERO,
        result_fn: Box::new(|| proved_result("racer-backend")),
    });

    let racer = PortfolioRacer::new(vec![
        (PortfolioStrategy::Bmc, Arc::clone(&backend)),
        (PortfolioStrategy::Bfs, Arc::clone(&backend)),
        (PortfolioStrategy::Ic3Pdr, backend),
    ]);

    assert_eq!(racer.lane_count(), 3);

    let result = racer.race(&test_vc("racer_test")).expect("should get a result");
    assert!(result.is_definitive());
    assert_eq!(result.total_lanes, 3);
}

#[test]
fn test_portfolio_racer_race_all() {
    let backend: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "batch",
        delay: Duration::ZERO,
        result_fn: Box::new(|| proved_result("batch")),
    });

    let racer = PortfolioRacer::new(vec![
        (PortfolioStrategy::Bmc, Arc::clone(&backend)),
        (PortfolioStrategy::Ic3Pdr, backend),
    ]);

    let vcs: Vec<_> = (0..3).map(|i| test_vc(&format!("fn_{i}"))).collect();
    let results = racer.race_all(&vcs);
    assert_eq!(results.len(), 3);
    for (vc, pr) in &results {
        assert!(pr.is_definitive());
        assert!(vc.function.starts_with("fn_"));
    }
}

#[test]
fn test_adaptive_selection_small_state_space() {
    let strategies = select_strategies(StateSpaceEstimate::Small);
    assert_eq!(strategies[0], PortfolioStrategy::Bfs);
    assert_eq!(strategies[1], PortfolioStrategy::Structural);
    assert_eq!(strategies.len(), 5);
}

#[test]
fn test_adaptive_selection_large_state_space() {
    let strategies = select_strategies(StateSpaceEstimate::Large);
    assert_eq!(strategies[0], PortfolioStrategy::Ic3Pdr);
    assert_eq!(strategies[1], PortfolioStrategy::KInduction);
}

#[test]
fn test_adaptive_selection_unknown() {
    let strategies = select_strategies(StateSpaceEstimate::Unknown);
    // Unknown should include all strategies
    assert_eq!(strategies.len(), 5);
}

#[test]
fn test_adaptive_racer_construction() {
    let backend: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "adaptive",
        delay: Duration::ZERO,
        result_fn: Box::new(|| proved_result("adaptive")),
    });

    let racer = PortfolioRacer::adaptive(StateSpaceEstimate::Small, backend);
    assert_eq!(racer.lane_count(), 5);

    let result = racer.race(&test_vc("adaptive_test")).expect("should get a result");
    assert!(result.is_definitive());
}

#[test]
fn test_strategy_names() {
    assert_eq!(PortfolioStrategy::Bmc.name(), "bmc");
    assert_eq!(PortfolioStrategy::Bfs.name(), "bfs");
    assert_eq!(PortfolioStrategy::Ic3Pdr.name(), "ic3pdr");
    assert_eq!(PortfolioStrategy::KInduction.name(), "k-induction");
    assert_eq!(PortfolioStrategy::Structural.name(), "structural");
}

#[test]
fn test_strategy_proof_strengths() {
    assert!(PortfolioStrategy::Bmc.proof_strength().is_bounded());
    assert_eq!(PortfolioStrategy::Ic3Pdr.proof_strength(), ProofStrength::inductive());
    assert_eq!(PortfolioStrategy::Structural.proof_strength(), ProofStrength::deductive());
}

#[test]
fn test_portfolio_race_cancellation_flag_set() {
    let fast: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "instant",
        delay: Duration::from_millis(5),
        result_fn: Box::new(|| proved_result("instant")),
    });
    let slow: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "moderate",
        delay: Duration::from_millis(200),
        result_fn: Box::new(|| proved_result("moderate")),
    });

    let lanes = vec![
        PortfolioLane { strategy: PortfolioStrategy::Bmc, backend: fast },
        PortfolioLane { strategy: PortfolioStrategy::Ic3Pdr, backend: slow },
    ];

    let result = race(&test_vc("timing_test"), lanes).expect("should get a result");

    assert!(result.is_definitive());
    assert_eq!(result.winning_strategy, PortfolioStrategy::Bmc);
    assert_eq!(result.result.solver_name(), "instant");
}

#[test]
fn test_portfolio_definitive_vs_nondefinitive() {
    let fast_unknown: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "fast-unknown",
        delay: Duration::from_millis(5),
        result_fn: Box::new(|| unknown_result("fast-unknown")),
    });
    let slow_proved: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "slow-proved",
        delay: Duration::from_millis(50),
        result_fn: Box::new(|| proved_result("slow-proved")),
    });

    let lanes = vec![
        PortfolioLane { strategy: PortfolioStrategy::Bfs, backend: fast_unknown },
        PortfolioLane { strategy: PortfolioStrategy::Ic3Pdr, backend: slow_proved },
    ];

    let result = race(&test_vc("mixed_test"), lanes).expect("should get a result");
    assert!(result.is_definitive());
    assert_eq!(result.winning_strategy, PortfolioStrategy::Ic3Pdr);
}

// -----------------------------------------------------------------------
// DispatchMode / PortfolioRunner tests (#68)
// -----------------------------------------------------------------------

/// Helper: create a test VC with a specific kind.
fn vc_with_kind(name: &str, kind: VcKind) -> VerificationCondition {
    VerificationCondition {
        kind,
        function: name.to_string(),
        location: SourceSpan::default(),
        formula: Formula::Bool(false),
        contract_metadata: None,
    }
}

/// A mock backend with a configurable role (for Selective routing tests).
struct RoleBackend {
    name: &'static str,
    role: crate::BackendRole,
    delay: Duration,
    result_fn: Box<dyn Fn() -> VerificationResult + Send + Sync>,
}

impl crate::VerificationBackend for RoleBackend {
    fn name(&self) -> &str {
        self.name
    }

    fn role(&self) -> crate::BackendRole {
        self.role
    }

    fn can_handle(&self, _vc: &VerificationCondition) -> bool {
        true
    }

    fn verify(&self, _vc: &VerificationCondition) -> VerificationResult {
        std::thread::sleep(self.delay);
        (self.result_fn)()
    }
}

#[test]
fn test_dispatch_mode_race_fastest_wins() {
    let fast: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "fast",
        delay: Duration::from_millis(5),
        result_fn: Box::new(|| proved_result("fast")),
    });
    let slow: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "slow",
        delay: Duration::from_millis(200),
        result_fn: Box::new(|| proved_result("slow")),
    });

    let runner = PortfolioRunner::new(vec![fast, slow], DispatchMode::Race);
    assert_eq!(runner.mode(), DispatchMode::Race);
    assert_eq!(runner.backend_count(), 2);

    let result = runner.verify(&test_vc("race_runner"));
    assert!(result.is_proved());
    assert_eq!(result.solver_name(), "fast");
}

#[test]
fn test_dispatch_mode_race_counterexample_wins() {
    let cex: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "cex-finder",
        delay: Duration::from_millis(5),
        result_fn: Box::new(|| failed_result("cex-finder")),
    });
    let prover: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "slow-prover",
        delay: Duration::from_millis(200),
        result_fn: Box::new(|| proved_result("slow-prover")),
    });

    let runner = PortfolioRunner::new(vec![cex, prover], DispatchMode::Race);
    let result = runner.verify(&test_vc("race_cex"));
    assert!(result.is_failed());
    assert_eq!(result.solver_name(), "cex-finder");
}

#[test]
fn test_dispatch_mode_race_empty_backends() {
    let runner = PortfolioRunner::new(vec![], DispatchMode::Race);
    let result = runner.verify(&test_vc("empty"));
    assert!(matches!(result, VerificationResult::Unknown { .. }));
}

#[test]
fn test_dispatch_mode_cascade_stops_on_proved() {
    let unk: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "unk-backend",
        delay: Duration::ZERO,
        result_fn: Box::new(|| unknown_result("unk-backend")),
    });
    let prover: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "prover",
        delay: Duration::ZERO,
        result_fn: Box::new(|| proved_result("prover")),
    });

    let runner = PortfolioRunner::new(vec![unk, prover], DispatchMode::Cascade);
    let result = runner.verify(&test_vc("cascade_test"));
    assert!(result.is_proved());
    assert_eq!(result.solver_name(), "prover");
}

#[test]
fn test_dispatch_mode_cascade_first_conclusive_wins() {
    let fast: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "first",
        delay: Duration::ZERO,
        result_fn: Box::new(|| proved_result("first")),
    });
    let second: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "second",
        delay: Duration::ZERO,
        result_fn: Box::new(|| failed_result("second")),
    });

    let runner = PortfolioRunner::new(vec![fast, second], DispatchMode::Cascade);
    let result = runner.verify(&test_vc("cascade_first"));
    assert!(result.is_proved());
    assert_eq!(result.solver_name(), "first");
}

#[test]
fn test_dispatch_mode_cascade_all_unknown_returns_first() {
    let b1: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "unk1",
        delay: Duration::ZERO,
        result_fn: Box::new(|| unknown_result("unk1")),
    });
    let b2: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "unk2",
        delay: Duration::ZERO,
        result_fn: Box::new(|| unknown_result("unk2")),
    });

    let runner = PortfolioRunner::new(vec![b1, b2], DispatchMode::Cascade);
    let result = runner.verify(&test_vc("cascade_unk"));
    assert!(matches!(result, VerificationResult::Unknown { .. }));
    assert_eq!(result.solver_name(), "unk1");
}

#[test]
fn test_dispatch_mode_cascade_empty_backends() {
    let runner = PortfolioRunner::new(vec![], DispatchMode::Cascade);
    let result = runner.verify(&test_vc("empty"));
    assert!(matches!(result, VerificationResult::Unknown { .. }));
}

#[test]
fn test_dispatch_mode_selective_routes_by_kind() {
    let smt: Arc<dyn crate::VerificationBackend> = Arc::new(RoleBackend {
        name: "z4-smt",
        role: crate::BackendRole::SmtSolver,
        delay: Duration::ZERO,
        result_fn: Box::new(|| proved_result("z4-smt")),
    });
    let temporal: Arc<dyn crate::VerificationBackend> = Arc::new(RoleBackend {
        name: "tla2-temporal",
        role: crate::BackendRole::Temporal,
        delay: Duration::ZERO,
        result_fn: Box::new(|| proved_result("tla2-temporal")),
    });

    let runner =
        PortfolioRunner::new(vec![smt, temporal], DispatchMode::Selective);

    // DivisionByZero is L0Safety -> prefers SmtSolver
    let safety_vc = vc_with_kind("div", VcKind::DivisionByZero);
    let result = runner.verify(&safety_vc);
    assert!(result.is_proved());
    assert_eq!(result.solver_name(), "z4-smt");

    // Temporal is L2Domain -> prefers Temporal backend
    let temporal_vc = vc_with_kind(
        "temp",
        VcKind::Temporal { property: "always safe".to_string() },
    );
    let result = runner.verify(&temporal_vc);
    assert!(result.is_proved());
    assert_eq!(result.solver_name(), "tla2-temporal");
}

#[test]
fn test_dispatch_mode_selective_empty_backends() {
    let runner = PortfolioRunner::new(vec![], DispatchMode::Selective);
    let result = runner.verify(&test_vc("empty"));
    assert!(matches!(result, VerificationResult::Unknown { .. }));
}

#[test]
fn test_portfolio_runner_verify_all() {
    let backend: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "batch-runner",
        delay: Duration::ZERO,
        result_fn: Box::new(|| proved_result("batch-runner")),
    });

    let runner = PortfolioRunner::new(vec![backend], DispatchMode::Cascade);
    let vcs: Vec<_> = (0..4).map(|i| test_vc(&format!("fn_{i}"))).collect();
    let results = runner.verify_all(&vcs);

    assert_eq!(results.len(), 4);
    for (vc, result) in &results {
        assert!(result.is_proved());
        assert!(vc.function.starts_with("fn_"));
    }
}

#[test]
fn test_dispatch_mode_race_definitive_beats_unknown() {
    let fast_unk: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "fast-unk",
        delay: Duration::from_millis(5),
        result_fn: Box::new(|| unknown_result("fast-unk")),
    });
    let slow_proved: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "slow-proved",
        delay: Duration::from_millis(50),
        result_fn: Box::new(|| proved_result("slow-proved")),
    });

    let runner = PortfolioRunner::new(vec![fast_unk, slow_proved], DispatchMode::Race);
    let result = runner.verify(&test_vc("race_mixed"));
    assert!(result.is_proved());
    assert_eq!(result.solver_name(), "slow-proved");
}

#[test]
fn test_dispatch_mode_selective_deductive_for_postcondition() {
    let deductive: Arc<dyn crate::VerificationBackend> = Arc::new(RoleBackend {
        name: "sunder",
        role: crate::BackendRole::Deductive,
        delay: Duration::ZERO,
        result_fn: Box::new(|| proved_result("sunder")),
    });
    let general: Arc<dyn crate::VerificationBackend> = Arc::new(RoleBackend {
        name: "mock",
        role: crate::BackendRole::General,
        delay: Duration::ZERO,
        result_fn: Box::new(|| proved_result("mock")),
    });

    let runner =
        PortfolioRunner::new(vec![general, deductive], DispatchMode::Selective);

    // Postcondition is L1Functional -> prefers Deductive
    let post_vc = vc_with_kind("post", VcKind::Postcondition);
    let result = runner.verify(&post_vc);
    assert!(result.is_proved());
    assert_eq!(result.solver_name(), "sunder");
}

// -----------------------------------------------------------------------
// Enhanced portfolio types tests (RaceStrategy, PortfolioConfig, SolverPool, etc.)
// -----------------------------------------------------------------------

fn make_solver_entry(name: &str, result: VerificationResult) -> SolverEntry {
    let name_owned = name.to_string();
    let result_clone = result.clone();
    SolverEntry {
        name: name_owned.clone(),
        backend: Arc::new(DelayedBackend {
            name: Box::leak(name_owned.into_boxed_str()),
            delay: Duration::ZERO,
            result_fn: Box::new(move || result_clone.clone()),
        }),
    }
}

#[test]
fn test_race_strategy_default_is_first_result() {
    assert_eq!(RaceStrategy::default(), RaceStrategy::FirstResult);
}

#[test]
fn test_portfolio_config_default() {
    let config = PortfolioConfig::default();
    assert_eq!(config.strategy, RaceStrategy::FirstResult);
    assert_eq!(config.solver_timeout_ms, 0);
    assert_eq!(config.max_parallel, 8);
}

#[test]
fn test_solver_entry_debug() {
    let entry = make_solver_entry("z4", proved_result("z4"));
    let debug = format!("{:?}", entry);
    assert!(debug.contains("z4"));
}

#[test]
fn test_solver_pool_basic() {
    let entries = vec![
        make_solver_entry("z4", proved_result("z4")),
        make_solver_entry("mock", proved_result("mock")),
    ];

    let pool = SolverPool::with_defaults(entries);
    assert_eq!(pool.solver_count(), 2);
    assert!(pool.solver_names().contains(&"z4"));
    assert!(pool.solver_names().contains(&"mock"));
}

#[test]
fn test_solver_pool_race_first_result() {
    let entries = vec![
        make_solver_entry("z4", proved_result("z4")),
        make_solver_entry("mock", failed_result("mock")),
    ];

    let config = PortfolioConfig {
        strategy: RaceStrategy::FirstResult,
        ..Default::default()
    };

    let pool = SolverPool::new(entries, config);
    let result = pool.race(&test_vc("pool_test"));
    assert!(result.is_definitive());
    assert_eq!(result.strategy_used, RaceStrategy::FirstResult);
    assert!(result.solver_count() > 0);
}

#[test]
fn test_solver_pool_race_empty() {
    let pool = SolverPool::with_defaults(vec![]);
    let result = pool.race(&test_vc("empty"));
    assert!(!result.is_definitive());
    assert_eq!(result.winner_solver, "none");
    assert_eq!(result.solver_count(), 0);
}

#[test]
fn test_solver_pool_race_all() {
    let entries = vec![make_solver_entry("z4", proved_result("z4"))];
    let pool = SolverPool::with_defaults(entries);

    let vcs: Vec<_> = (0..3).map(|i| test_vc(&format!("fn_{i}"))).collect();
    let results = pool.race_all(&vcs);
    assert_eq!(results.len(), 3);
    for (_, race_result) in &results {
        assert!(race_result.is_definitive());
    }
}

#[test]
fn test_race_result_accessors() {
    let result = RaceResult {
        winner_result: proved_result("z4"),
        winner_solver: "z4".to_string(),
        race_time_ms: 42,
        solver_statuses: vec![(
            "z4".to_string(),
            crate::adaptive::SolverStatus::Completed { time_ms: 42 },
        )],
        strategy_used: RaceStrategy::FirstResult,
    };

    assert!(result.is_definitive());
    assert_eq!(result.solver_count(), 1);
    assert_eq!(result.race_time_ms, 42);
}

#[test]
fn test_solver_statistics_basic() {
    let mut stats = SolverStatistics::new();
    assert_eq!(stats.total_races(), 0);
    assert_eq!(stats.win_rate("z4"), 0.0);

    stats.record_race("z4", true, 10);
    stats.record_race("z4", false, 20);
    stats.record_race("mock", true, 5);

    assert_eq!(stats.total_races(), 3);
    assert!((stats.win_rate("z4") - 0.5).abs() < f64::EPSILON);
    assert!((stats.win_rate("mock") - 1.0).abs() < f64::EPSILON);
    assert!((stats.avg_time_ms("z4") - 15.0).abs() < f64::EPSILON);
    assert!((stats.avg_time_ms("mock") - 5.0).abs() < f64::EPSILON);
}

#[test]
fn test_solver_statistics_solver_names() {
    let mut stats = SolverStatistics::new();
    stats.record_race("z4", true, 10);
    stats.record_race("sunder", true, 20);

    let names = stats.solver_names();
    assert_eq!(names.len(), 2);
    assert!(names.contains(&"z4"));
    assert!(names.contains(&"sunder"));
}

#[test]
fn test_solver_pool_first_sat_strategy() {
    let entries = vec![
        make_solver_entry("z4", proved_result("z4")),
        make_solver_entry("mock", failed_result("mock")),
    ];

    let config = PortfolioConfig {
        strategy: RaceStrategy::FirstSat,
        max_parallel: 1, // Sequential to make test deterministic
        ..Default::default()
    };

    let pool = SolverPool::new(entries, config);
    let result = pool.race(&test_vc("first_sat"));
    assert!(result.winner_result.is_proved());
    assert_eq!(result.winner_solver, "z4");
}

#[test]
fn test_solver_pool_best_strength_strategy() {
    let entries = vec![
        make_solver_entry("z4", proved_result("z4")),
        make_solver_entry("mock", proved_result("mock")),
    ];

    let config = PortfolioConfig {
        strategy: RaceStrategy::BestStrength,
        max_parallel: 1,
        ..Default::default()
    };

    let pool = SolverPool::new(entries, config);
    let result = pool.race(&test_vc("best_strength"));
    assert!(result.winner_result.is_proved());
    assert_eq!(result.strategy_used, RaceStrategy::BestStrength);
}

// -----------------------------------------------------------------------
// tRust #224: CachedPortfolioRacer + TimeoutFallbackChain tests
// -----------------------------------------------------------------------

fn make_cache() -> Arc<std::sync::Mutex<crate::query_cache::QueryCache>> {
    Arc::new(std::sync::Mutex::new(crate::query_cache::QueryCache::new(1024)))
}

#[test]
fn test_first_wins() {
    let cache = make_cache();
    let fast: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "z4-fast",
        delay: Duration::from_millis(10),
        result_fn: Box::new(|| proved_result("z4-fast")),
    });
    let slow: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "lean5-slow",
        delay: Duration::from_millis(500),
        result_fn: Box::new(|| proved_result("lean5-slow")),
    });

    let racer = CachedPortfolioRacer::new(
        vec![
            (BackendConfig::new("z4", 0), fast),
            (BackendConfig::new("lean5", 0), slow),
        ],
        5000,
        cache,
    );

    let vc = test_vc("first_wins");
    let result = racer.race(&vc);
    assert!(result.is_proved());
    assert_eq!(result.solver_name(), "z4-fast");
}

#[test]
fn test_timeout_fallback() {
    let cache = make_cache();
    let slow: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "z4-slow",
        delay: Duration::from_millis(500),
        result_fn: Box::new(|| proved_result("z4-slow")),
    });
    let fast: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "zani-fast",
        delay: Duration::from_millis(5),
        result_fn: Box::new(|| proved_result("zani-fast")),
    });

    let chain = TimeoutFallbackChain::new(
        vec![
            (BackendConfig::new("z4", 50), slow),
            (BackendConfig::new("zani", 0), fast),
        ],
        cache,
    );

    let vc = test_vc("timeout_fallback");
    let result = chain.execute(&vc);
    assert!(result.is_proved());
    assert_eq!(result.solver_name(), "zani-fast");
}

#[test]
fn test_cache_hit() {
    let cache = make_cache();
    let vc = test_vc("cache_hit");
    let expected = proved_result("cached-z4");

    cache.lock().expect("lock").store(&vc.formula, expected.clone());

    let slow: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "should-not-run",
        delay: Duration::from_secs(10),
        result_fn: Box::new(|| {
            panic!("solver should not run on cache hit");
        }),
    });

    let racer = CachedPortfolioRacer::new(
        vec![(BackendConfig::new("z4", 0), slow)],
        1000,
        cache,
    );

    let result = racer.race(&vc);
    assert!(result.is_proved());
    assert_eq!(result.solver_name(), "cached-z4");
}

#[test]
fn test_all_timeout() {
    let cache = make_cache();
    let slow1: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "z4-glacial",
        delay: Duration::from_millis(500),
        result_fn: Box::new(|| proved_result("z4-glacial")),
    });
    let slow2: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "zani-glacial",
        delay: Duration::from_millis(500),
        result_fn: Box::new(|| proved_result("zani-glacial")),
    });

    let chain = TimeoutFallbackChain::new(
        vec![
            (BackendConfig::new("z4", 30), slow1),
            (BackendConfig::new("zani", 30), slow2),
        ],
        cache,
    );

    let vc = test_vc("all_timeout");
    let result = chain.execute(&vc);
    assert!(
        matches!(result, VerificationResult::Timeout { .. }),
        "expected Timeout, got: {result:?}",
    );
}

// -----------------------------------------------------------------------
// tRust #297: ResultPolicy, run_portfolio, solver_selection, PortfolioStats
// -----------------------------------------------------------------------

#[test]
fn test_result_policy_default_is_first_any() {
    assert_eq!(ResultPolicy::default(), ResultPolicy::FirstAny);
}

#[test]
fn test_result_policy_variants_distinct() {
    let policies = [
        ResultPolicy::FirstSat,
        ResultPolicy::FirstUnsat,
        ResultPolicy::FirstAny,
        ResultPolicy::Majority,
        ResultPolicy::Reconciled,
    ];
    for (i, a) in policies.iter().enumerate() {
        for (j, b) in policies.iter().enumerate() {
            if i == j {
                assert_eq!(a, b);
            } else {
                assert_ne!(a, b);
            }
        }
    }
}

#[test]
fn test_run_portfolio_first_any_proved() {
    let b1: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "prover-a",
        delay: Duration::from_millis(5),
        result_fn: Box::new(|| proved_result("prover-a")),
    });
    let b2: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "prover-b",
        delay: Duration::from_millis(200),
        result_fn: Box::new(|| proved_result("prover-b")),
    });

    let (result, solver) =
        run_portfolio(&test_vc("first_any"), &[b1, b2], ResultPolicy::FirstAny);
    assert!(result.is_proved());
    assert_eq!(solver, "prover-a");
}

#[test]
fn test_run_portfolio_first_sat_ignores_failed() {
    let b1: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "failer",
        delay: Duration::from_millis(5),
        result_fn: Box::new(|| failed_result("failer")),
    });
    let b2: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "prover",
        delay: Duration::from_millis(50),
        result_fn: Box::new(|| proved_result("prover")),
    });

    let (result, solver) =
        run_portfolio(&test_vc("first_sat"), &[b1, b2], ResultPolicy::FirstSat);
    assert!(result.is_proved());
    assert_eq!(solver, "prover");
}

#[test]
fn test_run_portfolio_first_unsat_ignores_proved() {
    let b1: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "prover",
        delay: Duration::from_millis(5),
        result_fn: Box::new(|| proved_result("prover")),
    });
    let b2: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "failer",
        delay: Duration::from_millis(50),
        result_fn: Box::new(|| failed_result("failer")),
    });

    let (result, solver) =
        run_portfolio(&test_vc("first_unsat"), &[b1, b2], ResultPolicy::FirstUnsat);
    assert!(result.is_failed());
    assert_eq!(solver, "failer");
}

// tRust #803 P0-1: When both Proved and Failed appear, Majority returns
// Unknown (conflict), not Proved. The old test asserted buggy behavior where
// 2 Proved + 1 Failed returned Proved.
#[test]
fn test_run_portfolio_majority_conflict_returns_unknown() {
    let p1: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "prover-1",
        delay: Duration::ZERO,
        result_fn: Box::new(|| proved_result("prover-1")),
    });
    let p2: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "prover-2",
        delay: Duration::ZERO,
        result_fn: Box::new(|| proved_result("prover-2")),
    });
    let f1: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "failer-1",
        delay: Duration::ZERO,
        result_fn: Box::new(|| failed_result("failer-1")),
    });

    let (result, _solver) =
        run_portfolio(&test_vc("majority"), &[p1, p2, f1], ResultPolicy::Majority);
    // Conflict: both Proved and Failed present => Unknown regardless of counts.
    assert!(matches!(result, VerificationResult::Unknown { .. }));
}

#[test]
fn test_run_portfolio_majority_unanimous_proved() {
    // When all solvers agree (no conflict), strict majority works.
    let p1: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "prover-1",
        delay: Duration::ZERO,
        result_fn: Box::new(|| proved_result("prover-1")),
    });
    let p2: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "prover-2",
        delay: Duration::ZERO,
        result_fn: Box::new(|| proved_result("prover-2")),
    });
    let u1: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "unknown-1",
        delay: Duration::ZERO,
        result_fn: Box::new(|| VerificationResult::Unknown {
            solver: "unknown-1".to_string(),
            time_ms: 0,
            reason: "timeout".to_string(),
        }),
    });

    let (result, _solver) =
        run_portfolio(&test_vc("majority"), &[p1, p2, u1], ResultPolicy::Majority);
    // 2 Proved out of 3 total: 2 > 3/2 = 1, so strict majority holds.
    assert!(result.is_proved());
}

#[test]
fn test_run_portfolio_majority_no_majority_returns_unknown() {
    // 1 Proved, 2 Unknown: 1 is NOT > 3/2=1, no majority.
    let p1: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "prover-1",
        delay: Duration::ZERO,
        result_fn: Box::new(|| proved_result("prover-1")),
    });
    let u1: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "unknown-1",
        delay: Duration::ZERO,
        result_fn: Box::new(|| VerificationResult::Unknown {
            solver: "unknown-1".to_string(),
            time_ms: 0,
            reason: "timeout".to_string(),
        }),
    });
    let u2: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "unknown-2",
        delay: Duration::ZERO,
        result_fn: Box::new(|| VerificationResult::Unknown {
            solver: "unknown-2".to_string(),
            time_ms: 0,
            reason: "timeout".to_string(),
        }),
    });

    let (result, _solver) =
        run_portfolio(&test_vc("majority"), &[p1, u1, u2], ResultPolicy::Majority);
    // 1 Proved out of 3 total: 1 is NOT > 1, no strict majority.
    assert!(matches!(result, VerificationResult::Unknown { .. }));
}

#[test]
fn test_run_portfolio_empty_backends() {
    let (result, solver) =
        run_portfolio(&test_vc("empty"), &[], ResultPolicy::FirstAny);
    assert!(matches!(result, VerificationResult::Unknown { .. }));
    assert_eq!(solver, "none");
}

#[test]
fn test_solver_selection_l0_safety() {
    let vc = VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: "div_fn".to_string(),
        location: SourceSpan::default(),
        formula: Formula::Bool(false),
        contract_metadata: None,
    };
    let roles = solver_selection(&vc);
    assert!(roles.contains(&crate::BackendRole::SmtSolver));
    assert!(roles.contains(&crate::BackendRole::BoundedModelChecker));
    assert!(!roles.contains(&crate::BackendRole::Temporal));
}

#[test]
fn test_solver_selection_l1_functional() {
    let vc = VerificationCondition {
        kind: VcKind::Postcondition,
        function: "post_fn".to_string(),
        location: SourceSpan::default(),
        formula: Formula::Bool(false),
        contract_metadata: None,
    };
    let roles = solver_selection(&vc);
    assert_eq!(roles[0], crate::BackendRole::Deductive);
    assert!(roles.contains(&crate::BackendRole::SmtSolver));
}

#[test]
fn test_solver_selection_l2_domain() {
    let vc = VerificationCondition {
        kind: VcKind::Temporal { property: "always safe".to_string() },
        function: "temp_fn".to_string(),
        location: SourceSpan::default(),
        formula: Formula::Bool(false),
        contract_metadata: None,
    };
    let roles = solver_selection(&vc);
    assert_eq!(roles[0], crate::BackendRole::Temporal);
    assert!(roles.contains(&crate::BackendRole::Deductive));
}

#[test]
fn test_portfolio_stats_basic() {
    let mut stats = PortfolioStats::new();
    assert_eq!(stats.total_races(), 0);
    assert_eq!(stats.win_rate("z4"), 0.0);

    stats.record("z4", true, 10);
    stats.record("z4", false, 20);
    stats.record("mock", true, 5);
    stats.record_race();
    stats.record_race();

    assert_eq!(stats.total_races(), 2);
    assert!((stats.win_rate("z4") - 0.5).abs() < f64::EPSILON);
    assert!((stats.win_rate("mock") - 1.0).abs() < f64::EPSILON);
    assert!((stats.avg_time_ms("z4") - 15.0).abs() < f64::EPSILON);
    assert_eq!(stats.wins("z4"), 1);
    assert_eq!(stats.wins("mock"), 1);
    assert_eq!(stats.wins("nonexistent"), 0);
}

#[test]
fn test_portfolio_stats_ranking() {
    let mut stats = PortfolioStats::new();
    stats.record("slow-solver", false, 100);
    stats.record("slow-solver", false, 100);
    stats.record("fast-solver", true, 10);
    stats.record("fast-solver", true, 10);
    stats.record("mid-solver", true, 50);
    stats.record("mid-solver", false, 50);

    let ranking = stats.ranking();
    assert_eq!(ranking[0].0, "fast-solver");
    assert!((ranking[0].1 - 1.0).abs() < f64::EPSILON);
    assert_eq!(ranking[1].0, "mid-solver");
    assert!((ranking[1].1 - 0.5).abs() < f64::EPSILON);
    assert_eq!(ranking[2].0, "slow-solver");
    assert!((ranking[2].1).abs() < f64::EPSILON);
}

#[test]
fn test_portfolio_stats_solver_names() {
    let mut stats = PortfolioStats::new();
    stats.record("z4", true, 10);
    stats.record("sunder", true, 20);
    stats.record("lean5", false, 30);

    let names = stats.solver_names();
    assert_eq!(names.len(), 3);
    assert!(names.contains(&"z4"));
    assert!(names.contains(&"sunder"));
    assert!(names.contains(&"lean5"));
}

#[test]
fn test_run_portfolio_first_any_counterexample_wins() {
    let b1: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "bmc",
        delay: Duration::from_millis(5),
        result_fn: Box::new(|| failed_result("bmc")),
    });
    let b2: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "slow-prover",
        delay: Duration::from_millis(200),
        result_fn: Box::new(|| proved_result("slow-prover")),
    });

    let (result, solver) =
        run_portfolio(&test_vc("first_any_cex"), &[b1, b2], ResultPolicy::FirstAny);
    assert!(result.is_failed());
    assert_eq!(solver, "bmc");
}

// -----------------------------------------------------------------------
// tRust #424: BestStrength keeps strongest proof
// -----------------------------------------------------------------------

fn proved_with_strength(solver: &str, strength: ProofStrength) -> VerificationResult {
    VerificationResult::Proved {
        solver: solver.to_string(),
        time_ms: 0,
        strength,
        proof_certificate: None,
            solver_warnings: None,
    }
}

fn make_solver_entry_with_strength(
    name: &str,
    strength: ProofStrength,
) -> SolverEntry {
    let name_owned = name.to_string();
    let result = proved_with_strength(name, strength);
    SolverEntry {
        name: name_owned.clone(),
        backend: Arc::new(DelayedBackend {
            name: Box::leak(name_owned.into_boxed_str()),
            delay: Duration::ZERO,
            result_fn: Box::new(move || result.clone()),
        }),
    }
}

#[test]
fn test_best_strength_keeps_strongest_proof() {
    let entries = vec![
        make_solver_entry_with_strength("zani", ProofStrength::bounded(10)),
        make_solver_entry_with_strength("sunder", ProofStrength::deductive()),
    ];

    let config = PortfolioConfig {
        strategy: RaceStrategy::BestStrength,
        max_parallel: 2,
        ..Default::default()
    };

    let pool = SolverPool::new(entries, config);
    let result = pool.race(&test_vc("best_strength_compare"));
    assert!(result.winner_result.is_proved());
    match &result.winner_result {
        VerificationResult::Proved { strength, .. } => {
            assert!(
                strength.assurance.strength_order() >= 2,
                "expected Sound (2) or higher, got order {}",
                strength.assurance.strength_order()
            );
        }
        other => panic!("expected Proved, got: {other:?}"),
    }
}

#[test]
fn test_best_strength_does_not_downgrade() {
    let entries = vec![
        make_solver_entry_with_strength("sunder", ProofStrength::deductive()),
        make_solver_entry_with_strength("zani", ProofStrength::bounded(5)),
    ];

    let config = PortfolioConfig {
        strategy: RaceStrategy::BestStrength,
        max_parallel: 2,
        ..Default::default()
    };

    let pool = SolverPool::new(entries, config);
    let result = pool.race(&test_vc("no_downgrade"));
    assert!(result.winner_result.is_proved());
    match &result.winner_result {
        VerificationResult::Proved { strength, .. } => {
            assert!(
                strength.assurance.strength_order() >= 2,
                "proof was downgraded! order = {}",
                strength.assurance.strength_order()
            );
        }
        other => panic!("expected Proved, got: {other:?}"),
    }
}

// -----------------------------------------------------------------------
// tRust #425: TimeoutFallbackChain cancellation flag
// -----------------------------------------------------------------------

#[test]
fn test_timeout_fallback_chain_cancels_on_timeout() {
    let cache = make_cache();
    let slow: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "slow-z4",
        delay: Duration::from_millis(500),
        result_fn: Box::new(|| proved_result("slow-z4")),
    });
    let fast: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "fast-zani",
        delay: Duration::from_millis(5),
        result_fn: Box::new(|| proved_result("fast-zani")),
    });

    let chain = TimeoutFallbackChain::new(
        vec![
            (BackendConfig::new("z4", 50), slow),
            (BackendConfig::new("zani", 0), fast),
        ],
        cache,
    );

    let vc = test_vc("cancel_test");
    let result = chain.execute(&vc);
    assert!(result.is_proved());
    assert_eq!(result.solver_name(), "fast-zani");
}

// -----------------------------------------------------------------------
// tRust #423: Cross-solver reconciliation tests
// -----------------------------------------------------------------------

#[test]
fn test_reconcile_results_all_agree_proved() {
    let results = vec![
        ("z4".to_string(), proved_result("z4")),
        ("sunder".to_string(), proved_result("sunder")),
    ];
    let outcome = reconcile_results(results);
    assert!(outcome.is_agreed());
    assert!(!outcome.is_conflict());
    match outcome {
        ReconciliationOutcome::Agreed { solver, result } => {
            assert!(result.is_proved());
            assert_eq!(solver, "z4");
        }
        _ => panic!("expected Agreed"),
    }
}

#[test]
fn test_reconcile_results_all_agree_failed() {
    let results = vec![
        ("zani".to_string(), failed_result("zani")),
        ("z4".to_string(), failed_result("z4")),
    ];
    let outcome = reconcile_results(results);
    assert!(outcome.is_agreed());
    match outcome {
        ReconciliationOutcome::Agreed { solver, result } => {
            assert!(result.is_failed());
            assert_eq!(solver, "zani");
        }
        _ => panic!("expected Agreed"),
    }
}

#[test]
fn test_reconcile_results_conflict_proved_vs_failed() {
    let results = vec![
        ("z4".to_string(), proved_result("z4")),
        ("zani".to_string(), failed_result("zani")),
    ];
    let outcome = reconcile_results(results);
    assert!(outcome.is_conflict());
    assert!(!outcome.is_agreed());
    match &outcome {
        ReconciliationOutcome::Conflict {
            proved_solvers,
            failed_solvers,
            results,
        } => {
            assert_eq!(proved_solvers, &["z4"]);
            assert_eq!(failed_solvers, &["zani"]);
            assert_eq!(results.len(), 2);
        }
        _ => panic!("expected Conflict"),
    }

    let vr = outcome.into_result();
    assert!(matches!(vr, VerificationResult::Unknown { .. }));
    assert_eq!(vr.solver_name(), "portfolio-reconciler");
    match vr {
        VerificationResult::Unknown { reason, .. } => {
            assert!(reason.contains("cross-solver conflict"));
            assert!(reason.contains("z4"));
            assert!(reason.contains("zani"));
        }
        _ => panic!("expected Unknown"),
    }
}

#[test]
fn test_reconcile_results_conflict_multiple_solvers() {
    let results = vec![
        ("z4".to_string(), proved_result("z4")),
        ("sunder".to_string(), proved_result("sunder")),
        ("zani".to_string(), failed_result("zani")),
    ];
    let outcome = reconcile_results(results);
    assert!(outcome.is_conflict());
    match &outcome {
        ReconciliationOutcome::Conflict {
            proved_solvers,
            failed_solvers,
            ..
        } => {
            assert_eq!(proved_solvers.len(), 2);
            assert_eq!(failed_solvers.len(), 1);
            assert!(proved_solvers.contains(&"z4".to_string()));
            assert!(proved_solvers.contains(&"sunder".to_string()));
            assert!(failed_solvers.contains(&"zani".to_string()));
        }
        _ => panic!("expected Conflict"),
    }
}

#[test]
fn test_reconcile_results_inconclusive() {
    let results = vec![
        ("z4".to_string(), unknown_result("z4")),
        ("zani".to_string(), unknown_result("zani")),
    ];
    let outcome = reconcile_results(results);
    assert!(outcome.is_inconclusive());
    match outcome {
        ReconciliationOutcome::Inconclusive { solver, result } => {
            assert!(matches!(result, VerificationResult::Unknown { .. }));
            assert_eq!(solver, "z4");
        }
        _ => panic!("expected Inconclusive"),
    }
}

#[test]
fn test_reconcile_results_empty() {
    let outcome = reconcile_results(vec![]);
    assert!(outcome.is_inconclusive());
}

#[test]
fn test_run_portfolio_reconciled_policy_detects_conflict() {
    let prover: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "prover",
        delay: Duration::ZERO,
        result_fn: Box::new(|| proved_result("prover")),
    });
    let failer: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "failer",
        delay: Duration::ZERO,
        result_fn: Box::new(|| failed_result("failer")),
    });

    let (result, solver) = run_portfolio(
        &test_vc("reconciled_conflict"),
        &[prover, failer],
        ResultPolicy::Reconciled,
    );
    assert!(matches!(result, VerificationResult::Unknown { .. }));
    assert_eq!(solver, "portfolio-reconciler");
}

#[test]
fn test_run_portfolio_reconciled_policy_no_conflict() {
    let p1: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "prover-1",
        delay: Duration::ZERO,
        result_fn: Box::new(|| proved_result("prover-1")),
    });
    let p2: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "prover-2",
        delay: Duration::ZERO,
        result_fn: Box::new(|| proved_result("prover-2")),
    });

    let (result, _solver) = run_portfolio(
        &test_vc("reconciled_agree"),
        &[p1, p2],
        ResultPolicy::Reconciled,
    );
    assert!(result.is_proved());
}

#[test]
fn test_run_portfolio_reconciled_fn_conflict() {
    let prover: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "z4",
        delay: Duration::ZERO,
        result_fn: Box::new(|| proved_result("z4")),
    });
    let failer: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "zani",
        delay: Duration::ZERO,
        result_fn: Box::new(|| failed_result("zani")),
    });

    let outcome = run_portfolio_reconciled(
        &test_vc("reconciled_fn_conflict"),
        &[prover, failer],
    );
    assert!(outcome.is_conflict());
    match &outcome {
        ReconciliationOutcome::Conflict {
            proved_solvers,
            failed_solvers,
            ..
        } => {
            assert!(proved_solvers.contains(&"z4".to_string()));
            assert!(failed_solvers.contains(&"zani".to_string()));
        }
        _ => panic!("expected Conflict"),
    }
}

#[test]
fn test_run_portfolio_reconciled_fn_agreement() {
    let p1: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "z4",
        delay: Duration::ZERO,
        result_fn: Box::new(|| proved_result("z4")),
    });
    let p2: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "sunder",
        delay: Duration::ZERO,
        result_fn: Box::new(|| proved_result("sunder")),
    });

    let outcome = run_portfolio_reconciled(
        &test_vc("reconciled_fn_agree"),
        &[p1, p2],
    );
    assert!(outcome.is_agreed());
}

#[test]
fn test_run_portfolio_reconciled_fn_empty() {
    let outcome = run_portfolio_reconciled(
        &test_vc("reconciled_fn_empty"),
        &[],
    );
    assert!(outcome.is_inconclusive());
}

#[test]
fn test_run_portfolio_reconciled_fn_all_unknown() {
    let u1: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "unk1",
        delay: Duration::ZERO,
        result_fn: Box::new(|| unknown_result("unk1")),
    });
    let u2: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "unk2",
        delay: Duration::ZERO,
        result_fn: Box::new(|| unknown_result("unk2")),
    });

    let outcome = run_portfolio_reconciled(
        &test_vc("reconciled_fn_unk"),
        &[u1, u2],
    );
    assert!(outcome.is_inconclusive());
}

#[test]
fn test_reconciliation_outcome_into_result_agreed() {
    let outcome = ReconciliationOutcome::Agreed {
        result: proved_result("z4"),
        solver: "z4".to_string(),
    };
    let vr = outcome.into_result();
    assert!(vr.is_proved());
    assert_eq!(vr.solver_name(), "z4");
}

#[test]
fn test_reconciliation_outcome_into_result_conflict() {
    let outcome = ReconciliationOutcome::Conflict {
        results: vec![
            ("z4".to_string(), proved_result("z4")),
            ("zani".to_string(), failed_result("zani")),
        ],
        proved_solvers: vec!["z4".to_string()],
        failed_solvers: vec!["zani".to_string()],
    };
    let vr = outcome.into_result();
    assert!(matches!(vr, VerificationResult::Unknown { .. }));
    assert_eq!(vr.solver_name(), "portfolio-reconciler");
}

#[test]
fn test_reconciliation_outcome_into_result_inconclusive() {
    let outcome = ReconciliationOutcome::Inconclusive {
        result: unknown_result("z4"),
        solver: "z4".to_string(),
    };
    let vr = outcome.into_result();
    assert!(matches!(vr, VerificationResult::Unknown { .. }));
    assert_eq!(vr.solver_name(), "z4");
}

#[test]
fn test_existing_policies_unaffected_by_reconciled() {
    let fast_prover: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "fast-prover",
        delay: Duration::from_millis(5),
        result_fn: Box::new(|| proved_result("fast-prover")),
    });
    let slow_failer: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "slow-failer",
        delay: Duration::from_millis(200),
        result_fn: Box::new(|| failed_result("slow-failer")),
    });

    let (result, solver) = run_portfolio(
        &test_vc("existing_firstany"),
        &[fast_prover, slow_failer],
        ResultPolicy::FirstAny,
    );
    assert!(result.is_proved());
    assert_eq!(solver, "fast-prover");
}

// -------------------------------------------------------------------
// tRust #446: QueryClass -> portfolio strategy selection tests
// -------------------------------------------------------------------

/// Helper: create a VC with a specific formula for classifier testing.
fn make_classified_vc(formula: Formula) -> VerificationCondition {
    VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: "classified_test".to_string(),
        location: SourceSpan::default(),
        formula,
        contract_metadata: None,
    }
}

#[test]
fn test_select_strategies_easy_linear_starts_with_bmc() {
    let strategies = select_strategies_for_query(QueryClass::EasyLinear);
    assert_eq!(strategies.len(), 5, "all strategies should be included");
    assert_eq!(
        strategies[0],
        PortfolioStrategy::Bmc,
        "EasyLinear should start with BMC for fast counterexamples"
    );
}

#[test]
fn test_select_strategies_bitvector_starts_with_bmc() {
    let strategies = select_strategies_for_query(QueryClass::BitVector);
    assert_eq!(strategies[0], PortfolioStrategy::Bmc);
    assert_eq!(strategies[1], PortfolioStrategy::KInduction);
}

#[test]
fn test_select_strategies_quantified_starts_with_ic3pdr() {
    let strategies = select_strategies_for_query(QueryClass::Quantified);
    assert_eq!(
        strategies[0],
        PortfolioStrategy::Ic3Pdr,
        "Quantified queries should prefer IC3/PDR (CHC quantifier instantiation)"
    );
    assert_eq!(strategies[1], PortfolioStrategy::StrongestPostcondition);
    assert_eq!(strategies[2], PortfolioStrategy::KInduction);
}

#[test]
fn test_select_strategies_hard_nonlinear_starts_with_ic3pdr() {
    let strategies = select_strategies_for_query(QueryClass::HardNonlinear);
    assert_eq!(strategies[0], PortfolioStrategy::Ic3Pdr);
}

#[test]
fn test_select_strategies_array_theory_starts_with_ic3pdr() {
    let strategies = select_strategies_for_query(QueryClass::ArrayTheory);
    assert_eq!(strategies[0], PortfolioStrategy::Ic3Pdr);
}

#[test]
fn test_select_strategies_mixed_starts_with_bmc() {
    let strategies = select_strategies_for_query(QueryClass::Mixed);
    assert_eq!(strategies[0], PortfolioStrategy::Bmc);
}

#[test]
fn test_select_strategies_ownership_starts_with_structural() {
    let strategies = select_strategies_for_query(QueryClass::Ownership);
    assert_eq!(
        strategies[0],
        PortfolioStrategy::Structural,
        "Ownership VCs should prefer structural analysis (zero-cost invariant checks)"
    );
}

#[test]
fn test_select_strategies_all_classes_include_all_strategies() {
    let classes = [
        QueryClass::EasyLinear,
        QueryClass::BitVector,
        QueryClass::Quantified,
        QueryClass::HardNonlinear,
        QueryClass::ArrayTheory,
        QueryClass::Mixed,
        QueryClass::Ownership,
    ];
    let all_strategies = [
        PortfolioStrategy::Bmc,
        PortfolioStrategy::Bfs,
        PortfolioStrategy::Ic3Pdr,
        PortfolioStrategy::KInduction,
        PortfolioStrategy::Structural,
    ];
    for class in classes {
        let strategies = select_strategies_for_query(class);
        for expected in &all_strategies {
            assert!(
                strategies.contains(expected),
                "class {:?} should include strategy {:?}",
                class,
                expected
            );
        }
    }
}

#[test]
fn test_classify_and_select_strategies_linear_formula() {
    let vc = make_classified_vc(Formula::Add(
        Box::new(Formula::Var("x".into(), Sort::Int)),
        Box::new(Formula::Int(1)),
    ));
    let (class, strategies) = classify_and_select_strategies(&vc);
    assert_eq!(class, QueryClass::EasyLinear);
    assert_eq!(strategies[0], PortfolioStrategy::Bmc);
}

#[test]
fn test_classify_and_select_strategies_bitvector_formula() {
    let vc = make_classified_vc(Formula::BvAdd(
        Box::new(Formula::Var("a".into(), Sort::BitVec(32))),
        Box::new(Formula::Var("b".into(), Sort::BitVec(32))),
        32,
    ));
    let (class, strategies) = classify_and_select_strategies(&vc);
    assert_eq!(class, QueryClass::BitVector);
    assert_eq!(strategies[0], PortfolioStrategy::Bmc);
}

#[test]
fn test_classify_and_select_strategies_quantified_formula() {
    let vc = make_classified_vc(Formula::Forall(
        vec![("x".into(), Sort::Int)],
        Box::new(Formula::Gt(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        )),
    ));
    let (class, strategies) = classify_and_select_strategies(&vc);
    assert_eq!(class, QueryClass::Quantified);
    assert_eq!(strategies[0], PortfolioStrategy::Ic3Pdr);
}

#[test]
fn test_classify_and_select_strategies_array_formula() {
    let vc = make_classified_vc(Formula::Select(
        Box::new(Formula::Var(
            "arr".into(),
            Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int)),
        )),
        Box::new(Formula::Var("idx".into(), Sort::Int)),
    ));
    let (class, strategies) = classify_and_select_strategies(&vc);
    assert_eq!(class, QueryClass::ArrayTheory);
    assert_eq!(strategies[0], PortfolioStrategy::Ic3Pdr);
}

#[test]
fn test_classify_and_select_strategies_nonlinear_formula() {
    let vc = make_classified_vc(Formula::Mul(
        Box::new(Formula::Var("x".into(), Sort::Int)),
        Box::new(Formula::Var("y".into(), Sort::Int)),
    ));
    let (class, strategies) = classify_and_select_strategies(&vc);
    assert_eq!(class, QueryClass::HardNonlinear);
    assert_eq!(strategies[0], PortfolioStrategy::Ic3Pdr);
}

#[test]
fn test_classify_and_select_strategies_mixed_formula() {
    let vc = make_classified_vc(Formula::And(vec![
        Formula::BvAdd(
            Box::new(Formula::Var("a".into(), Sort::BitVec(32))),
            Box::new(Formula::Var("b".into(), Sort::BitVec(32))),
            32,
        ),
        Formula::Select(
            Box::new(Formula::Var(
                "arr".into(),
                Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int)),
            )),
            Box::new(Formula::Var("idx".into(), Sort::Int)),
        ),
    ]));
    let (class, strategies) = classify_and_select_strategies(&vc);
    assert_eq!(class, QueryClass::Mixed);
    assert_eq!(strategies[0], PortfolioStrategy::Bmc);
}

// -------------------------------------------------------------------
// tRust #446: classified_solver_selection tests
// -------------------------------------------------------------------

#[test]
fn test_classified_solver_selection_linear_prefers_smt() {
    let vc = make_classified_vc(Formula::Add(
        Box::new(Formula::Var("x".into(), Sort::Int)),
        Box::new(Formula::Int(1)),
    ));
    let (class, roles) = classified_solver_selection(&vc);
    assert_eq!(class, QueryClass::EasyLinear);
    assert_eq!(
        roles[0],
        crate::BackendRole::SmtSolver,
        "EasyLinear should prefer SmtSolver (z4)"
    );
}

#[test]
fn test_classified_solver_selection_bitvector_prefers_bmc() {
    let vc = make_classified_vc(Formula::BvAdd(
        Box::new(Formula::Var("a".into(), Sort::BitVec(32))),
        Box::new(Formula::Var("b".into(), Sort::BitVec(32))),
        32,
    ));
    let (class, roles) = classified_solver_selection(&vc);
    assert_eq!(class, QueryClass::BitVector);
    assert_eq!(
        roles[0],
        crate::BackendRole::BoundedModelChecker,
        "BitVector should prefer BoundedModelChecker (zani)"
    );
}

#[test]
fn test_classified_solver_selection_quantified_prefers_higher_order() {
    let vc = make_classified_vc(Formula::Forall(
        vec![("x".into(), Sort::Int)],
        Box::new(Formula::Gt(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        )),
    ));
    let (class, roles) = classified_solver_selection(&vc);
    assert_eq!(class, QueryClass::Quantified);
    assert_eq!(
        roles[0],
        crate::BackendRole::HigherOrder,
        "Quantified should prefer HigherOrder (lean5)"
    );
}

#[test]
fn test_classified_solver_selection_ownership_prefers_ownership() {
    let vc = VerificationCondition {
        kind: VcKind::Assertion {
            message: "[memory:region] borrow check".to_string(),
        },
        function: "ownership_test".to_string(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };
    let (class, roles) = classified_solver_selection(&vc);
    assert_eq!(class, QueryClass::Ownership);
    assert_eq!(
        roles[0],
        crate::BackendRole::Ownership,
        "Ownership VCs should prefer Ownership backend (certus)"
    );
}

#[test]
fn test_classified_solver_selection_merges_proof_level_roles() {
    let vc = make_classified_vc(Formula::Add(
        Box::new(Formula::Var("x".into(), Sort::Int)),
        Box::new(Formula::Int(1)),
    ));
    let (_, roles) = classified_solver_selection(&vc);
    assert!(
        roles.contains(&crate::BackendRole::Cegar),
        "Cegar from ProofLevel selection should be merged in"
    );
    let unique_count = {
        let mut seen = roles.clone();
        seen.sort();
        seen.dedup();
        seen.len()
    };
    assert_eq!(unique_count, roles.len(), "roles should have no duplicates");
}

// -------------------------------------------------------------------
// tRust #446: suggested_timeout_ms tests
// -------------------------------------------------------------------

#[test]
fn test_suggested_timeout_easy_linear_is_short() {
    let timeout = suggested_timeout_ms(QueryClass::EasyLinear);
    assert_eq!(timeout, 5_000, "EasyLinear should get 5s timeout");
}

#[test]
fn test_suggested_timeout_quantified_is_long() {
    let timeout = suggested_timeout_ms(QueryClass::Quantified);
    assert_eq!(timeout, 60_000, "Quantified should get 60s timeout");
}

#[test]
fn test_suggested_timeout_ordering() {
    assert!(
        suggested_timeout_ms(QueryClass::EasyLinear)
            < suggested_timeout_ms(QueryClass::BitVector)
    );
    assert!(
        suggested_timeout_ms(QueryClass::BitVector)
            < suggested_timeout_ms(QueryClass::HardNonlinear)
    );
    assert!(
        suggested_timeout_ms(QueryClass::HardNonlinear)
            <= suggested_timeout_ms(QueryClass::Quantified)
    );
}

// -------------------------------------------------------------------
// tRust #446: PortfolioRacer::classified constructor test
// -------------------------------------------------------------------

#[test]
fn test_portfolio_racer_classified_constructor() {
    let backend: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "test-solver",
        delay: Duration::from_millis(0),
        result_fn: Box::new(|| proved_result("test-solver")),
    });

    let vc = make_classified_vc(Formula::Add(
        Box::new(Formula::Var("x".into(), Sort::Int)),
        Box::new(Formula::Int(1)),
    ));
    let (racer, class) = PortfolioRacer::classified(&vc, backend);
    assert_eq!(class, QueryClass::EasyLinear);
    assert_eq!(racer.lane_count(), 5, "all strategies should be lanes");
}

#[test]
fn test_portfolio_racer_classified_bitvector_ordering() {
    let backend: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "bv-solver",
        delay: Duration::from_millis(0),
        result_fn: Box::new(|| proved_result("bv-solver")),
    });

    let vc = make_classified_vc(Formula::BvAdd(
        Box::new(Formula::Var("a".into(), Sort::BitVec(32))),
        Box::new(Formula::Var("b".into(), Sort::BitVec(32))),
        32,
    ));
    let (racer, class) = PortfolioRacer::classified(&vc, backend);
    assert_eq!(class, QueryClass::BitVector);

    let result = racer.race(&vc);
    assert!(result.is_some());
    let portfolio_result = result.unwrap();
    assert!(portfolio_result.is_definitive());
}

#[test]
fn test_different_query_classes_produce_different_strategy_orderings() {
    let linear = select_strategies_for_query(QueryClass::EasyLinear);
    let quantified = select_strategies_for_query(QueryClass::Quantified);
    let ownership = select_strategies_for_query(QueryClass::Ownership);

    assert_ne!(linear[0], quantified[0]);
    assert_ne!(linear[0], ownership[0]);
    assert_ne!(quantified[0], ownership[0]);
}

// -------------------------------------------------------------------
// tRust #476: Proof replay cache integration tests
// -------------------------------------------------------------------

use trust_cache::proof_replay::{ProofStrategy, ReplayCache};
use std::sync::Mutex;

/// Helper: create a shared replay cache.
fn make_replay_cache() -> Arc<Mutex<ReplayCache>> {
    Arc::new(Mutex::new(ReplayCache::new()))
}

#[test]
fn test_vc_to_strategy_key_deterministic() {
    let vc = test_vc("deterministic_test");
    let key1 = vc_to_strategy_key(&vc);
    let key2 = vc_to_strategy_key(&vc);
    assert_eq!(key1, key2, "strategy key must be deterministic for the same VC");
}

#[test]
fn test_vc_to_strategy_key_different_for_different_vcs() {
    let vc1 = test_vc("fn_a");
    let vc2 = vc_with_kind("fn_b", VcKind::DivisionByZero);
    let key1 = vc_to_strategy_key(&vc1);
    let key2 = vc_to_strategy_key(&vc2);
    assert_ne!(key1, key2, "different VCs should have different keys");
}

#[test]
fn test_portfolio_racer_with_replay_cache_records_winning_strategy() {
    let replay_cache = make_replay_cache();
    let backend: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "z4-replay",
        delay: Duration::ZERO,
        result_fn: Box::new(|| proved_result("z4-replay")),
    });

    let racer = PortfolioRacer::with_replay_cache(
        vec![
            (PortfolioStrategy::Bmc, Arc::clone(&backend)),
            (PortfolioStrategy::Ic3Pdr, backend),
        ],
        Arc::clone(&replay_cache),
    );

    assert!(racer.has_replay_cache());

    let vc = test_vc("replay_record");
    let result = racer.race(&vc).expect("should get a result");
    assert!(result.is_definitive());

    // Check that the winning strategy was recorded in the cache.
    let key = vc_to_strategy_key(&vc);
    let mut cache = replay_cache.lock().unwrap();
    let lookup = cache.lookup(&key);
    assert!(
        matches!(lookup, trust_cache::proof_replay::ReplayResult::ExactMatch(_)),
        "winning strategy should be cached as exact match"
    );
}

#[test]
fn test_portfolio_racer_replay_cache_frontloads_cached_strategy() {
    let replay_cache = make_replay_cache();

    // Pre-populate cache with Ic3Pdr as the winning strategy.
    let vc = test_vc("frontload_test");
    let key = vc_to_strategy_key(&vc);
    let cached_strategy = ProofStrategy::new("z4-cached", 100)
        .with_hint("portfolio:ic3pdr".to_string());
    {
        let mut cache = replay_cache.lock().unwrap();
        cache.record(key, cached_strategy);
    }

    // Both backends prove, but the fast one (Bmc lane, 5ms) would
    // normally win over the slow one (Ic3Pdr lane, 50ms). With replay
    // cache, Ic3Pdr is front-loaded as first lane.
    let fast_backend: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "fast-bmc",
        delay: Duration::from_millis(5),
        result_fn: Box::new(|| proved_result("fast-bmc")),
    });
    let slow_backend: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "slow-ic3",
        delay: Duration::from_millis(5),
        result_fn: Box::new(|| proved_result("slow-ic3")),
    });

    let racer = PortfolioRacer::with_replay_cache(
        vec![
            (PortfolioStrategy::Bmc, fast_backend),
            (PortfolioStrategy::Ic3Pdr, slow_backend),
        ],
        Arc::clone(&replay_cache),
    );

    let result = racer.race(&vc).expect("should get a result");
    assert!(result.is_definitive());
    // The result should note that a replay cache was consulted.
    // replay_hit is Some(...) because we had a cache hint.
    assert!(result.replay_hit.is_some(), "replay_hit should be set when cache was consulted");
}

#[test]
fn test_portfolio_racer_without_replay_cache_has_none_replay_hit() {
    let backend: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "no-cache",
        delay: Duration::ZERO,
        result_fn: Box::new(|| proved_result("no-cache")),
    });

    let racer = PortfolioRacer::new(vec![
        (PortfolioStrategy::Bmc, backend),
    ]);

    assert!(!racer.has_replay_cache());

    let vc = test_vc("no_cache_test");
    let result = racer.race(&vc).expect("should get a result");
    assert!(result.replay_hit.is_none(), "replay_hit should be None without cache");
}

#[test]
fn test_portfolio_racer_replay_cache_miss_records_winner() {
    let replay_cache = make_replay_cache();

    // Cache is empty — miss expected.
    let backend: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "z4-miss",
        delay: Duration::ZERO,
        result_fn: Box::new(|| proved_result("z4-miss")),
    });

    let racer = PortfolioRacer::with_replay_cache(
        vec![(PortfolioStrategy::Structural, backend)],
        Arc::clone(&replay_cache),
    );

    let vc = test_vc("miss_then_record");
    let result = racer.race(&vc).expect("should get a result");
    assert!(result.is_definitive());
    // No cache hint, so replay_hit should be None.
    assert!(result.replay_hit.is_none(), "no cache hint means replay_hit is None");

    // But the winner should now be recorded in the cache.
    let key = vc_to_strategy_key(&vc);
    let mut cache = replay_cache.lock().unwrap();
    assert!(
        matches!(cache.lookup(&key), trust_cache::proof_replay::ReplayResult::ExactMatch(_)),
        "after a miss-then-prove, the winning strategy should be cached"
    );
}

#[test]
fn test_portfolio_racer_replay_cache_stats_updated() {
    let replay_cache = make_replay_cache();
    let backend: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "stats-test",
        delay: Duration::ZERO,
        result_fn: Box::new(|| proved_result("stats-test")),
    });

    let racer = PortfolioRacer::with_replay_cache(
        vec![(PortfolioStrategy::Bmc, backend)],
        Arc::clone(&replay_cache),
    );

    // First race: cache miss.
    let vc = test_vc("stats_test");
    racer.race(&vc).expect("should get a result");

    // Second race: cache hit (exact match from first race).
    racer.race(&vc).expect("should get a result");

    let cache = replay_cache.lock().unwrap();
    let stats = cache.stats();
    assert_eq!(stats.lookups, 2, "two lookups should have been recorded");
    assert!(stats.exact_hits >= 1, "at least one exact hit expected on second race");
}

#[test]
fn test_race_all_with_replay_cache() {
    let replay_cache = make_replay_cache();
    let backend: Arc<dyn crate::VerificationBackend> = Arc::new(DelayedBackend {
        name: "batch-cache",
        delay: Duration::ZERO,
        result_fn: Box::new(|| proved_result("batch-cache")),
    });

    let racer = PortfolioRacer::with_replay_cache(
        vec![
            (PortfolioStrategy::Bmc, Arc::clone(&backend)),
            (PortfolioStrategy::Bfs, backend),
        ],
        Arc::clone(&replay_cache),
    );

    // tRust #476: Use distinct VcKind per VC so they get different strategy keys.
    // VCs with identical formula and kind share a cache key.
    let vcs = vec![
        vc_with_kind("batch_0", VcKind::DivisionByZero),
        vc_with_kind("batch_1", VcKind::Postcondition),
        vc_with_kind("batch_2", VcKind::Temporal { property: "always safe".to_string() }),
    ];
    let results = racer.race_all(&vcs);
    assert_eq!(results.len(), 3);

    // All results should be definitive.
    for (_, pr) in &results {
        assert!(pr.is_definitive());
    }

    // Cache should now have entries for all 3 VCs (distinct keys).
    let cache = replay_cache.lock().unwrap();
    assert!(cache.len() >= 3, "cache should have entries for all 3 VCs, got {}", cache.len());
}
