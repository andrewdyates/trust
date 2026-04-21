// trust-driver integration tests: end-to-end verification loop scenarios
//
// Exercises the public API of trust_driver from an external crate perspective,
// including run_loop, run_loop_with_debug, CegarVerifyPhase, and ConfigBridge.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::cell::Cell;
use std::io::Write as IoWrite;
use std::path::{Path, PathBuf};
use std::time::Duration;

use trust_driver::cegar_phase::{CegarPhaseConfig, CegarStats, CegarVerifyPhase};
use trust_driver::{
    BackpropOutput, BackpropPhase, CliOverrides, ConfigBridge, DebugOutput, DebugPhase,
    DebugReport, LoopConfig, ProofFrontier, SecurityViolation, Severity, StrengthenPhase,
    TerminationReason, VerifyOutput, VerifyPhase,
};
use trust_debug::{DebugSummary, SecurityViolationKind};
use trust_strengthen::{Proposal, ProposalKind, StrengthenOutput};

// ---------------------------------------------------------------------------
// Mock implementations
// ---------------------------------------------------------------------------

/// Mock verify phase that returns a pre-programmed sequence of outputs.
/// After exhausting the sequence, repeats the last entry.
struct MockVerify {
    outputs: Vec<VerifyOutput>,
    call_count: Cell<usize>,
}

impl MockVerify {
    fn new(outputs: Vec<VerifyOutput>) -> Self {
        Self {
            outputs,
            call_count: Cell::new(0),
        }
    }

}

impl VerifyPhase for MockVerify {
    fn verify(&self, _source_path: &Path) -> VerifyOutput {
        let idx = self.call_count.get();
        self.call_count.set(idx + 1);
        self.outputs[idx.min(self.outputs.len() - 1)].clone()
    }
}

/// Mock strengthen phase that returns proposals based on failure count.
struct MockStrengthen {
    proposals_per_call: usize,
}

impl StrengthenPhase for MockStrengthen {
    fn strengthen(&self, _: &Path, _: &VerifyOutput) -> StrengthenOutput {
        let proposals: Vec<Proposal> = (0..self.proposals_per_call)
            .map(|i| Proposal {
                function_path: format!("test::fn_{i}"),
                function_name: format!("fn_{i}"),
                kind: ProposalKind::AddPrecondition {
                    spec_body: format!("x > {i}"),
                },
                confidence: 0.9,
                rationale: format!("integration test proposal {i}"),
            })
            .collect();
        StrengthenOutput {
            has_proposals: !proposals.is_empty(),
            failures_analyzed: self.proposals_per_call,
            proposals,
        }
    }
}

/// Mock strengthen that returns no proposals.
struct EmptyStrengthen;

impl StrengthenPhase for EmptyStrengthen {
    fn strengthen(&self, _: &Path, _: &VerifyOutput) -> StrengthenOutput {
        StrengthenOutput {
            has_proposals: false,
            failures_analyzed: 0,
            proposals: vec![],
        }
    }
}

/// Strengthen phase that produces proposals only on the first call.
struct OneShotStrengthen {
    count: usize,
    called: Cell<bool>,
}

impl OneShotStrengthen {
    fn new(count: usize) -> Self {
        Self {
            count,
            called: Cell::new(false),
        }
    }
}

impl StrengthenPhase for OneShotStrengthen {
    fn strengthen(&self, _: &Path, _: &VerifyOutput) -> StrengthenOutput {
        if self.called.get() {
            return StrengthenOutput {
                has_proposals: false,
                failures_analyzed: 0,
                proposals: vec![],
            };
        }
        self.called.set(true);
        let proposals: Vec<Proposal> = (0..self.count)
            .map(|i| Proposal {
                function_path: format!("test::fn_{i}"),
                function_name: format!("fn_{i}"),
                kind: ProposalKind::AddPostcondition {
                    spec_body: format!("result >= {i}"),
                },
                confidence: 0.85,
                rationale: format!("one-shot proposal {i}"),
            })
            .collect();
        StrengthenOutput {
            has_proposals: true,
            failures_analyzed: self.count,
            proposals,
        }
    }
}

/// Mock backprop that applies all proposals and tracks the total.
struct MockBackprop {
    total_applied: Cell<usize>,
}

impl MockBackprop {
    fn new() -> Self {
        Self {
            total_applied: Cell::new(0),
        }
    }

    fn total_applied(&self) -> usize {
        self.total_applied.get()
    }
}

impl BackpropPhase for MockBackprop {
    fn backpropagate(&self, _: &Path, proposals: &[Proposal]) -> BackpropOutput {
        self.total_applied
            .set(self.total_applied.get() + proposals.len());
        BackpropOutput {
            applied: proposals.len(),
            skipped: 0,
        }
    }
}

/// Mock backprop that rejects all proposals.
struct RejectingBackprop;

impl BackpropPhase for RejectingBackprop {
    fn backpropagate(&self, _: &Path, proposals: &[Proposal]) -> BackpropOutput {
        BackpropOutput {
            applied: 0,
            skipped: proposals.len(),
        }
    }
}

/// Mock debug phase that finds violations.
struct MockDebug {
    violations: usize,
    has_critical: bool,
}

impl DebugPhase for MockDebug {
    fn find_violations(&self, _: &Path) -> DebugOutput {
        let violations: Vec<SecurityViolation> = (0..self.violations)
            .map(|i| SecurityViolation {
                id: format!("V{i:04}"),
                severity: if self.has_critical && i == 0 {
                    Severity::Critical
                } else {
                    Severity::Medium
                },
                kind: SecurityViolationKind::ArithmeticOverflow {
                    operation: "Add".to_string(),
                },
                function: format!("test::fn_{i}"),
                location: None,
                description: format!("integration test violation {i}"),
                flow_path: vec![],
                counterexample: None,
                solver: "mock".to_string(),
                time_ms: 0,
            })
            .collect();
        let report = DebugReport {
            target: "integration_test".to_string(),
            violations: violations.clone(),
            chains: vec![],
            summary: DebugSummary::from_violations(&violations, &[]),
        };
        DebugOutput::from_report(report)
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn frontier(trusted: u32, failed: u32) -> ProofFrontier {
    ProofFrontier {
        trusted,
        certified: 0,
        runtime_checked: 0,
        failed,
        unknown: 0,
    }
}

fn verify_output(trusted: u32, failed: u32) -> VerifyOutput {
    VerifyOutput {
        frontier: frontier(trusted, failed),
        fingerprint: None,
        vcs_dispatched: (trusted + failed) as usize,
        vcs_failed: failed as usize,
        detailed_results: None,
    }
}

fn verify_output_with_fingerprint(trusted: u32, failed: u32, fp: &str) -> VerifyOutput {
    VerifyOutput {
        frontier: frontier(trusted, failed),
        fingerprint: Some(fp.to_string()),
        vcs_dispatched: (trusted + failed) as usize,
        vcs_failed: failed as usize,
        detailed_results: None,
    }
}

fn test_path() -> PathBuf {
    PathBuf::from("/tmp/integration_test.rs")
}

// ===========================================================================
// Test 1: Single iteration success -- all VCs pass on first attempt
// ===========================================================================

#[test]
fn test_single_iteration_success_all_proved() {
    let verify = MockVerify::new(vec![verify_output(10, 0)]);
    let strengthen = EmptyStrengthen;
    let backprop = MockBackprop::new();
    let config = LoopConfig {
        max_iterations: 10,
        stable_round_limit: 2,
        allow_rewrite: true,
        run_debug: false,
    };

    let result = trust_driver::run_loop(&test_path(), &config, &verify, &strengthen, &backprop);

    assert_eq!(result.iterations, 1, "should terminate in one iteration");
    assert_eq!(result.reason, TerminationReason::AllProved);
    assert_eq!(result.final_frontier.trusted, 10);
    assert_eq!(result.final_frontier.failed, 0);
    assert_eq!(result.history.len(), 1);
    assert_eq!(result.history[0].vcs_failed, 0);
    assert_eq!(result.history[0].proposals, 0);
    assert_eq!(backprop.total_applied(), 0, "backprop should not be called");
}

// ===========================================================================
// Test 2: Strengthen-then-verify -- first pass fails, strengthen proposes,
//         second pass succeeds
// ===========================================================================

#[test]
fn test_strengthen_then_verify_succeeds() {
    // Iteration 0: 6 proven, 4 failed -> strengthen proposes 3 specs
    // Iteration 1: all 10 proven -> AllProved
    let verify = MockVerify::new(vec![verify_output(6, 4), verify_output(10, 0)]);
    let strengthen = MockStrengthen {
        proposals_per_call: 3,
    };
    let backprop = MockBackprop::new();
    let config = LoopConfig {
        max_iterations: 10,
        stable_round_limit: 2,
        allow_rewrite: true,
        run_debug: false,
    };

    let result = trust_driver::run_loop(&test_path(), &config, &verify, &strengthen, &backprop);

    assert_eq!(result.iterations, 2);
    assert_eq!(result.reason, TerminationReason::AllProved);
    assert_eq!(result.final_frontier.trusted, 10);
    assert_eq!(result.final_frontier.failed, 0);

    // First iteration should have proposals and applied rewrites
    assert_eq!(result.history[0].vcs_failed, 4);
    assert_eq!(result.history[0].proposals, 3);
    assert_eq!(result.history[0].applied, 3);

    // Second iteration should have no proposals (AllProved exits early)
    assert_eq!(result.history[1].vcs_failed, 0);
    assert_eq!(result.history[1].proposals, 0);

    assert_eq!(backprop.total_applied(), 3);
}

// ===========================================================================
// Test 3: Convergence detection -- frontier stabilizes
// ===========================================================================

#[test]
fn test_convergence_detection_stable_frontier() {
    // iter 0: 5/10 proven -> continue
    // iter 1: 7/10 proven -> continue (improved)
    // iter 2: 7/10 proven -> stable round 2 -> converged (stable_round_limit=2)
    let verify = MockVerify::new(vec![
        verify_output(5, 5),
        verify_output(7, 3),
        verify_output(7, 3),
    ]);
    let strengthen = MockStrengthen {
        proposals_per_call: 2,
    };
    let backprop = MockBackprop::new();
    let config = LoopConfig {
        max_iterations: 20,
        stable_round_limit: 2,
        allow_rewrite: true,
        run_debug: false,
    };

    let result = trust_driver::run_loop(&test_path(), &config, &verify, &strengthen, &backprop);

    assert_eq!(result.iterations, 3);
    assert_eq!(
        result.reason,
        TerminationReason::Converged { stable_rounds: 2 }
    );
    assert_eq!(result.final_frontier.trusted, 7);
    assert_eq!(result.final_frontier.failed, 3);
    assert_eq!(result.history.len(), 3);
}

#[test]
fn test_convergence_with_fingerprint() {
    // Same frontier AND same fingerprint => should converge in 2 rounds
    let verify = MockVerify::new(vec![
        verify_output_with_fingerprint(8, 2, "deadbeef"),
        verify_output_with_fingerprint(8, 2, "deadbeef"),
    ]);
    let strengthen = MockStrengthen {
        proposals_per_call: 1,
    };
    let backprop = MockBackprop::new();
    let config = LoopConfig {
        max_iterations: 10,
        stable_round_limit: 2,
        allow_rewrite: true,
        run_debug: false,
    };

    let result = trust_driver::run_loop(&test_path(), &config, &verify, &strengthen, &backprop);

    assert_eq!(result.iterations, 2);
    assert_eq!(
        result.reason,
        TerminationReason::Converged { stable_rounds: 2 }
    );
}

// ===========================================================================
// Test 4: Max iterations reached
// ===========================================================================

#[test]
fn test_max_iterations_reached() {
    // Each iteration improves slightly, never converges within limit.
    let verify = MockVerify::new(vec![
        verify_output(1, 9),
        verify_output(2, 8),
        verify_output(3, 7),
        verify_output(4, 6),
        verify_output(5, 5),
    ]);
    let strengthen = MockStrengthen {
        proposals_per_call: 1,
    };
    let backprop = MockBackprop::new();
    let config = LoopConfig {
        max_iterations: 3,
        stable_round_limit: 2,
        allow_rewrite: true,
        run_debug: false,
    };

    let result = trust_driver::run_loop(&test_path(), &config, &verify, &strengthen, &backprop);

    // ConvergenceTracker triggers limit at iteration >= max_iterations.
    // iter 0: continue, iter 1: continue, iter 2: continue, iter 3: limit reached
    assert_eq!(result.iterations, 4);
    assert_eq!(
        result.reason,
        TerminationReason::IterationLimit { iterations: 4 }
    );
    assert_eq!(result.history.len(), 4);
}

#[test]
fn test_max_iterations_one() {
    let verify = MockVerify::new(vec![verify_output(3, 7), verify_output(4, 6)]);
    let strengthen = MockStrengthen {
        proposals_per_call: 1,
    };
    let backprop = MockBackprop::new();
    let config = LoopConfig {
        max_iterations: 1,
        stable_round_limit: 2,
        allow_rewrite: true,
        run_debug: false,
    };

    let result = trust_driver::run_loop(&test_path(), &config, &verify, &strengthen, &backprop);

    // iter 0: continue, backprop; iter 1: limit reached
    assert_eq!(result.iterations, 2);
    assert_eq!(
        result.reason,
        TerminationReason::IterationLimit { iterations: 2 }
    );
}

// ===========================================================================
// Test 5: Backprop rewrite cycle -- full prove->strengthen->backprop->prove
// ===========================================================================

#[test]
fn test_full_backprop_rewrite_cycle() {
    // Multi-iteration cycle:
    // iter 0: 3 failed, strengthen proposes 2, backprop applies 2
    // iter 1: 1 failed, strengthen proposes 1, backprop applies 1
    // iter 2: 0 failed -> AllProved
    let verify = MockVerify::new(vec![
        verify_output(7, 3),
        verify_output(9, 1),
        verify_output(10, 0),
    ]);
    let strengthen = MockStrengthen {
        proposals_per_call: 2,
    };
    let backprop = MockBackprop::new();
    let config = LoopConfig {
        max_iterations: 10,
        stable_round_limit: 3,
        allow_rewrite: true,
        run_debug: false,
    };

    let result = trust_driver::run_loop(&test_path(), &config, &verify, &strengthen, &backprop);

    assert_eq!(result.iterations, 3);
    assert_eq!(result.reason, TerminationReason::AllProved);
    assert_eq!(result.final_frontier.trusted, 10);

    // Verify backprop was exercised in first two iterations
    assert!(result.history[0].applied > 0, "iter 0 should apply proposals");
    assert!(result.history[1].applied > 0, "iter 1 should apply proposals");

    // Total applied: 2 + 2 = 4 (2 proposals per call, 2 iterations with backprop)
    assert_eq!(backprop.total_applied(), 4);
}

#[test]
fn test_backprop_disabled_still_runs_loop() {
    // allow_rewrite=false: strengthen runs but backprop is skipped.
    // Loop should still converge via frontier stability.
    let verify = MockVerify::new(vec![
        verify_output(5, 5),
        verify_output(5, 5), // same => converges
    ]);
    let strengthen = MockStrengthen {
        proposals_per_call: 3,
    };
    let backprop = MockBackprop::new();
    let config = LoopConfig {
        max_iterations: 10,
        stable_round_limit: 2,
        allow_rewrite: false,
        run_debug: false,
    };

    let result = trust_driver::run_loop(&test_path(), &config, &verify, &strengthen, &backprop);

    // First iteration: proposals generated but not applied (allow_rewrite=false)
    assert_eq!(result.history[0].proposals, 3);
    assert_eq!(result.history[0].applied, 0);
    assert_eq!(
        backprop.total_applied(),
        0,
        "backprop should not be called when rewrite disabled"
    );
}

#[test]
fn test_backprop_rejects_all_stops_loop() {
    // Backprop rejects everything -> treated as no-proposals
    let verify = MockVerify::new(vec![verify_output(5, 5)]);
    let strengthen = MockStrengthen {
        proposals_per_call: 3,
    };
    let backprop = RejectingBackprop;
    let config = LoopConfig {
        max_iterations: 10,
        stable_round_limit: 2,
        allow_rewrite: true,
        run_debug: false,
    };

    let result = trust_driver::run_loop(&test_path(), &config, &verify, &strengthen, &backprop);

    assert_eq!(result.iterations, 1);
    assert_eq!(result.reason, TerminationReason::NoProposals);
    assert_eq!(result.history[0].proposals, 3);
    assert_eq!(result.history[0].applied, 0);
}

// ===========================================================================
// Test 6: CEGAR phase integration
// ===========================================================================

#[test]
fn test_cegar_phase_wraps_verify_no_failures() {
    // When inner verify returns all-proved, CEGAR adds no overhead.
    let inner = MockVerify::new(vec![verify_output(10, 0)]);
    let cegar = CegarVerifyPhase::new(inner, CegarPhaseConfig::default());

    let output = cegar.verify(&test_path());
    assert_eq!(output.vcs_failed, 0);
    assert_eq!(output.frontier.trusted, 10);
}

#[test]
fn test_cegar_phase_with_stats_tracks_refinement() {
    // Inner verify starts with failures; CEGAR should attempt refinement.
    let inner = MockVerify::new(vec![verify_output(5, 5), verify_output(8, 2)]);
    let config = CegarPhaseConfig {
        max_cegar_iterations: 5,
        initial_predicates: vec![trust_cegar::Predicate::comparison(
            "vcs_failed",
            trust_cegar::CmpOp::Eq,
            "0",
        )],
        blocks: vec![
            trust_types::BasicBlock {
                id: trust_types::BlockId(0),
                stmts: vec![],
                terminator: trust_types::Terminator::Assert {
                    cond: trust_types::Operand::Copy(trust_types::Place::local(1)),
                    expected: true,
                    msg: trust_types::AssertMessage::BoundsCheck,
                    target: trust_types::BlockId(1),
                    span: trust_types::SourceSpan::default(),
                },
            },
            trust_types::BasicBlock {
                id: trust_types::BlockId(1),
                stmts: vec![],
                terminator: trust_types::Terminator::Return,
            },
        ],
    };
    let cegar = CegarVerifyPhase::new(inner, config);

    let (output, stats) = cegar.verify_with_stats(&test_path());

    // After CEGAR refines, re-verify returns improved results.
    assert!(
        output.frontier.trusted >= 5,
        "CEGAR should not make things worse"
    );
    // Stats should show refinement activity.
    assert!(
        stats.refinement_iterations >= 1 || stats.real_counterexamples >= 1,
        "CEGAR should have attempted refinement"
    );
}

#[test]
fn test_cegar_phase_in_full_loop() {
    // Wire CegarVerifyPhase into run_loop to test the end-to-end path.
    let inner = MockVerify::new(vec![
        verify_output(5, 5),
        verify_output(8, 2),
        verify_output(10, 0),
    ]);
    let cegar = CegarVerifyPhase::new(inner, CegarPhaseConfig::default());
    let strengthen = MockStrengthen {
        proposals_per_call: 2,
    };
    let backprop = MockBackprop::new();
    let config = LoopConfig {
        max_iterations: 10,
        stable_round_limit: 2,
        allow_rewrite: true,
        run_debug: false,
    };

    let result = trust_driver::run_loop(&test_path(), &config, &cegar, &strengthen, &backprop);

    // The loop should eventually reach AllProved or converge.
    assert!(
        result.reason == TerminationReason::AllProved
            || matches!(result.reason, TerminationReason::Converged { .. }),
        "expected AllProved or Converged, got {:?}",
        result.reason
    );
}

#[test]
fn test_cegar_stats_default_values() {
    let stats = CegarStats::default();
    assert_eq!(stats.refinement_iterations, 0);
    assert_eq!(stats.spurious_eliminated, 0);
    assert_eq!(stats.real_counterexamples, 0);
    assert_eq!(stats.predicates_added, 0);
    assert!(!stats.hit_limit);
}

// ===========================================================================
// Test 7: Config bridge -- TrustConfig -> LoopConfig conversion
// ===========================================================================

#[test]
fn test_config_bridge_default() {
    let bridge = ConfigBridge::from_trust_config(&trust_config::TrustConfig::default());
    assert!(bridge.enabled);
    assert_eq!(bridge.level, "L0");
    assert_eq!(bridge.timeout, Duration::from_millis(5000));
    assert_eq!(bridge.loop_config.max_iterations, 8);
    assert_eq!(bridge.loop_config.stable_round_limit, 2);
    assert!(bridge.loop_config.allow_rewrite);
    assert!(bridge.loop_config.run_debug);
}

#[test]
fn test_config_bridge_disabled_disables_debug() {
    let tc = trust_config::TrustConfig {
        enabled: false,
        ..Default::default()
    };
    let bridge = ConfigBridge::from_trust_config(&tc);
    assert!(!bridge.loop_config.run_debug);
}

#[test]
fn test_config_bridge_cli_overrides() {
    let bridge = ConfigBridge::from_trust_config(&trust_config::TrustConfig::default());
    let cli = CliOverrides {
        max_iterations: Some(20),
        level: Some("L2".to_string()),
        timeout_ms: Some(30000),
        allow_rewrite: Some(false),
    };
    let merged = bridge.merge_with_cli(&cli);

    assert_eq!(merged.loop_config.max_iterations, 20);
    assert_eq!(merged.level, "L2");
    assert_eq!(merged.timeout, Duration::from_millis(30000));
    assert!(!merged.loop_config.allow_rewrite);
}

#[test]
fn test_config_bridge_partial_cli_overrides() {
    let tc = trust_config::TrustConfig {
        level: "L1".to_string(),
        timeout_ms: 8000,
        ..Default::default()
    };
    let bridge = ConfigBridge::from_trust_config(&tc);
    let cli = CliOverrides {
        max_iterations: Some(3),
        ..Default::default()
    };
    let merged = bridge.merge_with_cli(&cli);

    assert_eq!(merged.loop_config.max_iterations, 3);
    assert_eq!(merged.level, "L1"); // unchanged
    assert_eq!(merged.timeout, Duration::from_millis(8000)); // unchanged
    assert!(merged.loop_config.allow_rewrite); // unchanged default
}

#[test]
fn test_config_bridge_from_toml_file() {
    let dir = tempfile::TempDir::new().expect("tempdir");
    let path = dir.path().join("trust.toml");
    let mut f = std::fs::File::create(&path).expect("create toml");
    writeln!(
        f,
        r#"
enabled = true
level = "L2"
timeout_ms = 12000
skip_functions = ["test_", "bench_"]
verify_functions = ["critical_"]
"#
    )
    .expect("write toml");
    drop(f);

    let bridge = ConfigBridge::from_toml_path(&path).expect("should parse valid toml");

    assert!(bridge.enabled);
    assert_eq!(bridge.level, "L2");
    assert_eq!(bridge.timeout, Duration::from_millis(12000));
    assert_eq!(bridge.skip_functions, vec!["test_", "bench_"]);
    assert_eq!(bridge.verify_functions, vec!["critical_"]);
    assert!(bridge.loop_config.run_debug);
}

#[test]
fn test_config_bridge_nonexistent_path_returns_defaults() {
    let bridge =
        ConfigBridge::from_toml_path(Path::new("/nonexistent/trust.toml")).expect("should default");
    assert!(bridge.enabled);
    assert_eq!(bridge.level, "L0");
}

#[test]
fn test_config_bridge_invalid_toml_returns_error() {
    let dir = tempfile::TempDir::new().expect("tempdir");
    let path = dir.path().join("trust.toml");
    std::fs::write(&path, "garbage_field = 42").expect("write");

    let result = ConfigBridge::from_toml_path(&path);
    assert!(result.is_err(), "invalid toml should produce error");
}

#[test]
fn test_config_bridge_end_to_end_toml_plus_cli_into_loop() {
    // Load config from TOML, apply CLI overrides, use resulting LoopConfig in run_loop.
    let dir = tempfile::TempDir::new().expect("tempdir");
    let path = dir.path().join("trust.toml");
    std::fs::write(
        &path,
        r#"
enabled = true
level = "L1"
timeout_ms = 7000
"#,
    )
    .expect("write toml");

    let bridge = ConfigBridge::from_toml_path(&path).expect("parse");
    let cli = CliOverrides {
        max_iterations: Some(5),
        ..Default::default()
    };
    let final_config = bridge.merge_with_cli(&cli);

    assert_eq!(final_config.loop_config.max_iterations, 5);
    assert_eq!(final_config.level, "L1");

    // Use the LoopConfig in an actual loop run
    let verify = MockVerify::new(vec![verify_output(10, 0)]);
    let strengthen = EmptyStrengthen;
    let backprop = MockBackprop::new();

    let result = trust_driver::run_loop(
        &test_path(),
        &final_config.loop_config,
        &verify,
        &strengthen,
        &backprop,
    );

    assert_eq!(result.reason, TerminationReason::AllProved);
}

// ===========================================================================
// Additional integration scenarios
// ===========================================================================

#[test]
fn test_regression_stops_loop_immediately() {
    // iter 0: 8 proved, 2 failed
    // iter 1: 6 proved, 4 failed -> regression!
    let verify = MockVerify::new(vec![verify_output(8, 2), verify_output(6, 4)]);
    let strengthen = MockStrengthen {
        proposals_per_call: 2,
    };
    let backprop = MockBackprop::new();
    let config = LoopConfig {
        max_iterations: 10,
        stable_round_limit: 2,
        allow_rewrite: true,
        run_debug: false,
    };

    let result = trust_driver::run_loop(&test_path(), &config, &verify, &strengthen, &backprop);

    assert_eq!(result.iterations, 2);
    assert_eq!(result.reason, TerminationReason::Regressed);
    assert_eq!(result.final_frontier.trusted, 6);
    assert_eq!(result.final_frontier.failed, 4);
}

#[test]
fn test_no_proposals_stops_loop() {
    // Verify finds failures but strengthen has nothing to propose.
    let verify = MockVerify::new(vec![verify_output(3, 7)]);
    let strengthen = EmptyStrengthen;
    let backprop = MockBackprop::new();
    let config = LoopConfig::default();

    let result = trust_driver::run_loop(&test_path(), &config, &verify, &strengthen, &backprop);

    assert_eq!(result.iterations, 1);
    assert_eq!(result.reason, TerminationReason::NoProposals);
    assert_eq!(backprop.total_applied(), 0);
}

#[test]
fn test_one_shot_strengthen_then_convergence() {
    // Strengthen proposes specs once, then stops. Frontier converges after.
    let verify = MockVerify::new(vec![
        verify_output(3, 7), // iter 0: strengthen proposes
        verify_output(6, 4), // iter 1: improve, strengthen empty -> NoProposals
    ]);
    let strengthen = OneShotStrengthen::new(3);
    let backprop = MockBackprop::new();
    let config = LoopConfig {
        max_iterations: 10,
        stable_round_limit: 2,
        allow_rewrite: true,
        run_debug: false,
    };

    let result = trust_driver::run_loop(&test_path(), &config, &verify, &strengthen, &backprop);

    // After first iteration applies proposals, second iteration strengthen is empty.
    assert_eq!(result.iterations, 2);
    assert_eq!(result.reason, TerminationReason::NoProposals);
    assert_eq!(backprop.total_applied(), 3);
}

#[test]
fn test_debug_phase_with_critical_prevents_all_proved() {
    // VCs all pass but debug finds critical violations -> not AllProved
    let verify = MockVerify::new(vec![verify_output(10, 0)]);
    let strengthen = MockStrengthen {
        proposals_per_call: 1,
    };
    let backprop = MockBackprop::new();
    let debug = MockDebug {
        violations: 3,
        has_critical: true,
    };
    let config = LoopConfig {
        max_iterations: 3,
        stable_round_limit: 2,
        allow_rewrite: true,
        run_debug: true,
    };

    let result = trust_driver::run_loop_with_debug(
        &test_path(),
        &config,
        &verify,
        &strengthen,
        &backprop,
        Some(&debug),
    );

    assert_ne!(result.reason, TerminationReason::AllProved);
    assert!(result.history[0].debug_critical);
    assert_eq!(result.history[0].debug_violations, 3);
}

#[test]
fn test_debug_disabled_ignores_violations() {
    // Debug phase finds violations but run_debug=false means they are ignored.
    let verify = MockVerify::new(vec![verify_output(10, 0)]);
    let strengthen = EmptyStrengthen;
    let backprop = MockBackprop::new();
    let debug = MockDebug {
        violations: 5,
        has_critical: true,
    };
    let config = LoopConfig {
        max_iterations: 5,
        stable_round_limit: 2,
        allow_rewrite: true,
        run_debug: false,
    };

    let result = trust_driver::run_loop_with_debug(
        &test_path(),
        &config,
        &verify,
        &strengthen,
        &backprop,
        Some(&debug),
    );

    assert_eq!(result.reason, TerminationReason::AllProved);
    assert_eq!(result.history[0].debug_violations, 0);
    assert!(!result.history[0].debug_critical);
}

#[test]
fn test_history_records_progression() {
    // Verify progressive improvement is tracked in history records.
    let verify = MockVerify::new(vec![
        verify_output(2, 8),
        verify_output(5, 5),
        verify_output(8, 2),
        verify_output(10, 0),
    ]);
    let strengthen = MockStrengthen {
        proposals_per_call: 1,
    };
    let backprop = MockBackprop::new();
    let config = LoopConfig {
        max_iterations: 10,
        stable_round_limit: 3,
        allow_rewrite: true,
        run_debug: false,
    };

    let result = trust_driver::run_loop(&test_path(), &config, &verify, &strengthen, &backprop);

    assert_eq!(result.reason, TerminationReason::AllProved);
    assert_eq!(result.iterations, 4);
    assert_eq!(result.history.len(), 4);

    // Check monotonic improvement in trusted count
    let trusted_progression: Vec<u32> = result.history.iter().map(|r| r.frontier.trusted).collect();
    assert_eq!(trusted_progression, vec![2, 5, 8, 10]);

    // Check monotonic decrease in failures
    let failure_progression: Vec<usize> = result.history.iter().map(|r| r.vcs_failed).collect();
    assert_eq!(failure_progression, vec![8, 5, 2, 0]);
}

#[test]
fn test_loop_config_defaults() {
    let config = LoopConfig::default();
    assert_eq!(config.max_iterations, 8);
    assert_eq!(config.stable_round_limit, 2);
    assert!(config.allow_rewrite);
    assert!(config.run_debug);
}
