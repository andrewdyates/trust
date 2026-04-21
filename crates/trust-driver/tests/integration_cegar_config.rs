// trust-driver integration tests: CEGAR phase + config bridge end-to-end
//
// Supplements integration.rs with tests for CegarVerifyPhase and ConfigBridge,
// exercising the CEGAR refinement pipeline and TrustConfig->LoopConfig conversion
// from an external crate perspective.
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
// Mock implementations (minimal set needed for these tests)
// ---------------------------------------------------------------------------

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
                rationale: format!("cegar test proposal {i}"),
            })
            .collect();
        StrengthenOutput {
            has_proposals: !proposals.is_empty(),
            failures_analyzed: self.proposals_per_call,
            proposals,
        }
    }
}

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

struct MockBackprop;

impl BackpropPhase for MockBackprop {
    fn backpropagate(&self, _: &Path, proposals: &[Proposal]) -> BackpropOutput {
        BackpropOutput {
            applied: proposals.len(),
            skipped: 0,
        }
    }
}

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
                description: format!("cegar test violation {i}"),
                flow_path: vec![],
                counterexample: None,
                solver: "mock".to_string(),
                time_ms: 0,
            })
            .collect();
        let report = DebugReport {
            target: "cegar_config_test".to_string(),
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

fn test_path() -> PathBuf {
    PathBuf::from("/tmp/cegar_config_test.rs")
}

// ===========================================================================
// CEGAR phase integration tests
// ===========================================================================

/// CegarVerifyPhase with no failures: should pass through without refinement.
#[test]
fn test_cegar_phase_no_failures_passthrough() {
    let inner = MockVerify::new(vec![verify_output(10, 0)]);
    let cegar = CegarVerifyPhase::new(inner, CegarPhaseConfig::default());

    let output = cegar.verify(&test_path());
    assert_eq!(output.vcs_failed, 0);
    assert_eq!(output.frontier.trusted, 10);
}

/// CegarVerifyPhase verify_with_stats returns zero refinement stats when no failures.
#[test]
fn test_cegar_phase_stats_no_refinement_needed() {
    let inner = MockVerify::new(vec![verify_output(10, 0)]);
    let cegar = CegarVerifyPhase::new(inner, CegarPhaseConfig::default());

    let (output, stats) = cegar.verify_with_stats(&test_path());
    assert_eq!(output.vcs_failed, 0);
    assert_eq!(stats.refinement_iterations, 0);
    assert_eq!(stats.spurious_eliminated, 0);
    assert_eq!(stats.real_counterexamples, 0);
    assert_eq!(stats.predicates_added, 0);
    assert!(!stats.hit_limit);
}

/// CegarVerifyPhase with failures and blocks triggers refinement attempt.
#[test]
fn test_cegar_phase_refinement_with_blocks() {
    // Inner: first call has failures, second call has fewer after CEGAR refines.
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

    // CEGAR should improve or at least not worsen results.
    assert!(
        output.frontier.trusted >= 5,
        "trusted should not decrease after CEGAR"
    );
    // Refinement should have been attempted.
    assert!(
        stats.refinement_iterations >= 1 || stats.real_counterexamples >= 1,
        "CEGAR should attempt refinement or detect real counterexample"
    );
}

/// CegarVerifyPhase with no blocks gracefully handles the edge case.
#[test]
fn test_cegar_phase_no_blocks_graceful() {
    let inner = MockVerify::new(vec![verify_output(5, 5)]);
    let config = CegarPhaseConfig {
        max_cegar_iterations: 3,
        initial_predicates: vec![],
        blocks: vec![],
    };
    let cegar = CegarVerifyPhase::new(inner, config);

    let (output, stats) = cegar.verify_with_stats(&test_path());

    // Without blocks, CEGAR cannot check spuriousness: treats as real.
    assert_eq!(output.vcs_failed, 5);
    assert!(stats.real_counterexamples >= 1 || stats.refinement_iterations == 0);
}

/// CegarStats default values are all zero / false.
#[test]
fn test_cegar_stats_defaults() {
    let stats = CegarStats::default();
    assert_eq!(stats.refinement_iterations, 0);
    assert_eq!(stats.spurious_eliminated, 0);
    assert_eq!(stats.real_counterexamples, 0);
    assert_eq!(stats.predicates_added, 0);
    assert!(!stats.hit_limit);
}

/// CegarVerifyPhase wired into the full run_loop pipeline.
#[test]
fn test_cegar_phase_in_full_loop() {
    let inner = MockVerify::new(vec![
        verify_output(5, 5),
        verify_output(8, 2),
        verify_output(10, 0),
    ]);
    let cegar = CegarVerifyPhase::new(inner, CegarPhaseConfig::default());
    let strengthen = MockStrengthen {
        proposals_per_call: 2,
    };
    let backprop = MockBackprop;
    let config = LoopConfig {
        max_iterations: 10,
        stable_round_limit: 2,
        allow_rewrite: true,
        run_debug: false,
    };

    let result = trust_driver::run_loop(&test_path(), &config, &cegar, &strengthen, &backprop);

    // Should reach AllProved or converge.
    assert!(
        result.reason == TerminationReason::AllProved
            || matches!(result.reason, TerminationReason::Converged { .. }),
        "expected AllProved or Converged, got {:?}",
        result.reason
    );
}

/// CegarVerifyPhase in full loop with debug phase enabled.
#[test]
fn test_cegar_phase_with_debug_in_loop() {
    let inner = MockVerify::new(vec![verify_output(10, 0)]);
    let cegar = CegarVerifyPhase::new(inner, CegarPhaseConfig::default());
    let strengthen = EmptyStrengthen;
    let backprop = MockBackprop;
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
        &cegar,
        &strengthen,
        &backprop,
        Some(&debug),
    );

    // VCs all pass but debug is critical -> should NOT be AllProved
    assert_ne!(result.reason, TerminationReason::AllProved);
    assert!(result.history[0].debug_critical);
}

// ===========================================================================
// Config bridge integration tests
// ===========================================================================

/// Default TrustConfig produces sensible LoopConfig defaults.
#[test]
fn test_config_bridge_default_values() {
    let bridge = ConfigBridge::from_trust_config(&trust_config::TrustConfig::default());
    assert!(bridge.enabled);
    assert_eq!(bridge.level, "L0");
    assert_eq!(bridge.timeout, Duration::from_millis(5000));
    assert_eq!(bridge.loop_config.max_iterations, 8);
    assert_eq!(bridge.loop_config.stable_round_limit, 2);
    assert!(bridge.loop_config.allow_rewrite);
    assert!(bridge.loop_config.run_debug);
    assert!(bridge.skip_functions.is_empty());
    assert!(bridge.verify_functions.is_empty());
}

/// Disabled TrustConfig disables the debug phase.
#[test]
fn test_config_bridge_disabled_disables_debug() {
    let tc = trust_config::TrustConfig {
        enabled: false,
        ..Default::default()
    };
    let bridge = ConfigBridge::from_trust_config(&tc);
    assert!(!bridge.loop_config.run_debug);
    assert!(!bridge.enabled);
}

/// CLI overrides replace all config values.
#[test]
fn test_config_bridge_full_cli_overrides() {
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

/// Partial CLI overrides leave other fields unchanged.
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
    assert_eq!(merged.level, "L1");
    assert_eq!(merged.timeout, Duration::from_millis(8000));
    assert!(merged.loop_config.allow_rewrite);
}

/// No CLI overrides leave everything unchanged.
#[test]
fn test_config_bridge_no_cli_overrides() {
    let bridge = ConfigBridge::from_trust_config(&trust_config::TrustConfig::default());
    let original_max = bridge.loop_config.max_iterations;
    let original_level = bridge.level.clone();
    let cli = CliOverrides::default();
    let merged = bridge.merge_with_cli(&cli);

    assert_eq!(merged.loop_config.max_iterations, original_max);
    assert_eq!(merged.level, original_level);
}

/// ConfigBridge from a valid TOML file.
#[test]
fn test_config_bridge_from_toml_file() {
    let dir = tempfile::TempDir::new().unwrap();
    let path = dir.path().join("trust.toml");
    let mut f = std::fs::File::create(&path).unwrap();
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
    .unwrap();
    drop(f);

    let bridge = ConfigBridge::from_toml_path(&path).expect("should parse valid toml");

    assert!(bridge.enabled);
    assert_eq!(bridge.level, "L2");
    assert_eq!(bridge.timeout, Duration::from_millis(12000));
    assert_eq!(bridge.skip_functions, vec!["test_", "bench_"]);
    assert_eq!(bridge.verify_functions, vec!["critical_"]);
    assert!(bridge.loop_config.run_debug);
}

/// ConfigBridge from a nonexistent path returns defaults (no error).
#[test]
fn test_config_bridge_nonexistent_defaults() {
    let bridge =
        ConfigBridge::from_toml_path(Path::new("/nonexistent/trust.toml")).expect("should default");
    assert!(bridge.enabled);
    assert_eq!(bridge.level, "L0");
    assert_eq!(bridge.timeout, Duration::from_millis(5000));
}

/// ConfigBridge from invalid TOML returns an error.
#[test]
fn test_config_bridge_invalid_toml_error() {
    let dir = tempfile::TempDir::new().unwrap();
    let path = dir.path().join("trust.toml");
    std::fs::write(&path, "garbage_field = 42").unwrap();

    let result = ConfigBridge::from_toml_path(&path);
    assert!(result.is_err());
}

/// ConfigBridge from_toml_dir with nonexistent directory returns defaults.
#[test]
fn test_config_bridge_from_toml_dir_nonexistent() {
    let bridge = ConfigBridge::from_toml_dir(Path::new("/nonexistent/dir"));
    assert!(bridge.enabled);
    assert_eq!(bridge.level, "L0");
}

/// End-to-end: load TOML, apply CLI overrides, wire LoopConfig into run_loop.
#[test]
fn test_config_bridge_end_to_end_into_loop() {
    let dir = tempfile::TempDir::new().unwrap();
    let path = dir.path().join("trust.toml");
    std::fs::write(
        &path,
        r#"
enabled = true
level = "L1"
timeout_ms = 7000
skip_functions = ["bench_"]
"#,
    )
    .unwrap();

    let bridge = ConfigBridge::from_toml_path(&path).expect("parse");
    let cli = CliOverrides {
        max_iterations: Some(5),
        level: Some("L2".to_string()),
        ..Default::default()
    };
    let final_config = bridge.merge_with_cli(&cli);

    // Verify merged config values
    assert_eq!(final_config.loop_config.max_iterations, 5);
    assert_eq!(final_config.level, "L2");
    assert_eq!(final_config.timeout, Duration::from_millis(7000));
    assert_eq!(final_config.skip_functions, vec!["bench_"]);

    // Wire the LoopConfig into an actual loop run
    let verify = MockVerify::new(vec![verify_output(10, 0)]);
    let strengthen = EmptyStrengthen;
    let backprop = MockBackprop;

    let result = trust_driver::run_loop(
        &test_path(),
        &final_config.loop_config,
        &verify,
        &strengthen,
        &backprop,
    );

    assert_eq!(result.reason, TerminationReason::AllProved);
    assert_eq!(result.iterations, 1);
}

/// Convenience function: loop_config_from_trust_config.
#[test]
fn test_loop_config_from_trust_config_convenience() {
    let tc = trust_config::TrustConfig {
        enabled: false,
        ..Default::default()
    };
    let lc = trust_driver::config_bridge::loop_config_from_trust_config(&tc);
    assert!(!lc.run_debug);
    assert_eq!(lc.max_iterations, LoopConfig::default().max_iterations);
}

/// Convenience function: from_toml_path returns just the LoopConfig.
#[test]
fn test_from_toml_path_convenience() {
    let dir = tempfile::TempDir::new().unwrap();
    let path = dir.path().join("trust.toml");
    std::fs::write(&path, "enabled = false").unwrap();

    let lc = trust_driver::config_bridge::from_toml_path(&path).expect("parse");
    assert!(!lc.run_debug);
}

/// Convenience function: merge_with_cli on bare LoopConfig.
#[test]
fn test_merge_with_cli_convenience() {
    let lc = LoopConfig::default();
    let cli = CliOverrides {
        max_iterations: Some(42),
        allow_rewrite: Some(false),
        ..Default::default()
    };
    let merged = trust_driver::config_bridge::merge_with_cli(lc, &cli);
    assert_eq!(merged.max_iterations, 42);
    assert!(!merged.allow_rewrite);
    assert_eq!(
        merged.stable_round_limit,
        LoopConfig::default().stable_round_limit
    );
}
