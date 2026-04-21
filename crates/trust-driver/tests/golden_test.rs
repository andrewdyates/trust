// tests/golden_test.rs: 3-iteration golden test for binary_search.rs loop
//
// Demonstrates gradual convergence of the prove->strengthen->backprop loop:
//   Iteration 1: 3 overflow bugs detected (add, shift, cast)
//   Iteration 2: 2 proved, 1 remaining
//   Iteration 3: all proved, convergence detected
//
// Uses mock compiler stderr strings representing stage1 rustc output.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

mod mock_compiler;

use std::cell::{Cell, RefCell};
use std::path::Path;

use trust_driver::{
    BackpropOutput, BackpropPhase, ConvergenceDecision, LoopConfig, LoopResult, ProofFrontier,
    StrengthenOutput, TerminationReason, VerifyOutput, VerifyPhase, StrengthenPhase, run_loop,
};
use trust_strengthen::{Proposal, ProposalKind};

// ---------------------------------------------------------------------------
// Mock verify phase: 3-iteration gradual convergence
// ---------------------------------------------------------------------------

/// Verify phase that returns pre-programmed outputs matching mock_compiler stderr.
/// Iteration 1: 3 failures (overflow:add, overflow:shift, overflow:cast)
/// Iteration 2: 1 failure remaining (overflow:cast still fails)
/// Iteration 3: 0 failures (all proved)
struct GradualVerify {
    call_count: Cell<usize>,
}

impl GradualVerify {
    fn new() -> Self {
        Self { call_count: Cell::new(0) }
    }
}

impl VerifyPhase for GradualVerify {
    fn verify(&self, _source_path: &Path) -> VerifyOutput {
        let idx = self.call_count.get();
        self.call_count.set(idx + 1);

        match idx {
            0 => {
                // Iteration 1: 3 overflow failures detected
                // Matches mock_compiler::mock_stderr_iter1()
                VerifyOutput {
                    frontier: ProofFrontier {
                        trusted: 0,
                        certified: 0,
                        runtime_checked: 0,
                        failed: 3,
                        unknown: 0,
                    },
                    fingerprint: Some("iter1-3fail".into()),
                    vcs_dispatched: 3,
                    vcs_failed: 3,
                    detailed_results: None,
                }
            }
            1 => {
                // Iteration 2: add and shift fixed, cast still fails
                // Matches mock_compiler::mock_stderr_iter2()
                VerifyOutput {
                    frontier: ProofFrontier {
                        trusted: 2,
                        certified: 0,
                        runtime_checked: 0,
                        failed: 1,
                        unknown: 0,
                    },
                    fingerprint: Some("iter2-1fail".into()),
                    vcs_dispatched: 3,
                    vcs_failed: 1,
                    detailed_results: None,
                }
            }
            _ => {
                // Iteration 3+: all proved
                // Matches mock_compiler::mock_stderr_iter3()
                VerifyOutput {
                    frontier: ProofFrontier {
                        trusted: 3,
                        certified: 0,
                        runtime_checked: 0,
                        failed: 0,
                        unknown: 0,
                    },
                    fingerprint: Some("iter3-allproved".into()),
                    vcs_dispatched: 3,
                    vcs_failed: 0,
                    detailed_results: None,
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Mock strengthen phase: proposes fixes based on remaining failures
// ---------------------------------------------------------------------------

/// Strengthen phase that proposes fixes appropriate to the current failure set.
/// - When 3 failures: proposes fixes for overflow:add and overflow:shift
/// - When 1 failure: proposes fix for overflow:cast
/// - When 0 failures: no proposals
struct GradualStrengthen;

impl StrengthenPhase for GradualStrengthen {
    fn strengthen(&self, _source_path: &Path, verify_output: &VerifyOutput) -> StrengthenOutput {
        match verify_output.vcs_failed {
            3 => {
                // First pass: fix the add and shift overflows
                let proposals = vec![
                    Proposal {
                        function_path: "binary_search".into(),
                        function_name: "binary_search".into(),
                        kind: ProposalKind::SafeArithmetic {
                            original: "(low + high) / 2".into(),
                            replacement: "low + (high - low) / 2".into(),
                        },
                        confidence: 0.95,
                        rationale: "overflow:add — (low + high) can overflow usize".into(),
                    },
                    Proposal {
                        function_path: "binary_search".into(),
                        function_name: "binary_search".into(),
                        kind: ProposalKind::SafeArithmetic {
                            original: "high >> 1".into(),
                            replacement: "high.wrapping_shr(1)".into(),
                        },
                        confidence: 0.85,
                        rationale: "overflow:shift — shift by >= bit width is UB".into(),
                    },
                ];
                StrengthenOutput {
                    has_proposals: true,
                    failures_analyzed: 3,
                    proposals,
                }
            }
            1 => {
                // Second pass: fix the remaining cast overflow
                let proposals = vec![
                    Proposal {
                        function_path: "binary_search".into(),
                        function_name: "binary_search".into(),
                        kind: ProposalKind::SafeArithmetic {
                            original: "mid as i32".into(),
                            replacement: "i32::try_from(mid).expect(\"index fits i32\")".into(),
                        },
                        confidence: 0.90,
                        rationale: "overflow:cast — usize to i32 truncation".into(),
                    },
                ];
                StrengthenOutput {
                    has_proposals: true,
                    failures_analyzed: 1,
                    proposals,
                }
            }
            0 => StrengthenOutput {
                has_proposals: false,
                failures_analyzed: 0,
                proposals: vec![],
            },
            _ => StrengthenOutput {
                has_proposals: false,
                failures_analyzed: verify_output.vcs_failed,
                proposals: vec![],
            },
        }
    }
}

// ---------------------------------------------------------------------------
// Mock backprop phase: tracks applied rewrites
// ---------------------------------------------------------------------------

/// Backprop phase that records which proposals were applied.
struct TrackingBackprop {
    applied_proposals: RefCell<Vec<String>>,
}

impl TrackingBackprop {
    fn new() -> Self {
        Self {
            applied_proposals: RefCell::new(Vec::new()),
        }
    }

    fn applied(&self) -> Vec<String> {
        self.applied_proposals.borrow().clone()
    }
}

impl BackpropPhase for TrackingBackprop {
    fn backpropagate(&self, _source_path: &Path, proposals: &[Proposal]) -> BackpropOutput {
        let mut applied = 0;
        for proposal in proposals {
            self.applied_proposals
                .borrow_mut()
                .push(proposal.rationale.clone());
            applied += 1;
        }
        BackpropOutput {
            applied,
            skipped: 0,
        }
    }
}

// ---------------------------------------------------------------------------
// Golden test: 3-iteration gradual convergence
// ---------------------------------------------------------------------------

#[test]
fn test_golden_binary_search_3iter_convergence() {
    let verify = GradualVerify::new();
    let strengthen = GradualStrengthen;
    let backprop = TrackingBackprop::new();

    let config = LoopConfig {
        max_iterations: 5,
        stable_round_limit: 2,
        allow_rewrite: true,
        run_debug: false,
    };

    let result: LoopResult = run_loop(
        Path::new("examples/binary_search.rs"),
        &config,
        &verify,
        &strengthen,
        &backprop,
    );

    // -- Assertion 1: Loop converges in <= 5 iterations --
    assert!(
        result.iterations <= 5,
        "Loop should converge in <= 5 iterations, got {}",
        result.iterations,
    );

    // -- Assertion 2: Final result has 0 failures --
    assert_eq!(
        result.final_frontier.failed, 0,
        "Final frontier should have 0 failures, got {}",
        result.final_frontier.failed,
    );
    assert_eq!(result.final_frontier.trusted, 3);

    // -- Assertion 3: Terminates with AllProved --
    assert_eq!(
        result.reason,
        TerminationReason::AllProved,
        "Expected AllProved, got {:?}",
        result.reason,
    );

    // -- Assertion 4: Exactly 3 iterations --
    assert_eq!(
        result.iterations, 3,
        "Expected exactly 3 iterations (detect-3, fix-2-remaining-1, all-proved), got {}",
        result.iterations,
    );

    // -- Assertion 5: History tracks all 3 iterations --
    assert_eq!(result.history.len(), 3);

    // Iteration 0: 3 failures, 2 proposals, 2 applied
    let iter0 = &result.history[0];
    assert_eq!(iter0.vcs_failed, 3, "Iter 0: should detect 3 failures");
    assert_eq!(iter0.proposals, 2, "Iter 0: should have 2 proposals (add, shift)");
    assert_eq!(iter0.applied, 2, "Iter 0: should apply 2 fixes");
    assert!(
        matches!(iter0.decision, ConvergenceDecision::Continue { .. }),
        "Iter 0: should continue",
    );

    // Iteration 1: 1 failure, 1 proposal, 1 applied
    let iter1 = &result.history[1];
    assert_eq!(iter1.vcs_failed, 1, "Iter 1: should have 1 failure remaining");
    assert_eq!(iter1.proposals, 1, "Iter 1: should have 1 proposal (cast)");
    assert_eq!(iter1.applied, 1, "Iter 1: should apply 1 fix");
    assert!(
        matches!(iter1.decision, ConvergenceDecision::Continue { .. }),
        "Iter 1: should continue",
    );

    // Iteration 2: 0 failures, all proved
    let iter2 = &result.history[2];
    assert_eq!(iter2.vcs_failed, 0, "Iter 2: should have 0 failures");

    // -- Assertion 6: No regressions between iterations --
    // Trusted count should be monotonically non-decreasing
    for i in 1..result.history.len() {
        assert!(
            result.history[i].frontier.trusted >= result.history[i - 1].frontier.trusted,
            "Regression detected: iter {} trusted ({}) < iter {} trusted ({})",
            i,
            result.history[i].frontier.trusted,
            i - 1,
            result.history[i - 1].frontier.trusted,
        );
    }
    // Failed count should be monotonically non-increasing
    for i in 1..result.history.len() {
        assert!(
            result.history[i].frontier.failed <= result.history[i - 1].frontier.failed,
            "Regression detected: iter {} failed ({}) > iter {} failed ({})",
            i,
            result.history[i].frontier.failed,
            i - 1,
            result.history[i - 1].frontier.failed,
        );
    }

    // -- Assertion 7: Rewrites match expected patterns --
    let applied = backprop.applied();
    assert_eq!(applied.len(), 3, "Should have applied 3 total rewrites");
    assert!(
        applied.iter().any(|r| r.contains("overflow:add")),
        "Should have applied overflow:add fix",
    );
    assert!(
        applied.iter().any(|r| r.contains("overflow:shift")),
        "Should have applied overflow:shift fix",
    );
    assert!(
        applied.iter().any(|r| r.contains("overflow:cast")),
        "Should have applied overflow:cast fix",
    );
}

// ---------------------------------------------------------------------------
// Golden test: regression detection (adding a bug should be caught)
// ---------------------------------------------------------------------------

/// Verify phase that simulates a regression: iteration 0 has 2 failures,
/// iteration 1 has 3 failures (got worse).
struct RegressingVerify {
    call_count: Cell<usize>,
}

impl RegressingVerify {
    fn new() -> Self {
        Self { call_count: Cell::new(0) }
    }
}

impl VerifyPhase for RegressingVerify {
    fn verify(&self, _source_path: &Path) -> VerifyOutput {
        let idx = self.call_count.get();
        self.call_count.set(idx + 1);

        if idx == 0 {
            VerifyOutput {
                frontier: ProofFrontier {
                    trusted: 1,
                    certified: 0,
                    runtime_checked: 0,
                    failed: 2,
                    unknown: 0,
                },
                fingerprint: Some("v1".into()),
                vcs_dispatched: 3,
                vcs_failed: 2,
                detailed_results: None,
            }
        } else {
            // Regression: more failures than before
            VerifyOutput {
                frontier: ProofFrontier {
                    trusted: 0,
                    certified: 0,
                    runtime_checked: 0,
                    failed: 3,
                    unknown: 0,
                },
                fingerprint: Some("v2-regressed".into()),
                vcs_dispatched: 3,
                vcs_failed: 3,
                detailed_results: None,
            }
        }
    }
}

/// Simple strengthen that always proposes 1 fix.
struct SimpleStrengthen;

impl StrengthenPhase for SimpleStrengthen {
    fn strengthen(&self, _: &Path, verify_output: &VerifyOutput) -> StrengthenOutput {
        if verify_output.vcs_failed == 0 {
            return StrengthenOutput {
                has_proposals: false,
                failures_analyzed: 0,
                proposals: vec![],
            };
        }
        StrengthenOutput {
            has_proposals: true,
            failures_analyzed: verify_output.vcs_failed,
            proposals: vec![Proposal {
                function_path: "binary_search".into(),
                function_name: "binary_search".into(),
                kind: ProposalKind::SafeArithmetic {
                    original: "a + b".into(),
                    replacement: "a.wrapping_add(b)".into(),
                },
                confidence: 0.8,
                rationale: "fix attempt".into(),
            }],
        }
    }
}

/// Simple backprop that applies everything.
struct SimpleBackprop;

impl BackpropPhase for SimpleBackprop {
    fn backpropagate(&self, _: &Path, proposals: &[Proposal]) -> BackpropOutput {
        BackpropOutput {
            applied: proposals.len(),
            skipped: 0,
        }
    }
}

#[test]
fn test_golden_regression_detected() {
    let verify = RegressingVerify::new();
    let strengthen = SimpleStrengthen;
    let backprop = SimpleBackprop;

    let config = LoopConfig {
        max_iterations: 5,
        stable_round_limit: 2,
        allow_rewrite: true,
        run_debug: false,
    };

    let result = run_loop(
        Path::new("examples/binary_search.rs"),
        &config,
        &verify,
        &strengthen,
        &backprop,
    );

    // Should detect the regression and stop
    assert_eq!(
        result.reason,
        TerminationReason::Regressed,
        "Loop should detect regression, got {:?}",
        result.reason,
    );
    assert_eq!(result.iterations, 2, "Should stop after 2 iterations");
    assert!(result.final_frontier.failed > 0, "Should end with failures");
}

// ---------------------------------------------------------------------------
// Golden test: mock stderr strings are parseable
// ---------------------------------------------------------------------------

#[test]
fn test_mock_stderr_format() {
    // Verify mock stderr strings have the expected structure
    let stderr1 = mock_compiler::mock_stderr_iter1();
    assert!(stderr1.contains("overflow:add"), "Iter 1 stderr should mention overflow:add");
    assert!(stderr1.contains("overflow:shift"), "Iter 1 stderr should mention overflow:shift");
    assert!(stderr1.contains("overflow:cast"), "Iter 1 stderr should mention overflow:cast");
    // Count failure lines
    let failures_1: usize = stderr1.lines().filter(|l| l.contains("[FAIL]")).count();
    assert_eq!(failures_1, 3, "Iter 1 should have 3 FAIL lines");

    let stderr2 = mock_compiler::mock_stderr_iter2();
    let failures_2: usize = stderr2.lines().filter(|l| l.contains("[FAIL]")).count();
    assert_eq!(failures_2, 1, "Iter 2 should have 1 FAIL line");
    let proved_2: usize = stderr2.lines().filter(|l| l.contains("[PROVED]")).count();
    assert_eq!(proved_2, 2, "Iter 2 should have 2 PROVED lines");

    let stderr3 = mock_compiler::mock_stderr_iter3();
    let failures_3: usize = stderr3.lines().filter(|l| l.contains("[FAIL]")).count();
    assert_eq!(failures_3, 0, "Iter 3 should have 0 FAIL lines");
    let proved_3: usize = stderr3.lines().filter(|l| l.contains("[PROVED]")).count();
    assert_eq!(proved_3, 3, "Iter 3 should have 3 PROVED lines");
}
