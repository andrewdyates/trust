#![allow(dead_code)]
//! trust-driver/lib.rs: Prove-strengthen-backprop loop orchestration
//!
//! Wires the three-phase loop described in VISION.md (Idea 2):
//!   verify -> strengthen -> backprop -> converge -> repeat
//!
//! Phases are abstracted as traits so that:
//!   1. Tests use lightweight mocks (no real solver or LLM)
//!   2. Production code can plug in trust-vcgen/trust-router, trust-strengthen,
//!      and trust-backprop (when it exists)
//!
//! Author: Andrew Yates <andrew@andrewdyates.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::path::Path;

// tRust #670: Pipeline profiling and benchmarking infrastructure.
pub mod benchmark;
pub mod cached_verify;
pub mod cegar_phase;
pub mod codegen;
pub mod config_bridge;
// tRust #684: File-based prove-strengthen-backprop loop.
pub mod file_loop;
pub mod incremental;
pub mod parallel;
pub mod phases;
pub mod pipeline;
pub mod profiling;
pub mod recovery;
pub mod scheduling;
pub mod testgen;
pub mod verification_loop;
pub(crate) mod compiler;
pub(crate) mod parser;

pub use phases::{ProductionBackpropPhase, ProductionStrengthenPhase, ProductionVerifyPhase};

// ---------------------------------------------------------------------------
// Error types
// ---------------------------------------------------------------------------

/// Errors from the trust-driver orchestration layer.
#[derive(Debug, thiserror::Error)]
pub enum DriverError {
    #[error("rustc not found at `{path}`")]
    RustcNotFound { path: String },

    #[error("source file not found: `{path}`")]
    SourceNotFound { path: String },

    #[error("failed to spawn compiler at `{path}`: {source}")]
    CompilerSpawn {
        path: String,
        source: std::io::Error,
    },

    #[error("compilation failed (exit {exit_code:?}): {stderr}")]
    CompilationFailed {
        exit_code: Option<i32>,
        stderr: String,
    },

    #[error("failed to read config `{path}`: {source}")]
    ConfigRead {
        path: String,
        source: std::io::Error,
    },

    #[error("failed to parse config `{path}`: {message}")]
    ConfigParse { path: String, message: String },
}

pub use trust_convergence::{
    ConvergenceDecision, ConvergenceTracker, ConvergenceVerdict, FrontierDelta,
    IterationSnapshot, ProofFrontier, StepVerdict, VerdictConfig,
};
pub use trust_debug::{DebugReport, SecurityViolation, Severity};
pub use trust_strengthen::{Proposal, StrengthenOutput};
pub use config_bridge::{CliOverrides, ConfigBridge};

// ---------------------------------------------------------------------------
// Phase traits
// ---------------------------------------------------------------------------

/// Verify phase: run VCs through solver backends and return a proof frontier.
pub trait VerifyPhase {
    fn verify(&self, source_path: &Path) -> VerifyOutput;
}

/// Output of the verify phase.
#[derive(Debug, Clone)]
pub struct VerifyOutput {
    /// Aggregate proof counts for this iteration.
    pub frontier: ProofFrontier,
    /// Optional fingerprint for exact-match convergence detection.
    pub fingerprint: Option<String>,
    /// Number of VCs dispatched.
    pub vcs_dispatched: usize,
    /// Number of VCs that failed.
    pub vcs_failed: usize,
    /// Detailed per-function verification results, when available.
    ///
    /// When populated (e.g., from in-process TyCtxt verification), the strengthen
    /// phase uses these real `VcKind` variants to generate VcKind-specific proposals
    /// (overflow bounds, division-by-zero guards, OOB checks, etc.) instead of
    /// falling back to generic `VcKind::Assertion` placeholders.
    pub detailed_results: Option<trust_types::CrateVerificationResult>,
}

/// Strengthen phase: analyze failures and propose specs.
pub trait StrengthenPhase {
    fn strengthen(&self, source_path: &Path, verify_output: &VerifyOutput) -> StrengthenOutput;
}

/// Backprop phase: apply proposed specs to source code.
pub trait BackpropPhase {
    fn backpropagate(&self, source_path: &Path, proposals: &[Proposal]) -> BackpropOutput;
}

/// Output of the backprop phase.
#[derive(Debug, Clone)]
pub struct BackpropOutput {
    /// Number of proposals successfully applied.
    pub applied: usize,
    /// Number of proposals skipped (e.g., conflict, already present).
    pub skipped: usize,
}

/// Debug phase: find violations in the current binary/MIR to discover
/// properties we should be proving. Feeds violations back as new VCs.
pub trait DebugPhase {
    fn find_violations(&self, source_path: &Path) -> DebugOutput;
}

/// Output of the debug phase.
#[derive(Debug, Clone)]
pub struct DebugOutput {
    /// Full debug report with all violations found.
    pub report: DebugReport,
    /// New VCs that should be added to the verify phase.
    pub new_proof_obligations: usize,
    /// Whether any critical/high violations were found.
    pub has_critical: bool,
}

impl DebugOutput {
    pub fn from_report(report: DebugReport) -> Self {
        let has_critical = report.violations.iter().any(|v| {
            matches!(v.severity, Severity::Critical | Severity::High)
        });
        let new_proof_obligations = report.violations.len();
        Self { report, new_proof_obligations, has_critical }
    }
}

// ---------------------------------------------------------------------------
// Loop configuration and result
// ---------------------------------------------------------------------------

/// Configuration for the prove-strengthen-backprop loop.
#[derive(Debug, Clone)]
pub struct LoopConfig {
    /// Maximum number of iterations before stopping.
    pub max_iterations: u32,
    /// Number of consecutive stable rounds before declaring convergence.
    pub stable_round_limit: usize,
    /// Whether backprop is allowed to modify source files.
    pub allow_rewrite: bool,
    /// Whether to run the debug phase (violation discovery) each iteration.
    pub run_debug: bool,
}

impl Default for LoopConfig {
    fn default() -> Self {
        Self {
            max_iterations: 8,
            stable_round_limit: 2,
            allow_rewrite: true,
            run_debug: true,
        }
    }
}

/// Why the loop terminated.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TerminationReason {
    /// Proof frontier converged (stable for N rounds).
    Converged { stable_rounds: usize },
    /// Hit the iteration limit.
    IterationLimit { iterations: u32 },
    /// Proof frontier regressed.
    Regressed,
    /// Strengthen produced no proposals.
    NoProposals,
    /// All VCs already proved on first pass.
    AllProved,
}

/// Result of running the loop.
#[derive(Debug, Clone)]
pub struct LoopResult {
    /// Number of iterations executed.
    pub iterations: u32,
    /// Final proof frontier.
    pub final_frontier: ProofFrontier,
    /// Why the loop stopped.
    pub reason: TerminationReason,
    /// Per-iteration history.
    pub history: Vec<IterationRecord>,
}

/// Record of a single iteration.
#[derive(Debug, Clone)]
pub struct IterationRecord {
    pub iteration: u32,
    pub frontier: ProofFrontier,
    pub vcs_failed: usize,
    pub proposals: usize,
    pub applied: usize,
    pub decision: ConvergenceDecision,
    /// Violations found by debug phase (if enabled).
    pub debug_violations: usize,
    /// Critical/high violations found by debug phase.
    pub debug_critical: bool,
}

// ---------------------------------------------------------------------------
// Loop entry point
// ---------------------------------------------------------------------------

/// Run the prove-strengthen-backprop loop.
///
/// Orchestrates repeated calls to verify -> debug -> strengthen -> backprop,
/// tracking convergence via `ConvergenceTracker`. Stops when:
/// - The proof frontier converges (stable for `stable_round_limit` rounds)
/// - The iteration limit is reached
/// - The frontier regresses
/// - Strengthen produces no proposals (nothing left to try)
/// - All VCs are already proved
///
/// The optional `debug` phase runs after verify to discover violations
/// (injection paths, memory corruption chains, etc.) that the verify
/// phase's VCs may not cover. These violations feed into strengthen
/// as additional proof obligations.
pub fn run_loop(
    source_path: &Path,
    config: &LoopConfig,
    verify: &dyn VerifyPhase,
    strengthen: &dyn StrengthenPhase,
    backprop: &dyn BackpropPhase,
) -> LoopResult {
    run_loop_with_debug(source_path, config, verify, strengthen, backprop, None)
}

/// Run the full loop with an optional debug phase.
pub fn run_loop_with_debug(
    source_path: &Path,
    config: &LoopConfig,
    verify: &dyn VerifyPhase,
    strengthen: &dyn StrengthenPhase,
    backprop: &dyn BackpropPhase,
    debug: Option<&dyn DebugPhase>,
) -> LoopResult {
    let mut tracker = ConvergenceTracker::new(config.stable_round_limit, config.max_iterations);
    let mut history = Vec::new();
    let mut iteration: u32 = 0;

    loop {
        // Phase 1: Verify
        let v_out = verify.verify(source_path);

        // Phase 1.5: Debug — find violations the verify phase may miss
        let d_out = if config.run_debug {
            debug.map(|d| d.find_violations(source_path))
        } else {
            None
        };
        let (debug_violations, debug_critical) = match &d_out {
            Some(d) => (d.new_proof_obligations, d.has_critical),
            None => (0, false),
        };

        // Phase 2: Check convergence
        let snapshot = match &v_out.fingerprint {
            Some(fp) => {
                IterationSnapshot::new(iteration, v_out.frontier.clone()).with_fingerprint(fp)
            }
            None => IterationSnapshot::new(iteration, v_out.frontier.clone()),
        };
        let decision = tracker.observe(snapshot);

        // Early exit: all proved AND no debug violations
        if v_out.vcs_failed == 0 && !debug_critical {
            history.push(IterationRecord {
                iteration,
                frontier: v_out.frontier.clone(),
                vcs_failed: 0,
                proposals: 0,
                applied: 0,
                decision: decision.clone(),
                debug_violations,
                debug_critical,
            });
            return LoopResult {
                iterations: iteration + 1,
                final_frontier: v_out.frontier,
                reason: TerminationReason::AllProved,
                history,
            };
        }

        match &decision {
            ConvergenceDecision::Converged { stable_rounds, .. } => {
                history.push(IterationRecord {
                    iteration,
                    frontier: v_out.frontier.clone(),
                    vcs_failed: v_out.vcs_failed,
                    proposals: 0,
                    applied: 0,
                    decision: decision.clone(),
                    debug_violations,
                    debug_critical,
                });
                return LoopResult {
                    iterations: iteration + 1,
                    final_frontier: v_out.frontier,
                    reason: TerminationReason::Converged {
                        stable_rounds: *stable_rounds,
                    },
                    history,
                };
            }
            ConvergenceDecision::IterationLimitReached { .. } => {
                history.push(IterationRecord {
                    iteration,
                    frontier: v_out.frontier.clone(),
                    vcs_failed: v_out.vcs_failed,
                    proposals: 0,
                    applied: 0,
                    decision: decision.clone(),
                    debug_violations,
                    debug_critical,
                });
                return LoopResult {
                    iterations: iteration + 1,
                    final_frontier: v_out.frontier,
                    reason: TerminationReason::IterationLimit {
                        iterations: iteration + 1,
                    },
                    history,
                };
            }
            ConvergenceDecision::Regressed { .. } => {
                history.push(IterationRecord {
                    iteration,
                    frontier: v_out.frontier.clone(),
                    vcs_failed: v_out.vcs_failed,
                    proposals: 0,
                    applied: 0,
                    decision: decision.clone(),
                    debug_violations,
                    debug_critical,
                });
                return LoopResult {
                    iterations: iteration + 1,
                    final_frontier: v_out.frontier,
                    reason: TerminationReason::Regressed,
                    history,
                };
            }
            ConvergenceDecision::Continue { .. } => {
                // Continue to strengthen + backprop
            }
        }

        // Phase 3: Strengthen — analyze failures and propose specs
        let s_out = strengthen.strengthen(source_path, &v_out);

        if !s_out.has_proposals {
            history.push(IterationRecord {
                iteration,
                frontier: v_out.frontier.clone(),
                vcs_failed: v_out.vcs_failed,
                proposals: 0,
                applied: 0,
                decision,
                debug_violations,
                debug_critical,
            });
            return LoopResult {
                iterations: iteration + 1,
                final_frontier: v_out.frontier,
                reason: TerminationReason::NoProposals,
                history,
            };
        }

        // Phase 4: Backprop — apply proposals to source
        let b_out = if config.allow_rewrite {
            backprop.backpropagate(source_path, &s_out.proposals)
        } else {
            BackpropOutput {
                applied: 0,
                skipped: s_out.proposals.len(),
            }
        };

        history.push(IterationRecord {
            iteration,
            frontier: v_out.frontier.clone(),
            vcs_failed: v_out.vcs_failed,
            proposals: s_out.proposals.len(),
            applied: b_out.applied,
            decision,
            debug_violations,
            debug_critical,
        });

        // If nothing was applied and rewrite is enabled, treat as no-proposals
        if config.allow_rewrite && b_out.applied == 0 {
            return LoopResult {
                iterations: iteration + 1,
                final_frontier: v_out.frontier,
                reason: TerminationReason::NoProposals,
                history,
            };
        }

        iteration += 1;
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::Cell;
    use std::path::PathBuf;

    // -- Mock phases --------------------------------------------------------

    /// A verify phase that returns a sequence of pre-programmed outputs.
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
            // Clamp to last output if we run past the sequence
            self.outputs[idx.min(self.outputs.len() - 1)].clone()
        }
    }

    /// A strengthen phase that always produces a fixed number of proposals.
    struct MockStrengthen {
        proposal_count: usize,
    }

    impl StrengthenPhase for MockStrengthen {
        fn strengthen(&self, _: &Path, _: &VerifyOutput) -> StrengthenOutput {
            let proposals: Vec<Proposal> = (0..self.proposal_count)
                .map(|i| Proposal {
                    function_path: format!("test::fn_{i}"),
                    function_name: format!("fn_{i}"),
                    kind: trust_strengthen::ProposalKind::AddPrecondition {
                        spec_body: format!("x > {i}"),
                    },
                    confidence: 0.9,
                    rationale: format!("mock proposal {i}"),
                })
                .collect();
            StrengthenOutput {
                has_proposals: !proposals.is_empty(),
                failures_analyzed: self.proposal_count,
                proposals,
            }
        }
    }

    /// A strengthen phase that returns no proposals.
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

    /// A backprop phase that "applies" all proposals.
    struct MockBackprop;

    impl BackpropPhase for MockBackprop {
        fn backpropagate(&self, _: &Path, proposals: &[Proposal]) -> BackpropOutput {
            BackpropOutput {
                applied: proposals.len(),
                skipped: 0,
            }
        }
    }

    /// A backprop phase that applies nothing.
    struct NoOpBackprop;

    impl BackpropPhase for NoOpBackprop {
        fn backpropagate(&self, _: &Path, proposals: &[Proposal]) -> BackpropOutput {
            BackpropOutput {
                applied: 0,
                skipped: proposals.len(),
            }
        }
    }

    // -- Helpers -------------------------------------------------------------

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
        PathBuf::from("/tmp/test.rs")
    }

    // -- Test cases ----------------------------------------------------------

    #[test]
    fn test_all_proved_first_pass() {
        let verify = MockVerify::new(vec![verify_output(5, 0)]);
        let strengthen = EmptyStrengthen;
        let backprop = MockBackprop;
        let config = LoopConfig::default();

        let result = run_loop(&test_path(), &config, &verify, &strengthen, &backprop);

        assert_eq!(result.iterations, 1);
        assert_eq!(result.reason, TerminationReason::AllProved);
        assert_eq!(result.final_frontier.trusted, 5);
        assert_eq!(result.final_frontier.failed, 0);
    }

    #[test]
    fn test_converges_after_improvement() {
        // Iteration 0: 2 proved, 3 failed -> improve
        // Iteration 1: 4 proved, 1 failed -> improve
        // Iteration 2: 4 proved, 1 failed -> stable (same as iter 1)
        // stable_round_limit=2 -> converged
        let verify = MockVerify::new(vec![
            verify_output(2, 3),
            verify_output(4, 1),
            verify_output(4, 1),
        ]);
        let strengthen = MockStrengthen { proposal_count: 2 };
        let backprop = MockBackprop;
        let config = LoopConfig {
            max_iterations: 10,
            stable_round_limit: 2,
            allow_rewrite: true,
            run_debug: false,
        };

        let result = run_loop(&test_path(), &config, &verify, &strengthen, &backprop);

        assert_eq!(result.iterations, 3);
        assert_eq!(
            result.reason,
            TerminationReason::Converged { stable_rounds: 2 }
        );
        assert_eq!(result.final_frontier.trusted, 4);
        assert_eq!(result.final_frontier.failed, 1);
        assert_eq!(result.history.len(), 3);
    }

    #[test]
    fn test_iteration_limit() {
        // Iterations 0, 1, 2 each improve. Iteration 3 hits the limit (>= 3).
        // ConvergenceTracker uses iteration >= limit, so 4 total calls to verify.
        let verify = MockVerify::new(vec![
            verify_output(1, 4),
            verify_output(2, 3),
            verify_output(3, 2),
            verify_output(4, 1),
        ]);
        let strengthen = MockStrengthen { proposal_count: 1 };
        let backprop = MockBackprop;
        let config = LoopConfig {
            max_iterations: 3,
            stable_round_limit: 2,
            allow_rewrite: true,
            run_debug: false,
        };

        let result = run_loop(&test_path(), &config, &verify, &strengthen, &backprop);

        assert_eq!(result.iterations, 4);
        assert_eq!(
            result.reason,
            TerminationReason::IterationLimit { iterations: 4 }
        );
    }

    #[test]
    fn test_regression_stops_loop() {
        // Iteration 0: 4 proved, 1 failed
        // Iteration 1: 3 proved, 2 failed -> regression!
        let verify = MockVerify::new(vec![verify_output(4, 1), verify_output(3, 2)]);
        let strengthen = MockStrengthen { proposal_count: 1 };
        let backprop = MockBackprop;
        let config = LoopConfig::default();

        let result = run_loop(&test_path(), &config, &verify, &strengthen, &backprop);

        assert_eq!(result.iterations, 2);
        assert_eq!(result.reason, TerminationReason::Regressed);
        assert_eq!(result.final_frontier.trusted, 3);
    }

    #[test]
    fn test_no_proposals_stops_loop() {
        let verify = MockVerify::new(vec![verify_output(2, 3)]);
        let strengthen = EmptyStrengthen;
        let backprop = MockBackprop;
        let config = LoopConfig::default();

        let result = run_loop(&test_path(), &config, &verify, &strengthen, &backprop);

        assert_eq!(result.iterations, 1);
        assert_eq!(result.reason, TerminationReason::NoProposals);
    }

    #[test]
    fn test_rewrite_disabled_skips_backprop() {
        let verify = MockVerify::new(vec![verify_output(2, 3)]);
        let strengthen = MockStrengthen { proposal_count: 2 };
        let backprop = MockBackprop;
        let config = LoopConfig {
            allow_rewrite: false,
            run_debug: false,
            ..Default::default()
        };

        let result = run_loop(&test_path(), &config, &verify, &strengthen, &backprop);

        // With rewrite disabled, proposals are generated but not applied.
        // The loop records 0 applied and continues — but since allow_rewrite
        // is false, the "applied == 0" check is skipped and we don't terminate
        // on NoProposals for that reason. Instead the loop continues.
        // With the same frontier each time and stable_round_limit=2,
        // iteration 1 will converge.
        assert!(result.iterations >= 1);
        // Check that the first iteration had proposals but 0 applied
        assert_eq!(result.history[0].proposals, 2);
        assert_eq!(result.history[0].applied, 0);
    }

    #[test]
    fn test_backprop_applies_nothing_stops() {
        // Strengthen returns proposals but backprop can't apply any
        let verify = MockVerify::new(vec![verify_output(2, 3)]);
        let strengthen = MockStrengthen { proposal_count: 2 };
        let backprop = NoOpBackprop;
        let config = LoopConfig {
            allow_rewrite: true,
            run_debug: false,
            ..Default::default()
        };

        let result = run_loop(&test_path(), &config, &verify, &strengthen, &backprop);

        assert_eq!(result.iterations, 1);
        assert_eq!(result.reason, TerminationReason::NoProposals);
        assert_eq!(result.history[0].proposals, 2);
        assert_eq!(result.history[0].applied, 0);
    }

    #[test]
    fn test_history_tracks_all_iterations() {
        let verify = MockVerify::new(vec![
            verify_output(1, 4),
            verify_output(2, 3),
            verify_output(3, 2),
            verify_output(3, 2), // converge
        ]);
        let strengthen = MockStrengthen { proposal_count: 1 };
        let backprop = MockBackprop;
        let config = LoopConfig {
            max_iterations: 10,
            stable_round_limit: 2,
            allow_rewrite: true,
            run_debug: false,
        };

        let result = run_loop(&test_path(), &config, &verify, &strengthen, &backprop);

        assert_eq!(result.history.len(), result.iterations as usize);
        // Verify frontier progression in history
        assert_eq!(result.history[0].frontier.trusted, 1);
        assert_eq!(result.history[1].frontier.trusted, 2);
        assert_eq!(result.history[2].frontier.trusted, 3);
        assert_eq!(result.history[3].frontier.trusted, 3);
    }

    #[test]
    fn test_single_iteration_limit() {
        let verify = MockVerify::new(vec![verify_output(2, 3)]);
        let strengthen = MockStrengthen { proposal_count: 1 };
        let backprop = MockBackprop;
        let config = LoopConfig {
            max_iterations: 1,
            stable_round_limit: 2,
            allow_rewrite: true,
            run_debug: false,
        };

        let result = run_loop(&test_path(), &config, &verify, &strengthen, &backprop);

        // With max_iterations=1, the tracker's iteration_limit is 1.
        // iteration=0 is first observation, continue.
        // After backprop, iteration becomes 1.
        // iteration=1: tracker sees iteration 1 >= limit 1 -> IterationLimitReached
        assert_eq!(result.iterations, 2);
        assert_eq!(
            result.reason,
            TerminationReason::IterationLimit { iterations: 2 }
        );
    }

    #[test]
    fn test_fingerprint_convergence() {
        // Same frontier and fingerprint -> converges in 2 rounds
        let mut out1 = verify_output(3, 1);
        out1.fingerprint = Some("abc123".into());
        let mut out2 = verify_output(3, 1);
        out2.fingerprint = Some("abc123".into());

        let verify = MockVerify::new(vec![out1, out2]);
        let strengthen = MockStrengthen { proposal_count: 1 };
        let backprop = MockBackprop;
        let config = LoopConfig {
            max_iterations: 10,
            stable_round_limit: 2,
            allow_rewrite: true,
            run_debug: false,
        };

        let result = run_loop(&test_path(), &config, &verify, &strengthen, &backprop);

        assert_eq!(result.iterations, 2);
        assert_eq!(
            result.reason,
            TerminationReason::Converged { stable_rounds: 2 }
        );
    }

    #[test]
    fn test_default_config() {
        let config = LoopConfig::default();
        assert_eq!(config.max_iterations, 8);
        assert_eq!(config.stable_round_limit, 2);
        assert!(config.allow_rewrite);
    }
}

// -- Debug phase integration tests --

#[cfg(test)]
mod debug_tests {
    use super::*;
    use std::cell::Cell;
    use std::path::PathBuf;

    struct MockVerify {
        outputs: Vec<VerifyOutput>,
        call_count: Cell<usize>,
    }

    impl MockVerify {
        fn new(outputs: Vec<VerifyOutput>) -> Self {
            Self { outputs, call_count: Cell::new(0) }
        }
    }

    impl VerifyPhase for MockVerify {
        fn verify(&self, _: &Path) -> VerifyOutput {
            let idx = self.call_count.get();
            self.call_count.set(idx + 1);
            self.outputs[idx.min(self.outputs.len() - 1)].clone()
        }
    }

    struct MockStrengthen { count: usize }

    impl StrengthenPhase for MockStrengthen {
        fn strengthen(&self, _: &Path, _: &VerifyOutput) -> StrengthenOutput {
            let proposals: Vec<Proposal> = (0..self.count)
                .map(|i| Proposal {
                    function_path: format!("test::fn_{i}"),
                    function_name: format!("fn_{i}"),
                    kind: trust_strengthen::ProposalKind::AddPrecondition {
                        spec_body: format!("x > {i}"),
                    },
                    confidence: 0.9,
                    rationale: format!("mock {i}"),
                })
                .collect();
            StrengthenOutput {
                has_proposals: !proposals.is_empty(),
                failures_analyzed: self.count,
                proposals,
            }
        }
    }

    struct MockBackprop;
    impl BackpropPhase for MockBackprop {
        fn backpropagate(&self, _: &Path, proposals: &[Proposal]) -> BackpropOutput {
            BackpropOutput { applied: proposals.len(), skipped: 0 }
        }
    }

    /// A debug phase that finds a configurable number of violations.
    struct MockDebug {
        violations: usize,
        has_critical: bool,
    }

    impl DebugPhase for MockDebug {
        fn find_violations(&self, _: &Path) -> DebugOutput {
            use trust_debug::{DebugSummary, SecurityViolationKind};
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
                    description: format!("mock violation {i}"),
                    flow_path: vec![],
                    counterexample: None,
                    solver: "mock".to_string(),
                    time_ms: 0,
                })
                .collect();
            let report = DebugReport {
                target: "test".to_string(),
                violations: violations.clone(),
                chains: vec![],
                summary: DebugSummary::from_violations(&violations, &[]),
            };
            DebugOutput::from_report(report)
        }
    }

    fn verify_output(trusted: u32, failed: u32) -> VerifyOutput {
        VerifyOutput {
            frontier: ProofFrontier { trusted, certified: 0, runtime_checked: 0, failed, unknown: 0 },
            fingerprint: None,
            vcs_dispatched: (trusted + failed) as usize,
            vcs_failed: failed as usize,
            detailed_results: None,
        }
    }

    #[test]
    fn test_debug_phase_records_violations() {
        let verify = MockVerify::new(vec![verify_output(3, 2), verify_output(3, 2)]);
        let strengthen = MockStrengthen { count: 1 };
        let backprop = MockBackprop;
        let debug = MockDebug { violations: 5, has_critical: true };
        let config = LoopConfig {
            max_iterations: 10,
            stable_round_limit: 2,
            allow_rewrite: true,
            run_debug: true,
        };

        let result = run_loop_with_debug(
            &PathBuf::from("/tmp/test.rs"),
            &config,
            &verify,
            &strengthen,
            &backprop,
            Some(&debug),
        );

        // Debug violations should be recorded in history
        assert!(result.history[0].debug_violations > 0);
        assert!(result.history[0].debug_critical);
    }

    #[test]
    fn test_debug_critical_prevents_all_proved() {
        // VCs all pass (0 failed) but debug finds critical violations
        let verify = MockVerify::new(vec![verify_output(5, 0)]);
        let strengthen = MockStrengthen { count: 1 };
        let backprop = MockBackprop;
        let debug = MockDebug { violations: 2, has_critical: true };
        let config = LoopConfig {
            max_iterations: 3,
            stable_round_limit: 2,
            allow_rewrite: true,
            run_debug: true,
        };

        let result = run_loop_with_debug(
            &PathBuf::from("/tmp/test.rs"),
            &config,
            &verify,
            &strengthen,
            &backprop,
            Some(&debug),
        );

        // Should NOT return AllProved because debug found critical violations
        assert_ne!(result.reason, TerminationReason::AllProved);
        assert!(result.history[0].debug_critical);
    }

    #[test]
    fn test_debug_disabled_no_violations() {
        let verify = MockVerify::new(vec![verify_output(5, 0)]);
        let strengthen = MockStrengthen { count: 0 };
        let backprop = MockBackprop;
        let debug = MockDebug { violations: 10, has_critical: true };
        let config = LoopConfig {
            max_iterations: 3,
            stable_round_limit: 2,
            allow_rewrite: true,
            run_debug: false,
        };

        let result = run_loop_with_debug(
            &PathBuf::from("/tmp/test.rs"),
            &config,
            &verify,
            &strengthen,
            &backprop,
            Some(&debug),
        );

        // Debug is disabled, so violations should be 0
        assert_eq!(result.history[0].debug_violations, 0);
        assert!(!result.history[0].debug_critical);
        // All VCs proved and no debug violations -> AllProved
        assert_eq!(result.reason, TerminationReason::AllProved);
    }
}

// -- Stub phase integration tests (mirrors main.rs --loop code path) --

#[cfg(test)]
mod loop_integration_tests {
    use super::*;
    use std::path::PathBuf;
    use verification_loop::{VerificationLoop, VerificationLoopConfig};

    /// Stub verify phase that returns all-verified (0 failures).
    /// Mirrors the StubVerifyPhase in main.rs when all VCs pass.
    struct AllVerifiedStub;

    impl VerifyPhase for AllVerifiedStub {
        fn verify(&self, _: &Path) -> VerifyOutput {
            VerifyOutput {
                frontier: ProofFrontier {
                    trusted: 5,
                    certified: 0,
                    runtime_checked: 0,
                    failed: 0,
                    unknown: 0,
                },
                fingerprint: None,
                vcs_dispatched: 5,
                vcs_failed: 0,
                detailed_results: None,
            }
        }
    }

    /// Stub verify phase that returns some failures.
    struct SomeFailuresStub;

    impl VerifyPhase for SomeFailuresStub {
        fn verify(&self, _: &Path) -> VerifyOutput {
            VerifyOutput {
                frontier: ProofFrontier {
                    trusted: 3,
                    certified: 0,
                    runtime_checked: 0,
                    failed: 2,
                    unknown: 0,
                },
                fingerprint: None,
                vcs_dispatched: 5,
                vcs_failed: 2,
                detailed_results: None,
            }
        }
    }

    /// Stub strengthen that returns no proposals (mirrors main.rs StubStrengthenPhase).
    struct NoProposalStrengthen;

    impl StrengthenPhase for NoProposalStrengthen {
        fn strengthen(&self, _: &Path, _: &VerifyOutput) -> StrengthenOutput {
            StrengthenOutput {
                has_proposals: false,
                failures_analyzed: 0,
                proposals: vec![],
            }
        }
    }

    /// Stub backprop that applies nothing (mirrors main.rs StubBackpropPhase).
    struct NoOpBackprop;

    impl BackpropPhase for NoOpBackprop {
        fn backpropagate(&self, _: &Path, proposals: &[Proposal]) -> BackpropOutput {
            BackpropOutput {
                applied: 0,
                skipped: proposals.len(),
            }
        }
    }

    #[test]
    fn test_loop_with_stubs_all_verified() {
        // When all VCs pass on the first iteration, the loop should return Verified.
        // This mirrors the --loop path in main.rs when the crate has no failures.
        let verify = AllVerifiedStub;
        let strengthen = NoProposalStrengthen;
        let backprop = NoOpBackprop;

        let config = VerificationLoopConfig {
            run_debug: false,
            ..Default::default()
        };
        let mut vloop = VerificationLoop::new(config, &verify, &strengthen, &backprop);
        let (outcome, history) = vloop.run(&PathBuf::from("/tmp/stub_test.rs"));

        assert_eq!(
            outcome,
            verification_loop::LoopOutcome::Verified {
                iterations: 1,
                vcs_proved: 5,
            }
        );
        assert_eq!(history.len(), 1);
        assert_eq!(history[0].vcs_failed, 0);
    }

    #[test]
    fn test_loop_with_stubs_refuted_no_proposals() {
        // When VCs fail and no proposals are generated, the loop should return Refuted.
        // This mirrors the --loop path when strengthen has no suggestions.
        let verify = SomeFailuresStub;
        let strengthen = NoProposalStrengthen;
        let backprop = NoOpBackprop;

        let config = VerificationLoopConfig {
            run_debug: false,
            ..Default::default()
        };
        let mut vloop = VerificationLoop::new(config, &verify, &strengthen, &backprop);
        let (outcome, history) = vloop.run(&PathBuf::from("/tmp/stub_test.rs"));

        assert_eq!(
            outcome,
            verification_loop::LoopOutcome::Refuted {
                iterations: 1,
                vcs_failed: 2,
                exhausted_proposals: true,
            }
        );
        assert_eq!(history.len(), 1);
        assert_eq!(history[0].vcs_failed, 2);
        assert_eq!(history[0].frontier.trusted, 3);
    }
}
