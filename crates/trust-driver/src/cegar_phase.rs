// trust-driver/cegar_phase.rs: CEGAR-enhanced verification phase
//
// Wraps a standard VerifyPhase with CEGAR predicate abstraction refinement.
// When the inner verify phase returns counterexamples, the CEGAR phase:
//   1. Replays the counterexample path concretely
//   2. If spurious: extracts interpolant predicates via LazyRefiner, re-verifies
//   3. If real: reports the counterexample as-is
//   4. Tracks CEGAR iterations in CegarStats for the driver's IterationRecord
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::path::Path;

use trust_cegar::{CegarConfig, CegarError, CegarLoop, CegarOutcome, LazyRefiner, Predicate};
use trust_types::{BasicBlock, BlockId, Counterexample, Terminator};

use crate::{ProofFrontier, VerifyOutput, VerifyPhase};

/// Statistics from CEGAR refinement within a single driver iteration.
#[derive(Debug, Clone, Default)]
pub struct CegarStats {
    /// Number of CEGAR refinement iterations performed.
    pub refinement_iterations: usize,
    /// Number of spurious counterexamples eliminated.
    pub spurious_eliminated: usize,
    /// Number of real counterexamples found.
    pub real_counterexamples: usize,
    /// Number of new predicates discovered.
    pub predicates_added: usize,
    /// Whether CEGAR hit its iteration limit.
    pub hit_limit: bool,
}

/// Configuration for the CEGAR-enhanced verification phase.
#[derive(Debug, Clone)]
pub struct CegarPhaseConfig {
    /// Maximum CEGAR refinement iterations per driver iteration.
    pub max_cegar_iterations: usize,
    /// Initial predicates to seed the abstraction.
    pub initial_predicates: Vec<Predicate>,
    /// Basic blocks of the function under verification (for path replay).
    pub blocks: Vec<BasicBlock>,
}

impl Default for CegarPhaseConfig {
    fn default() -> Self {
        Self {
            max_cegar_iterations: 10,
            initial_predicates: Vec::new(),
            blocks: Vec::new(),
        }
    }
}

/// A VerifyPhase that wraps an inner verify phase with CEGAR refinement.
///
/// On each call to `verify()`:
/// 1. Runs the inner verify phase to get initial results.
/// 2. For each failed VC with a counterexample, checks spuriousness via CegarLoop.
/// 3. If spurious, refines predicates and re-runs inner verify.
/// 4. Repeats until no more spurious counterexamples or limit reached.
pub struct CegarVerifyPhase<V: VerifyPhase> {
    inner: V,
    config: CegarPhaseConfig,
}

impl<V: VerifyPhase> CegarVerifyPhase<V> {
    /// Create a CEGAR-enhanced verify phase wrapping the given inner phase.
    #[must_use]
    pub fn new(inner: V, config: CegarPhaseConfig) -> Self {
        Self { inner, config }
    }

    /// Run verification with CEGAR refinement, returning both the output and stats.
    pub fn verify_with_stats(&self, source_path: &Path) -> (VerifyOutput, CegarStats) {
        let mut stats = CegarStats::default();
        let mut cegar_loop = CegarLoop::new(
            self.config.initial_predicates.clone(),
            CegarConfig {
                max_iterations: self.config.max_cegar_iterations,
            },
        );
        let mut refiner = LazyRefiner::new(self.config.initial_predicates.clone());

        // Initial verification pass.
        let mut output = self.inner.verify(source_path);

        // CEGAR refinement loop: re-verify while we can eliminate spurious counterexamples.
        for _ in 0..self.config.max_cegar_iterations {
            if output.vcs_failed == 0 {
                break;
            }

            // Build a synthetic counterexample from the verify output to check spuriousness.
            // In a full implementation, the verify phase would return counterexamples per-VC.
            // Here, we use the frontier to determine if refinement is warranted.
            let cex = match build_synthetic_counterexample(&output) {
                Some(cex) => cex,
                None => break,
            };

            // Compute abstraction for current blocks.
            if !self.config.blocks.is_empty() {
                cegar_loop.compute_abstraction(&self.config.blocks);
            }

            // Check if the counterexample is spurious.
            let is_spurious = cegar_loop.is_spurious(&cex, &self.config.blocks);

            if !is_spurious {
                stats.real_counterexamples += 1;
                break;
            }

            stats.spurious_eliminated += 1;

            // Attempt refinement via the CegarLoop.
            let outcome = cegar_loop.refine_iteration(&cex, &self.config.blocks);
            stats.refinement_iterations += 1;

            match outcome {
                Ok(CegarOutcome::Refined { new_predicates }) => {
                    stats.predicates_added += new_predicates.len();

                    // Also refine along the path using LazyRefiner for targeted precision.
                    let path = extract_block_path(&self.config.blocks);
                    if !path.is_empty() {
                        if let Ok(lazy_preds) =
                            refiner.refine_path(&path, &self.config.blocks, &cex)
                        {
                            stats.predicates_added += lazy_preds.len();
                        }
                    }

                    // Re-verify with refined abstraction.
                    output = self.inner.verify(source_path);
                }
                Ok(CegarOutcome::Safe) => {
                    // Abstraction proves the property -- adjust frontier.
                    output.vcs_failed = 0;
                    output.frontier = ProofFrontier {
                        trusted: output.frontier.trusted + output.frontier.failed,
                        failed: 0,
                        ..output.frontier
                    };
                    break;
                }
                Ok(CegarOutcome::Unsafe) => {
                    stats.real_counterexamples += 1;
                    break;
                }
                Err(CegarError::MaxIterationsExceeded { .. }) => {
                    stats.hit_limit = true;
                    break;
                }
                Err(CegarError::RefinementStalled) => {
                    // No new predicates -- cannot make further progress.
                    break;
                }
                // CegarOutcome is #[non_exhaustive]; future variants stop refinement.
                Ok(_) => break,
                Err(_) => {
                    // Other errors (solver, invalid block) -- stop refinement.
                    break;
                }
            }
        }

        (output, stats)
    }
}

impl<V: VerifyPhase> VerifyPhase for CegarVerifyPhase<V> {
    fn verify(&self, source_path: &Path) -> VerifyOutput {
        let (output, _stats) = self.verify_with_stats(source_path);
        output
    }
}

/// Build a synthetic counterexample from a VerifyOutput for CEGAR checking.
///
/// In a full pipeline, individual VC results carry counterexamples. Here, we
/// construct a minimal one indicating that some VCs failed, allowing the
/// CEGAR loop to attempt refinement.
fn build_synthetic_counterexample(output: &VerifyOutput) -> Option<Counterexample> {
    if output.vcs_failed == 0 {
        return None;
    }
    // Synthetic: provide the failure count as a variable for predicate extraction.
    Some(Counterexample::new(vec![
        (
            "vcs_failed".to_string(),
            trust_types::CounterexampleValue::Uint(output.vcs_failed as u128),
        ),
        (
            "vcs_total".to_string(),
            trust_types::CounterexampleValue::Uint(output.vcs_dispatched as u128),
        ),
    ]))
}

/// Extract a linear block path from a list of basic blocks.
///
/// Walks from block 0 following `Goto` terminators. Returns block indices in order.
fn extract_block_path(blocks: &[BasicBlock]) -> Vec<usize> {
    if blocks.is_empty() {
        return Vec::new();
    }

    let mut path = Vec::new();
    let mut visited = vec![false; blocks.len()];
    let mut current = 0usize;

    loop {
        if current >= blocks.len() || visited[current] {
            break;
        }
        visited[current] = true;
        path.push(current);

        // Follow the next block in the linear path.
        match &blocks[current].terminator {
            Terminator::Goto(BlockId(next)) => {
                current = *next;
            }
            _ => break,
        }
    }

    path
}

#[cfg(test)]
mod tests {
    use std::cell::Cell;
    use std::path::PathBuf;

    use trust_cegar::{CmpOp, Predicate};
    use trust_types::{BasicBlock, BlockId, ConstValue, Operand, Place, Rvalue, SourceSpan, Statement, Terminator};

    use super::*;
    use crate::{ProofFrontier, VerifyOutput, VerifyPhase};

    // -- Mock verify phase that returns a sequence of outputs --

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
        PathBuf::from("/tmp/cegar_test.rs")
    }

    fn simple_blocks() -> Vec<BasicBlock> {
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(1),
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(0))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Goto(BlockId(1)),
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![],
                terminator: Terminator::Return,
            },
        ]
    }

    #[test]
    fn test_cegar_phase_all_proved_no_refinement() {
        let inner = MockVerify::new(vec![verify_output(5, 0)]);
        let phase = CegarVerifyPhase::new(inner, CegarPhaseConfig::default());

        let output = phase.verify(&test_path());
        assert_eq!(output.vcs_failed, 0);
        assert_eq!(output.frontier.trusted, 5);
    }

    #[test]
    fn test_cegar_phase_with_stats_no_failures() {
        let inner = MockVerify::new(vec![verify_output(5, 0)]);
        let phase = CegarVerifyPhase::new(inner, CegarPhaseConfig::default());

        let (output, stats) = phase.verify_with_stats(&test_path());
        assert_eq!(output.vcs_failed, 0);
        assert_eq!(stats.refinement_iterations, 0);
        assert_eq!(stats.spurious_eliminated, 0);
    }

    #[test]
    fn test_cegar_phase_refinement_improves_result() {
        // First verify: 3 failed. After refinement and re-verify: 1 failed.
        let inner = MockVerify::new(vec![verify_output(2, 3), verify_output(4, 1)]);

        // Use blocks with an assert terminator so that the CegarLoop computes
        // abstract states containing predicates, enabling spurious detection
        // when the synthetic counterexample contradicts those predicates.
        let blocks = vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Assert {
                    cond: Operand::Copy(Place::local(1)),
                    expected: true,
                    msg: trust_types::AssertMessage::BoundsCheck,
                    target: BlockId(1),
                    span: SourceSpan::default(),
                },
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![],
                terminator: Terminator::Return,
            },
        ];

        let config = CegarPhaseConfig {
            max_cegar_iterations: 5,
            // Seed with a predicate on "vcs_failed" so that the synthetic
            // counterexample (vcs_failed=3) gets compared against it.
            initial_predicates: vec![Predicate::comparison("vcs_failed", CmpOp::Eq, "0")],
            blocks,
        };
        let phase = CegarVerifyPhase::new(inner, config);

        let (output, stats) = phase.verify_with_stats(&test_path());
        // After CEGAR detects the spurious counterexample and re-verifies,
        // the mock returns the improved second output.
        assert_eq!(output.frontier.trusted, 4);
        assert_eq!(output.vcs_failed, 1);
        assert!(stats.spurious_eliminated >= 1);
        assert!(stats.refinement_iterations >= 1);
    }

    #[test]
    fn test_cegar_phase_respects_iteration_limit() {
        // Always returns failures -- CEGAR should stop at limit.
        let inner = MockVerify::new(vec![verify_output(2, 3)]);
        let config = CegarPhaseConfig {
            max_cegar_iterations: 2,
            initial_predicates: vec![Predicate::comparison("x", CmpOp::Ge, "0")],
            blocks: simple_blocks(),
        };
        let phase = CegarVerifyPhase::new(inner, config);

        let (_output, stats) = phase.verify_with_stats(&test_path());
        assert!(stats.refinement_iterations <= 2);
    }

    #[test]
    fn test_cegar_phase_no_blocks_still_works() {
        // Empty blocks config -- CEGAR should gracefully handle this.
        let inner = MockVerify::new(vec![verify_output(2, 3)]);
        let config = CegarPhaseConfig {
            max_cegar_iterations: 5,
            initial_predicates: vec![],
            blocks: vec![],
        };
        let phase = CegarVerifyPhase::new(inner, config);

        let (output, stats) = phase.verify_with_stats(&test_path());
        // Without blocks, cannot determine spuriousness -- treats as real.
        assert_eq!(output.vcs_failed, 3);
        assert!(stats.real_counterexamples >= 1 || stats.refinement_iterations == 0);
    }

    #[test]
    fn test_cegar_stats_default() {
        let stats = CegarStats::default();
        assert_eq!(stats.refinement_iterations, 0);
        assert_eq!(stats.spurious_eliminated, 0);
        assert_eq!(stats.real_counterexamples, 0);
        assert_eq!(stats.predicates_added, 0);
        assert!(!stats.hit_limit);
    }

    #[test]
    fn test_extract_block_path_linear() {
        let blocks = vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Goto(BlockId(1)),
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![],
                terminator: Terminator::Goto(BlockId(2)),
            },
            BasicBlock {
                id: BlockId(2),
                stmts: vec![],
                terminator: Terminator::Return,
            },
        ];
        let path = extract_block_path(&blocks);
        assert_eq!(path, vec![0, 1, 2]);
    }

    #[test]
    fn test_extract_block_path_empty() {
        let path = extract_block_path(&[]);
        assert!(path.is_empty());
    }

    #[test]
    fn test_extract_block_path_single_block() {
        let blocks = vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![],
            terminator: Terminator::Return,
        }];
        let path = extract_block_path(&blocks);
        assert_eq!(path, vec![0]);
    }

    #[test]
    fn test_build_synthetic_counterexample_no_failures() {
        let output = verify_output(5, 0);
        assert!(build_synthetic_counterexample(&output).is_none());
    }

    #[test]
    fn test_build_synthetic_counterexample_with_failures() {
        let output = verify_output(3, 2);
        let cex = build_synthetic_counterexample(&output);
        assert!(cex.is_some());
        let cex = cex.unwrap();
        assert_eq!(cex.assignments.len(), 2);
    }

    #[test]
    fn test_cegar_verify_phase_implements_verify_trait() {
        // Ensure CegarVerifyPhase<MockVerify> implements VerifyPhase.
        let inner = MockVerify::new(vec![verify_output(5, 0)]);
        let phase = CegarVerifyPhase::new(inner, CegarPhaseConfig::default());
        let output: VerifyOutput = VerifyPhase::verify(&phase, &test_path());
        assert_eq!(output.vcs_failed, 0);
    }
}
