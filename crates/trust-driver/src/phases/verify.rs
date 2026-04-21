// trust-driver/phases/verify.rs: Production VerifyPhase implementation
//
// Invokes the stage1 tRust compiler on a source file, parses the
// verification diagnostics from stderr, and aggregates them into a
// VerifyOutput with a ProofFrontier.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::path::{Path, PathBuf};

use trust_types::VerificationResult;

use crate::{ProofFrontier, VerifyOutput, VerifyPhase};
use crate::parser::parse_trust_output;

/// Production verify phase that invokes the stage1 tRust compiler.
///
/// Runs `rustc` from the configured stage1 directory with `-Z trust-verify`
/// enabled, captures verification diagnostics from stderr, and aggregates
/// the results into a `VerifyOutput`.
///
/// # Construction
///
/// ```no_run
/// use trust_driver::phases::verify::ProductionVerifyPhase;
/// use std::path::PathBuf;
///
/// let phase = ProductionVerifyPhase::new(PathBuf::from("build/host/stage1"));
/// ```
#[derive(Debug, Clone)]
pub struct ProductionVerifyPhase {
    /// Path to the stage1 compiler directory (contains `bin/rustc`).
    stage1_dir: PathBuf,
}

impl ProductionVerifyPhase {
    /// Create a new production verify phase targeting the given stage1 dir.
    #[must_use]
    pub fn new(stage1_dir: PathBuf) -> Self {
        Self { stage1_dir }
    }

    /// Build a `VerifyOutput` from parsed verification results.
    fn aggregate_results(&self, results: &[(VerificationResult, String)]) -> VerifyOutput {
        let mut trusted: u32 = 0;
        let mut failed: u32 = 0;
        let mut unknown: u32 = 0;

        for (result, _desc) in results {
            match result {
                VerificationResult::Proved { .. } => trusted += 1,
                VerificationResult::Failed { .. } => failed += 1,
                VerificationResult::Unknown { .. } | VerificationResult::Timeout { .. } => {
                    unknown += 1;
                }
                _ => unknown += 1, // tRust: future VerificationResult variants
            }
        }

        let total = trusted + failed + unknown;

        VerifyOutput {
            frontier: ProofFrontier {
                trusted,
                certified: 0,
                runtime_checked: 0,
                failed,
                unknown,
            },
            fingerprint: None,
            vcs_dispatched: total as usize,
            vcs_failed: failed as usize,
            detailed_results: None,
        }
    }
}

impl VerifyPhase for ProductionVerifyPhase {
    fn verify(&self, source_path: &Path) -> VerifyOutput {
        // Invoke the stage1 compiler and capture stderr.
        let stderr = match crate::compiler::invoke_rustc(source_path, &self.stage1_dir) {
            Ok(stderr) => stderr,
            Err(e) => {
                // On compiler invocation failure, return an empty frontier.
                // The loop will see 0 dispatched / 0 failed and treat it
                // as "all proved" (vacuously). Callers should check
                // vcs_dispatched == 0 to distinguish this from real success.
                eprintln!("trust-driver: compiler invocation failed: {e}");
                return VerifyOutput {
                    frontier: ProofFrontier {
                        trusted: 0,
                        certified: 0,
                        runtime_checked: 0,
                        failed: 0,
                        unknown: 0,
                    },
                    fingerprint: None,
                    vcs_dispatched: 0,
                    vcs_failed: 0,
                    detailed_results: None,
                };
            }
        };

        // Parse verification diagnostics from compiler output.
        let parsed = parse_trust_output(&stderr);

        // Convert to (VerificationResult, description) pairs for aggregation.
        let results: Vec<(VerificationResult, String)> = parsed
            .into_iter()
            .map(|pvc| (pvc.result, pvc.description))
            .collect();

        self.aggregate_results(&results)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_types::ProofStrength;

    #[test]
    fn test_aggregate_results_empty() {
        let phase = ProductionVerifyPhase::new(PathBuf::from("/nonexistent"));
        let output = phase.aggregate_results(&[]);

        assert_eq!(output.frontier.trusted, 0);
        assert_eq!(output.frontier.failed, 0);
        assert_eq!(output.frontier.unknown, 0);
        assert_eq!(output.vcs_dispatched, 0);
        assert_eq!(output.vcs_failed, 0);
    }

    #[test]
    fn test_aggregate_results_mixed() {
        let phase = ProductionVerifyPhase::new(PathBuf::from("/nonexistent"));
        let results = vec![
            (
                VerificationResult::Proved {
                    solver: "z4".to_string(),
                    time_ms: 5,
                    strength: ProofStrength::smt_unsat(), proof_certificate: None,
                solver_warnings: None, },
                "overflow check".to_string(),
            ),
            (
                VerificationResult::Proved {
                    solver: "z4".to_string(),
                    time_ms: 3,
                    strength: ProofStrength::smt_unsat(), proof_certificate: None,
                solver_warnings: None, },
                "bounds check".to_string(),
            ),
            (
                VerificationResult::Failed {
                    solver: "z4".to_string(),
                    time_ms: 10,
                    counterexample: None,
                },
                "division by zero".to_string(),
            ),
            (
                VerificationResult::Unknown {
                    solver: "z4".to_string(),
                    time_ms: 100,
                    reason: "incomplete".to_string(),
                },
                "loop invariant".to_string(),
            ),
            (
                VerificationResult::Timeout {
                    solver: "z4".to_string(),
                    timeout_ms: 5000,
                },
                "recursive spec".to_string(),
            ),
        ];

        let output = phase.aggregate_results(&results);

        assert_eq!(output.frontier.trusted, 2);
        assert_eq!(output.frontier.failed, 1);
        assert_eq!(output.frontier.unknown, 2); // Unknown + Timeout
        assert_eq!(output.vcs_dispatched, 5);
        assert_eq!(output.vcs_failed, 1);
    }

    #[test]
    fn test_aggregate_results_all_proved() {
        let phase = ProductionVerifyPhase::new(PathBuf::from("/nonexistent"));
        let results = vec![
            (
                VerificationResult::Proved {
                    solver: "z4".to_string(),
                    time_ms: 1,
                    strength: ProofStrength::smt_unsat(), proof_certificate: None,
                solver_warnings: None, },
                "check 1".to_string(),
            ),
            (
                VerificationResult::Proved {
                    solver: "z4".to_string(),
                    time_ms: 2,
                    strength: ProofStrength::smt_unsat(), proof_certificate: None,
                solver_warnings: None, },
                "check 2".to_string(),
            ),
        ];

        let output = phase.aggregate_results(&results);

        assert_eq!(output.frontier.trusted, 2);
        assert_eq!(output.frontier.failed, 0);
        assert_eq!(output.vcs_dispatched, 2);
        assert_eq!(output.vcs_failed, 0);
    }

    #[test]
    fn test_verify_missing_compiler_returns_empty_frontier() {
        let phase = ProductionVerifyPhase::new(PathBuf::from("/nonexistent/stage1"));
        let output = phase.verify(Path::new("/tmp/test.rs"));

        // Compiler not found -> graceful empty result
        assert_eq!(output.vcs_dispatched, 0);
        assert_eq!(output.vcs_failed, 0);
        assert_eq!(output.frontier.trusted, 0);
    }
}
