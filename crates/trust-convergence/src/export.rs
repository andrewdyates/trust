// trust-convergence/export.rs: Convergence proof export and verification.
//
// Exports a convergence proof summarizing the entire loop run: all iterations,
// frontier deltas, final decision, and a consistency check for auditing.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::{ConvergenceDecision, ConvergenceTracker, FrontierDelta, ProofFrontier, StepVerdict};

/// Errors that can occur when verifying a convergence proof.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum ProofVerificationError {
    #[error("empty proof: no iterations recorded")]
    EmptyProof,
    #[error(
        "iteration sequence is not monotonically increasing: iteration {current} follows {previous}"
    )]
    NonMonotonicIterations { previous: u32, current: u32 },
    #[error("delta mismatch at iteration {iteration}: recorded delta does not match computed delta from frontiers")]
    DeltaMismatch { iteration: u32 },
    #[error("final frontier mismatch: proof final frontier does not match last iteration frontier")]
    FinalFrontierMismatch,
    #[error("decision mismatch: proof claims {claimed:?} but computed {computed:?}")]
    DecisionMismatch {
        claimed: ConvergenceDecisionKind,
        computed: ConvergenceDecisionKind,
    },
}

/// Simplified decision kind for error reporting (avoids carrying full enum payloads).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConvergenceDecisionKind {
    Continue,
    Converged,
    Regressed,
    IterationLimitReached,
}

impl From<&ConvergenceDecision> for ConvergenceDecisionKind {
    fn from(decision: &ConvergenceDecision) -> Self {
        match decision {
            ConvergenceDecision::Continue { .. } => Self::Continue,
            ConvergenceDecision::Converged { .. } => Self::Converged,
            ConvergenceDecision::Regressed { .. } => Self::Regressed,
            ConvergenceDecision::IterationLimitReached { .. } => Self::IterationLimitReached,
        }
    }
}

/// A single iteration record within a convergence proof.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct IterationRecord {
    /// Iteration number.
    pub iteration: u32,
    /// Proof frontier at this iteration.
    pub frontier: SerializableFrontier,
    /// Delta from the previous iteration (None for the first iteration).
    pub delta: Option<SerializableDelta>,
    /// Step verdict compared to previous iteration.
    pub verdict: Option<String>,
    /// Fingerprint if present.
    pub fingerprint: Option<String>,
}

/// Serializable version of `ProofFrontier`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct SerializableFrontier {
    pub trusted: u32,
    pub certified: u32,
    pub runtime_checked: u32,
    pub failed: u32,
    pub unknown: u32,
}

impl From<&ProofFrontier> for SerializableFrontier {
    fn from(f: &ProofFrontier) -> Self {
        Self {
            trusted: f.trusted,
            certified: f.certified,
            runtime_checked: f.runtime_checked,
            failed: f.failed,
            unknown: f.unknown,
        }
    }
}

impl From<&SerializableFrontier> for ProofFrontier {
    fn from(f: &SerializableFrontier) -> Self {
        Self {
            trusted: f.trusted,
            certified: f.certified,
            runtime_checked: f.runtime_checked,
            failed: f.failed,
            unknown: f.unknown,
        }
    }
}

/// Serializable version of `FrontierDelta`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct SerializableDelta {
    pub trusted: i64,
    pub certified: i64,
    pub runtime_checked: i64,
    pub failed: i64,
    pub unknown: i64,
}

impl From<&FrontierDelta> for SerializableDelta {
    fn from(d: &FrontierDelta) -> Self {
        Self {
            trusted: d.trusted,
            certified: d.certified,
            runtime_checked: d.runtime_checked,
            failed: d.failed,
            unknown: d.unknown,
        }
    }
}

impl From<&SerializableDelta> for FrontierDelta {
    fn from(d: &SerializableDelta) -> Self {
        Self {
            trusted: d.trusted,
            certified: d.certified,
            runtime_checked: d.runtime_checked,
            failed: d.failed,
            unknown: d.unknown,
        }
    }
}

/// Complete convergence proof for a loop run.
///
/// Contains every iteration's frontier and delta, plus the final decision.
/// Can be serialized to JSON for persistence and later verified for consistency.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct ConvergenceProof {
    /// All iteration records in order.
    pub iterations: Vec<IterationRecord>,
    /// The final frontier at loop termination.
    pub final_frontier: SerializableFrontier,
    /// Why the loop terminated.
    pub decision: String,
    /// Number of consecutive stable rounds at termination.
    pub stable_rounds: usize,
    /// Whether the fingerprint matched at convergence.
    pub fingerprint_matched: bool,
    /// Total iterations observed.
    pub total_iterations: usize,
}

/// Human-readable convergence summary.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub(crate) struct ProofSummary {
    /// One-line outcome description.
    pub outcome: String,
    /// Total iterations in the proof.
    pub total_iterations: usize,
    /// Final convergence score (proved / total), if applicable.
    pub final_score: Option<f64>,
    /// Net change in static proofs from first to last iteration.
    pub net_proved_delta: i64,
    /// Net change in failures from first to last iteration.
    pub net_failed_delta: i64,
    /// Whether the loop converged to a fixed point.
    pub converged: bool,
}

/// Export a convergence proof from a tracker's history.
///
/// Captures every iteration snapshot, computes deltas, and records the final decision.
#[must_use]
pub(crate) fn export_proof(tracker: &ConvergenceTracker) -> ConvergenceProof {
    let history = tracker.history();
    let mut iterations = Vec::with_capacity(history.len());

    for (i, snapshot) in history.iter().enumerate() {
        let delta = if i > 0 {
            let prev = &history[i - 1];
            let d = snapshot.frontier.delta_from(&prev.frontier);
            Some(SerializableDelta::from(&d))
        } else {
            None
        };

        let verdict = if i > 0 {
            let prev = &history[i - 1];
            let d = snapshot.frontier.delta_from(&prev.frontier);
            Some(classify_verdict(&prev.frontier, &snapshot.frontier, &d))
        } else {
            None
        };

        iterations.push(IterationRecord {
            iteration: snapshot.iteration,
            frontier: SerializableFrontier::from(&snapshot.frontier),
            delta,
            verdict,
            fingerprint: snapshot.fingerprint.clone(),
        });
    }

    let final_frontier = history
        .last()
        .map(|s| SerializableFrontier::from(&s.frontier))
        .unwrap_or(SerializableFrontier {
            trusted: 0,
            certified: 0,
            runtime_checked: 0,
            failed: 0,
            unknown: 0,
        });

    let report = tracker.latest_report();
    let (decision_str, stable_rounds, fingerprint_matched) = match &report {
        Some(r) => (format_decision(&r.decision), r.stable_rounds, r.fingerprint_matched),
        None => ("no observations".to_string(), 0, false),
    };

    ConvergenceProof {
        iterations,
        final_frontier,
        decision: decision_str,
        stable_rounds,
        fingerprint_matched,
        total_iterations: history.len(),
    }
}

/// Verify that a `ConvergenceProof` is internally consistent.
///
/// Checks:
/// 1. Non-empty iteration list
/// 2. Monotonically increasing iteration numbers
/// 3. Deltas match computed differences between consecutive frontiers
/// 4. Final frontier matches the last iteration's frontier
///
/// # Errors
///
/// Returns the first inconsistency found.
pub(crate) fn verify_proof(proof: &ConvergenceProof) -> Result<(), ProofVerificationError> {
    if proof.iterations.is_empty() {
        return Err(ProofVerificationError::EmptyProof);
    }

    // Check monotonic iteration numbers.
    for window in proof.iterations.windows(2) {
        let prev = &window[0];
        let curr = &window[1];
        if curr.iteration <= prev.iteration {
            return Err(ProofVerificationError::NonMonotonicIterations {
                previous: prev.iteration,
                current: curr.iteration,
            });
        }
    }

    // Check delta consistency.
    for i in 1..proof.iterations.len() {
        let prev_frontier: ProofFrontier = ProofFrontier::from(&proof.iterations[i - 1].frontier);
        let curr_frontier: ProofFrontier = ProofFrontier::from(&proof.iterations[i].frontier);
        let computed = curr_frontier.delta_from(&prev_frontier);
        let computed_ser = SerializableDelta::from(&computed);

        if let Some(recorded) = &proof.iterations[i].delta
            && *recorded != computed_ser {
                return Err(ProofVerificationError::DeltaMismatch {
                    iteration: proof.iterations[i].iteration,
                });
            }
    }

    // Check final frontier matches last iteration.
    // SAFETY: verify_proof is called after checking iterations.is_empty() returns Ok(()).
    let last = &proof.iterations.last()
        .unwrap_or_else(|| unreachable!("iterations empty after non-empty validation"));
    if last.frontier != proof.final_frontier {
        return Err(ProofVerificationError::FinalFrontierMismatch);
    }

    Ok(())
}

/// Generate a human-readable summary from a convergence proof.
#[must_use]
pub(crate) fn summarize(proof: &ConvergenceProof) -> ProofSummary {
    let total_iterations = proof.total_iterations;
    let converged = proof.decision.contains("converged");

    let final_score = {
        let f = &proof.final_frontier;
        let total = f.trusted + f.certified + f.runtime_checked + f.failed + f.unknown;
        if total > 0 {
            Some((f.trusted + f.certified) as f64 / total as f64)
        } else {
            None
        }
    };

    let (net_proved_delta, net_failed_delta) = if proof.iterations.len() >= 2 {
        let first = &proof.iterations[0].frontier;
        // SAFETY: iterations.len() >= 2 check is at the top of this if-block.
        let last = &proof.iterations.last()
            .unwrap_or_else(|| unreachable!("iterations empty in len >= 2 block"))
            .frontier;
        let first_proved = (first.trusted + first.certified) as i64;
        let last_proved = (last.trusted + last.certified) as i64;
        let first_failed = first.failed as i64;
        let last_failed = last.failed as i64;
        (last_proved - first_proved, last_failed - first_failed)
    } else {
        (0, 0)
    };

    let outcome = if converged {
        format!(
            "Converged after {} iterations (stable rounds: {}, fingerprint matched: {})",
            total_iterations, proof.stable_rounds, proof.fingerprint_matched
        )
    } else {
        format!(
            "Terminated after {} iterations: {}",
            total_iterations, proof.decision
        )
    };

    ProofSummary {
        outcome,
        total_iterations,
        final_score,
        net_proved_delta,
        net_failed_delta,
        converged,
    }
}

/// Serialize a convergence proof to a JSON string.
///
/// # Errors
///
/// Returns an error if serialization fails (should not happen for valid proofs).
pub(crate) fn to_json(proof: &ConvergenceProof) -> Result<String, serde_json::Error> {
    serde_json::to_string_pretty(proof)
}

/// Deserialize a convergence proof from a JSON string.
///
/// # Errors
///
/// Returns an error if the JSON is malformed or does not match the expected schema.
pub(crate) fn from_json(json: &str) -> Result<ConvergenceProof, serde_json::Error> {
    serde_json::from_str(json)
}

// --- Private helpers ---

fn classify_verdict(
    previous: &ProofFrontier,
    current: &ProofFrontier,
    delta: &FrontierDelta,
) -> String {
    if delta.statically_proved_delta() < 0 {
        return "regressed".to_string();
    }
    if delta.failed > 0 {
        return "regressed".to_string();
    }
    if *current == *previous {
        return "stable".to_string();
    }
    "improved".to_string()
}

fn format_decision(decision: &ConvergenceDecision) -> String {
    match decision {
        ConvergenceDecision::Continue { verdict } => {
            let v = match verdict {
                StepVerdict::Improved => "improved",
                StepVerdict::Stable => "stable",
                StepVerdict::Regressed => "regressed",
            };
            format!("continue ({v})")
        }
        ConvergenceDecision::Converged { stable_rounds, fingerprint_matched } => {
            format!(
                "converged (stable_rounds: {stable_rounds}, fingerprint_matched: {fingerprint_matched})"
            )
        }
        ConvergenceDecision::Regressed { reason } => {
            format!("regressed ({reason:?})")
        }
        ConvergenceDecision::IterationLimitReached { iteration, limit } => {
            format!("iteration limit reached (iteration: {iteration}, limit: {limit})")
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ConvergenceTracker, IterationSnapshot};

    fn frontier(
        trusted: u32,
        certified: u32,
        runtime_checked: u32,
        failed: u32,
        unknown: u32,
    ) -> ProofFrontier {
        ProofFrontier { trusted, certified, runtime_checked, failed, unknown }
    }

    #[test]
    fn test_export_empty_tracker() {
        let tracker = ConvergenceTracker::new(2, 8);
        let proof = export_proof(&tracker);
        assert!(proof.iterations.is_empty());
        assert_eq!(proof.total_iterations, 0);
        assert_eq!(proof.decision, "no observations");
    }

    #[test]
    fn test_export_single_iteration() {
        let mut tracker = ConvergenceTracker::new(2, 8);
        tracker.observe(IterationSnapshot::new(0, frontier(3, 0, 1, 0, 0)));
        let proof = export_proof(&tracker);

        assert_eq!(proof.iterations.len(), 1);
        assert_eq!(proof.total_iterations, 1);
        assert_eq!(proof.final_frontier.trusted, 3);
        assert!(proof.iterations[0].delta.is_none());
        assert!(proof.iterations[0].verdict.is_none());
    }

    #[test]
    fn test_export_convergence() {
        let mut tracker = ConvergenceTracker::new(2, 8);
        tracker.observe(IterationSnapshot::new(0, frontier(3, 0, 1, 0, 0)));
        tracker.observe(IterationSnapshot::new(1, frontier(3, 0, 1, 0, 0)));
        let proof = export_proof(&tracker);

        assert_eq!(proof.iterations.len(), 2);
        assert!(proof.decision.contains("converged"));
        assert_eq!(proof.stable_rounds, 2);

        // Second iteration should have a delta.
        let delta = proof.iterations[1].delta.expect("should have delta");
        assert_eq!(delta.trusted, 0);
        assert_eq!(delta.failed, 0);
    }

    #[test]
    fn test_export_with_improvement() {
        let mut tracker = ConvergenceTracker::new(3, 8);
        tracker.observe(IterationSnapshot::new(0, frontier(1, 0, 2, 1, 0)));
        tracker.observe(IterationSnapshot::new(1, frontier(3, 0, 1, 0, 0)));
        let proof = export_proof(&tracker);

        let delta = proof.iterations[1].delta.expect("delta");
        assert_eq!(delta.trusted, 2);
        assert_eq!(delta.failed, -1);
        assert_eq!(proof.iterations[1].verdict.as_deref(), Some("improved"));
    }

    #[test]
    fn test_export_with_fingerprint() {
        let mut tracker = ConvergenceTracker::new(2, 8);
        tracker.observe(
            IterationSnapshot::new(0, frontier(3, 0, 0, 0, 0)).with_fingerprint("abc123"),
        );
        tracker.observe(
            IterationSnapshot::new(1, frontier(3, 0, 0, 0, 0)).with_fingerprint("abc123"),
        );
        let proof = export_proof(&tracker);

        assert_eq!(proof.iterations[0].fingerprint.as_deref(), Some("abc123"));
        assert!(proof.fingerprint_matched);
    }

    #[test]
    fn test_verify_valid_proof() {
        let mut tracker = ConvergenceTracker::new(2, 8);
        tracker.observe(IterationSnapshot::new(0, frontier(1, 0, 2, 1, 0)));
        tracker.observe(IterationSnapshot::new(1, frontier(3, 0, 1, 0, 0)));
        tracker.observe(IterationSnapshot::new(2, frontier(3, 0, 1, 0, 0)));

        let proof = export_proof(&tracker);
        assert!(verify_proof(&proof).is_ok());
    }

    #[test]
    fn test_verify_empty_proof_fails() {
        let proof = ConvergenceProof {
            iterations: vec![],
            final_frontier: SerializableFrontier {
                trusted: 0,
                certified: 0,
                runtime_checked: 0,
                failed: 0,
                unknown: 0,
            },
            decision: "none".into(),
            stable_rounds: 0,
            fingerprint_matched: false,
            total_iterations: 0,
        };
        assert!(matches!(
            verify_proof(&proof),
            Err(ProofVerificationError::EmptyProof)
        ));
    }

    #[test]
    fn test_verify_non_monotonic_iterations_fails() {
        let proof = ConvergenceProof {
            iterations: vec![
                IterationRecord {
                    iteration: 1,
                    frontier: SerializableFrontier {
                        trusted: 1,
                        certified: 0,
                        runtime_checked: 0,
                        failed: 0,
                        unknown: 0,
                    },
                    delta: None,
                    verdict: None,
                    fingerprint: None,
                },
                IterationRecord {
                    iteration: 0,
                    frontier: SerializableFrontier {
                        trusted: 2,
                        certified: 0,
                        runtime_checked: 0,
                        failed: 0,
                        unknown: 0,
                    },
                    delta: Some(SerializableDelta {
                        trusted: 1,
                        certified: 0,
                        runtime_checked: 0,
                        failed: 0,
                        unknown: 0,
                    }),
                    verdict: Some("improved".into()),
                    fingerprint: None,
                },
            ],
            final_frontier: SerializableFrontier {
                trusted: 2,
                certified: 0,
                runtime_checked: 0,
                failed: 0,
                unknown: 0,
            },
            decision: "continue".into(),
            stable_rounds: 0,
            fingerprint_matched: false,
            total_iterations: 2,
        };
        assert!(matches!(
            verify_proof(&proof),
            Err(ProofVerificationError::NonMonotonicIterations { .. })
        ));
    }

    #[test]
    fn test_verify_delta_mismatch_fails() {
        let proof = ConvergenceProof {
            iterations: vec![
                IterationRecord {
                    iteration: 0,
                    frontier: SerializableFrontier {
                        trusted: 1,
                        certified: 0,
                        runtime_checked: 0,
                        failed: 0,
                        unknown: 0,
                    },
                    delta: None,
                    verdict: None,
                    fingerprint: None,
                },
                IterationRecord {
                    iteration: 1,
                    frontier: SerializableFrontier {
                        trusted: 3,
                        certified: 0,
                        runtime_checked: 0,
                        failed: 0,
                        unknown: 0,
                    },
                    delta: Some(SerializableDelta {
                        trusted: 999, // Wrong: should be 2
                        certified: 0,
                        runtime_checked: 0,
                        failed: 0,
                        unknown: 0,
                    }),
                    verdict: Some("improved".into()),
                    fingerprint: None,
                },
            ],
            final_frontier: SerializableFrontier {
                trusted: 3,
                certified: 0,
                runtime_checked: 0,
                failed: 0,
                unknown: 0,
            },
            decision: "continue".into(),
            stable_rounds: 0,
            fingerprint_matched: false,
            total_iterations: 2,
        };
        assert!(matches!(
            verify_proof(&proof),
            Err(ProofVerificationError::DeltaMismatch { iteration: 1 })
        ));
    }

    #[test]
    fn test_verify_final_frontier_mismatch_fails() {
        let proof = ConvergenceProof {
            iterations: vec![IterationRecord {
                iteration: 0,
                frontier: SerializableFrontier {
                    trusted: 3,
                    certified: 0,
                    runtime_checked: 0,
                    failed: 0,
                    unknown: 0,
                },
                delta: None,
                verdict: None,
                fingerprint: None,
            }],
            final_frontier: SerializableFrontier {
                trusted: 999, // Wrong: should match iteration 0
                certified: 0,
                runtime_checked: 0,
                failed: 0,
                unknown: 0,
            },
            decision: "continue".into(),
            stable_rounds: 0,
            fingerprint_matched: false,
            total_iterations: 1,
        };
        assert!(matches!(
            verify_proof(&proof),
            Err(ProofVerificationError::FinalFrontierMismatch)
        ));
    }

    #[test]
    fn test_json_roundtrip() {
        let mut tracker = ConvergenceTracker::new(2, 8);
        tracker.observe(IterationSnapshot::new(0, frontier(1, 0, 2, 1, 0)));
        tracker.observe(IterationSnapshot::new(1, frontier(3, 0, 1, 0, 0)));
        tracker.observe(IterationSnapshot::new(2, frontier(3, 0, 1, 0, 0)));

        let proof = export_proof(&tracker);
        let json = to_json(&proof).expect("serialize");
        let deserialized = from_json(&json).expect("deserialize");
        assert_eq!(proof, deserialized);

        // Deserialized proof should also verify.
        assert!(verify_proof(&deserialized).is_ok());
    }

    #[test]
    fn test_summarize_converged() {
        let mut tracker = ConvergenceTracker::new(2, 8);
        tracker.observe(IterationSnapshot::new(0, frontier(1, 0, 2, 1, 0)));
        tracker.observe(IterationSnapshot::new(1, frontier(3, 0, 1, 0, 0)));
        tracker.observe(IterationSnapshot::new(2, frontier(3, 0, 1, 0, 0)));

        let proof = export_proof(&tracker);
        let summary = summarize(&proof);

        assert_eq!(summary.total_iterations, 3);
        assert!(summary.converged);
        assert_eq!(summary.net_proved_delta, 2);
        assert_eq!(summary.net_failed_delta, -1);
        assert!(summary.final_score.is_some());
        assert!(summary.outcome.contains("Converged"));
    }

    #[test]
    fn test_summarize_not_converged() {
        let mut tracker = ConvergenceTracker::new(3, 8);
        tracker.observe(IterationSnapshot::new(0, frontier(1, 0, 2, 1, 0)));
        tracker.observe(IterationSnapshot::new(1, frontier(3, 0, 1, 0, 0)));

        let proof = export_proof(&tracker);
        let summary = summarize(&proof);

        assert!(!summary.converged);
        assert!(summary.outcome.contains("Terminated"));
    }

    #[test]
    fn test_summarize_single_iteration() {
        let mut tracker = ConvergenceTracker::new(2, 8);
        tracker.observe(IterationSnapshot::new(0, frontier(5, 0, 0, 0, 0)));

        let proof = export_proof(&tracker);
        let summary = summarize(&proof);

        assert_eq!(summary.total_iterations, 1);
        assert_eq!(summary.net_proved_delta, 0);
        assert_eq!(summary.net_failed_delta, 0);
        assert!((summary.final_score.expect("score") - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_serializable_frontier_roundtrip() {
        let f = frontier(1, 2, 3, 4, 5);
        let sf = SerializableFrontier::from(&f);
        let back = ProofFrontier::from(&sf);
        assert_eq!(f, back);
    }

    #[test]
    fn test_serializable_delta_roundtrip() {
        let d = FrontierDelta {
            trusted: 1,
            certified: -2,
            runtime_checked: 3,
            failed: -4,
            unknown: 5,
        };
        let sd = SerializableDelta::from(&d);
        let back = FrontierDelta::from(&sd);
        assert_eq!(d, back);
    }

    #[test]
    fn test_convergence_decision_kind_mapping() {
        assert_eq!(
            ConvergenceDecisionKind::from(&ConvergenceDecision::Continue {
                verdict: StepVerdict::Improved
            }),
            ConvergenceDecisionKind::Continue
        );
        assert_eq!(
            ConvergenceDecisionKind::from(&ConvergenceDecision::Converged {
                stable_rounds: 2,
                fingerprint_matched: true
            }),
            ConvergenceDecisionKind::Converged
        );
        assert_eq!(
            ConvergenceDecisionKind::from(&ConvergenceDecision::Regressed {
                reason: crate::RegressionReason::FewerStaticProofs
            }),
            ConvergenceDecisionKind::Regressed
        );
        assert_eq!(
            ConvergenceDecisionKind::from(&ConvergenceDecision::IterationLimitReached {
                iteration: 8,
                limit: 8
            }),
            ConvergenceDecisionKind::IterationLimitReached
        );
    }
}
