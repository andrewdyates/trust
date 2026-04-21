// Rewrite loop orchestration for `cargo trust build --rewrite`.
//
// Implements the prove-strengthen-backprop convergence loop as a CLI
// orchestrator. Each iteration:
//   1. Invoke rustc (prove) and parse verification results
//   2. Analyze failures and propose rewrites (strengthen)
//   3. Apply rewrites to source via trust-backprop (backprop)
//   4. Check convergence
//
// Uses trust-backprop for AST-aware source rewriting with governance controls.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_backprop::{apply_plan, GovernancePolicy, RewriteTracker};
use trust_backprop::file_io::apply_plan_to_files;
use trust_strengthen::{Proposal, ProposalKind};

use crate::types::{VerificationOutcome, VerificationResult};

// ---------------------------------------------------------------------------
// Convergence tracking
// ---------------------------------------------------------------------------

/// Proof frontier snapshot for one iteration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ProofFrontier {
    pub(crate) proved: usize,
    pub(crate) failed: usize,
    pub(crate) unknown: usize,
}

impl ProofFrontier {
    pub(crate) fn from_results(results: &[VerificationResult]) -> Self {
        let proved = results
            .iter()
            .filter(|r| r.outcome == VerificationOutcome::Proved)
            .count();
        let failed = results
            .iter()
            .filter(|r| r.outcome == VerificationOutcome::Failed)
            .count();
        let unknown = results
            .iter()
            .filter(|r| r.outcome == VerificationOutcome::Unknown)
            .count();
        Self {
            proved,
            failed,
            unknown,
        }
    }

    pub(crate) fn total(&self) -> usize {
        self.proved + self.failed + self.unknown
    }
}

/// Decision after comparing two frontiers.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum LoopDecision {
    /// Keep iterating, with a description of what happened.
    Continue { verdict: &'static str },
    /// Proof frontier converged (same results for `stable_rounds` iterations).
    Converged { stable_rounds: usize },
    /// Proof frontier regressed (more failures or fewer proofs).
    Regressed { reason: &'static str },
    /// Hit the iteration limit.
    IterationLimitReached,
}

/// Lightweight convergence tracker for the rewrite loop.
pub(crate) struct ConvergenceTracker {
    history: Vec<ProofFrontier>,
    max_iterations: usize,
    stable_limit: usize,
}

impl ConvergenceTracker {
    pub(crate) fn new(max_iterations: usize) -> Self {
        Self {
            history: Vec::new(),
            max_iterations,
            stable_limit: 2,
        }
    }

    /// Record a new frontier and return the convergence decision.
    pub(crate) fn observe(&mut self, frontier: ProofFrontier) -> LoopDecision {
        self.history.push(frontier);
        let iteration = self.history.len();

        if iteration >= self.max_iterations {
            return LoopDecision::IterationLimitReached;
        }

        if iteration < 2 {
            return LoopDecision::Continue {
                verdict: "first iteration",
            };
        }

        let current = &self.history[iteration - 1];
        let previous = &self.history[iteration - 2];

        // Check for regression.
        if current.proved < previous.proved {
            return LoopDecision::Regressed {
                reason: "fewer proofs than previous iteration",
            };
        }
        if current.failed > previous.failed {
            return LoopDecision::Regressed {
                reason: "more failures than previous iteration",
            };
        }

        // Check for stability / convergence.
        let stable_rounds = self.trailing_stable_rounds();
        if stable_rounds >= self.stable_limit {
            return LoopDecision::Converged { stable_rounds };
        }

        if current == previous {
            LoopDecision::Continue {
                verdict: "stable (no change)",
            }
        } else {
            LoopDecision::Continue {
                verdict: "improved",
            }
        }
    }

    fn trailing_stable_rounds(&self) -> usize {
        if self.history.len() < 2 {
            return 1;
        }
        let current = self.history.last().expect("invariant: non-empty history");
        let mut count = 1;
        for prev in self.history.iter().rev().skip(1) {
            if prev == current {
                count += 1;
            } else {
                break;
            }
        }
        count
    }

    pub(crate) fn iteration_count(&self) -> usize {
        self.history.len()
    }
}

// ---------------------------------------------------------------------------
// Rewrite plan (lightweight version of trust-backprop types)
// ---------------------------------------------------------------------------

/// A proposed source rewrite from analyzing verification failures.
#[derive(Debug, Clone)]
#[allow(dead_code)] // Fields used for display and future rewrite application.
pub(crate) struct RewriteProposal {
    pub(crate) function: String,
    pub(crate) kind: String,
    pub(crate) description: String,
}

/// Analyze verification failures and propose rewrites.
///
/// This is the CLI-level equivalent of trust-strengthen. It maps failed VCs
/// to rewrite proposals based on the failure kind (overflow, div-by-zero, etc.).
pub(crate) fn propose_rewrites(failures: &[VerificationResult]) -> Vec<RewriteProposal> {
    failures
        .iter()
        .filter(|r| r.outcome == VerificationOutcome::Failed)
        .map(|r| {
            let (kind, description) = classify_failure(r);
            RewriteProposal {
                function: extract_function_name(&r.raw_line),
                kind: kind.to_string(),
                description: description.to_string(),
            }
        })
        .collect()
}

/// Classify a verification failure into a rewrite category.
fn classify_failure(result: &VerificationResult) -> (&'static str, &'static str) {
    let kind_lower = result.kind.to_lowercase();
    if kind_lower.contains("overflow") {
        (
            "safe_arithmetic",
            "Replace raw arithmetic with checked variant",
        )
    } else if kind_lower.contains("div") && kind_lower.contains("zero") {
        (
            "non_zero_check",
            "Add divisor != 0 assertion before division",
        )
    } else if kind_lower.contains("bounds") || kind_lower.contains("oob") {
        (
            "bounds_check",
            "Add index < len assertion before array access",
        )
    } else {
        (
            "add_precondition",
            "Add precondition to constrain inputs",
        )
    }
}

/// Extract a function name from a raw compiler diagnostic line, if present.
fn extract_function_name(line: &str) -> String {
    // Look for patterns like "fn_name" or "mod::fn_name" in the line.
    // Fallback to "unknown" if we can't parse it.
    if let Some(idx) = line.find("tRust [") {
        let after = &line[idx..];
        if let Some(bracket_end) = after.find(']') {
            let kind = &after[7..bracket_end]; // after "tRust ["
            return kind.to_string();
        }
    }
    "unknown".to_string()
}

// ---------------------------------------------------------------------------
// Loop progress display
// ---------------------------------------------------------------------------

/// Print iteration progress to the terminal.
pub(crate) fn print_iteration_header(iteration: usize, max: usize) {
    eprintln!();
    eprintln!(
        "=== tRust Rewrite Loop: Iteration {}/{} ===",
        iteration + 1,
        max
    );
}

/// Print iteration summary after verification.
pub(crate) fn print_iteration_summary(
    frontier: &ProofFrontier,
    proposals: &[RewriteProposal],
    decision: &LoopDecision,
    elapsed: &std::time::Duration,
) {
    eprintln!();
    eprintln!(
        "  Frontier: {} proved, {} failed, {} unknown ({} total)",
        frontier.proved, frontier.failed, frontier.unknown, frontier.total()
    );

    if !proposals.is_empty() {
        eprintln!("  Proposals: {} rewrites suggested", proposals.len());
        for (i, p) in proposals.iter().enumerate().take(5) {
            eprintln!("    {}: [{}] {}", i + 1, p.kind, p.description);
        }
        if proposals.len() > 5 {
            eprintln!("    ... and {} more", proposals.len() - 5);
        }
    }

    let decision_str = match decision {
        LoopDecision::Continue { verdict } => format!("CONTINUE ({verdict})"),
        LoopDecision::Converged { stable_rounds } => {
            format!("CONVERGED (stable for {stable_rounds} rounds)")
        }
        LoopDecision::Regressed { reason } => format!("REGRESSED ({reason})"),
        LoopDecision::IterationLimitReached => "ITERATION LIMIT REACHED".to_string(),
    };
    eprintln!("  Decision: {decision_str}");
    eprintln!("  Elapsed: {}ms", elapsed.as_millis());
}

/// Print final loop summary.
pub(crate) fn print_loop_summary(
    tracker: &ConvergenceTracker,
    final_frontier: &ProofFrontier,
    total_elapsed: &std::time::Duration,
    final_decision: &LoopDecision,
) {
    eprintln!();
    eprintln!("=== tRust Rewrite Loop Summary ===");
    eprintln!("  Iterations: {}", tracker.iteration_count());
    eprintln!(
        "  Final frontier: {} proved, {} failed, {} unknown",
        final_frontier.proved, final_frontier.failed, final_frontier.unknown
    );

    let score = if final_frontier.total() > 0 {
        final_frontier.proved as f64 / final_frontier.total() as f64
    } else {
        0.0
    };
    eprintln!("  Convergence score: {:.1}%", score * 100.0);

    let outcome = match final_decision {
        LoopDecision::Converged { .. } => "CONVERGED",
        LoopDecision::IterationLimitReached => "ITERATION LIMIT",
        LoopDecision::Regressed { .. } => "REGRESSED",
        LoopDecision::Continue { .. } => "IN PROGRESS",
    };
    eprintln!("  Outcome: {outcome}");
    eprintln!("  Total time: {}ms", total_elapsed.as_millis());
    eprintln!("==================================");
}

// ---------------------------------------------------------------------------
// Backprop engine: applies trust-backprop rewrites to source files
// ---------------------------------------------------------------------------

/// Orchestrates applying rewrite proposals to source files via `trust-backprop`.
///
/// Respects governance controls:
/// - Protected functions cannot be rewritten (except spec-only when allowed)
/// - Test functions are immutable
/// - Per-function rewrite limit enforced across iterations
pub(crate) struct BackpropEngine {
    policy: GovernancePolicy,
    tracker: RewriteTracker,
    /// Default source file path to use when the verification result does not
    /// contain an extractable file path. Set from the CLI `--file` argument in
    /// single-file mode.
    default_source_file: Option<String>,
}

/// Result of applying a single backprop iteration.
#[derive(Debug)]
pub(crate) struct BackpropResult {
    /// Number of files modified.
    pub(crate) files_modified: usize,
    /// Number of rewrites applied.
    pub(crate) rewrites_applied: usize,
    /// Number of proposals skipped due to governance.
    pub(crate) governance_skips: usize,
    /// Number of proposals skipped due to rewrite limit.
    pub(crate) limit_skips: usize,
}

impl BackpropEngine {
    /// Create a new backprop engine with default governance policy.
    #[cfg(test)]
    pub(crate) fn new() -> Self {
        Self {
            policy: GovernancePolicy::default(),
            tracker: RewriteTracker::new(),
            default_source_file: None,
        }
    }

    /// Create a new backprop engine with protected functions.
    ///
    /// Functions in `skip_functions` will be treated as protected and will not
    /// be rewritten (except for spec-only changes if policy allows).
    pub(crate) fn with_protected(skip_functions: &[String]) -> Self {
        Self {
            policy: GovernancePolicy {
                protected_functions: skip_functions.to_vec(),
                ..GovernancePolicy::default()
            },
            tracker: RewriteTracker::new(),
            default_source_file: None,
        }
    }

    /// Set the default source file path used when verification results lack
    /// file path information. Typically the CLI `--file` target.
    pub(crate) fn set_default_source_file(&mut self, path: String) {
        self.default_source_file = Some(path);
    }

    /// Apply rewrite proposals to source files.
    ///
    /// Converts CLI-level `RewriteProposal`s into `trust_strengthen::Proposal`s,
    /// checks governance, generates a rewrite plan, and applies it to disk.
    ///
    /// Returns a summary of what was applied and what was skipped.
    pub(crate) fn apply(
        &mut self,
        proposals: &[RewriteProposal],
        verification_results: &[VerificationResult],
    ) -> BackpropResult {
        let mut governance_skips = 0usize;
        let mut limit_skips = 0usize;

        // Convert CLI proposals to trust-strengthen Proposals, filtering by
        // governance and rewrite-limit.
        let mut strengthen_proposals = Vec::new();
        for proposal in proposals {
            // Check per-function rewrite limit before conversion
            if self.tracker.exceeds_limit(
                &proposal.function,
                self.policy.max_rewrites_per_function,
            ) {
                limit_skips += 1;
                eprintln!(
                    "    Backprop: skipping `{}` (rewrite limit {} exceeded)",
                    proposal.function, self.policy.max_rewrites_per_function
                );
                continue;
            }

            let sp = to_strengthen_proposal(
                proposal,
                verification_results,
                self.default_source_file.as_deref(),
            );

            // Check governance
            let violations = self.policy.check(&sp);
            if !violations.is_empty() {
                governance_skips += 1;
                eprintln!(
                    "    Backprop: skipping `{}` (governance: {:?})",
                    proposal.function, violations
                );
                continue;
            }

            strengthen_proposals.push(sp);
        }

        if strengthen_proposals.is_empty() {
            return BackpropResult {
                files_modified: 0,
                rewrites_applied: 0,
                governance_skips,
                limit_skips,
            };
        }

        // Generate rewrite plan through trust-backprop (non-strict: skip violations)
        let plan = match apply_plan(&strengthen_proposals, &self.policy) {
            Ok(plan) => plan,
            Err(e) => {
                eprintln!("    Backprop: plan generation failed: {e}");
                return BackpropResult {
                    files_modified: 0,
                    rewrites_applied: 0,
                    governance_skips,
                    limit_skips,
                };
            }
        };

        if plan.is_empty() {
            return BackpropResult {
                files_modified: 0,
                rewrites_applied: 0,
                governance_skips,
                limit_skips,
            };
        }

        let rewrites_applied = plan.len();

        // Apply the plan to actual files on disk
        match apply_plan_to_files(&plan) {
            Ok(results) => {
                let files_modified = results.len();

                // Record applied rewrites in the tracker
                for rewrite in &plan.rewrites {
                    self.tracker.record(&rewrite.function_name);
                }

                for result in &results {
                    eprintln!(
                        "    Backprop: modified {} ({} rewrites)",
                        result.path, result.rewrite_count
                    );
                }

                BackpropResult {
                    files_modified,
                    rewrites_applied,
                    governance_skips,
                    limit_skips,
                }
            }
            Err(e) => {
                eprintln!("    Backprop: file rewrite failed: {e}");
                BackpropResult {
                    files_modified: 0,
                    rewrites_applied: 0,
                    governance_skips,
                    limit_skips,
                }
            }
        }
    }
}

/// Convert a CLI-level `RewriteProposal` into a `trust_strengthen::Proposal`.
///
/// Maps the proposal kind string to the appropriate `ProposalKind` variant,
/// using the raw verification result line to extract file path information.
/// Falls back to `default_source_file` when the verification result lacks an
/// extractable path.
fn to_strengthen_proposal(
    proposal: &RewriteProposal,
    verification_results: &[VerificationResult],
    default_source_file: Option<&str>,
) -> Proposal {
    // Try to extract file path from the matching verification result's raw line.
    // The raw_line may contain a path like "src/lib.rs:10:5".
    let file_path = verification_results
        .iter()
        .find(|r| r.outcome == VerificationOutcome::Failed && r.kind == proposal.function)
        .and_then(|r| extract_file_path(&r.raw_line))
        .or_else(|| default_source_file.map(String::from))
        .unwrap_or_else(|| proposal.function.clone());

    let kind = match proposal.kind.as_str() {
        "safe_arithmetic" => ProposalKind::SafeArithmetic {
            original: String::new(), // Resolved by trust-backprop locator from source
            replacement: String::new(),
        },
        "non_zero_check" => ProposalKind::AddNonZeroCheck {
            check_expr: "assert!(divisor != 0, \"divisor must be non-zero\")".into(),
        },
        "bounds_check" => ProposalKind::AddBoundsCheck {
            check_expr: "assert!(index < collection.len(), \"index out of bounds\")".into(),
        },
        _ => ProposalKind::AddPrecondition {
            spec_body: proposal.description.clone(),
        },
    };

    Proposal {
        function_path: file_path,
        function_name: proposal.function.clone(),
        kind,
        confidence: 0.8,
        rationale: proposal.description.clone(),
    }
}

/// Try to extract a file path from a raw compiler diagnostic line.
///
/// Looks for patterns like `/path/to/file.rs:10:5` or `src/file.rs:10`.
fn extract_file_path(line: &str) -> Option<String> {
    // Look for a .rs file reference with line number
    for segment in line.split_whitespace() {
        let cleaned = segment.trim_start_matches('(').trim_end_matches(')');
        if cleaned.ends_with(".rs") || cleaned.contains(".rs:") {
            // Strip line:col suffix
            let path = if let Some(idx) = cleaned.find(".rs:") {
                &cleaned[..idx + 3]
            } else {
                cleaned
            };
            return Some(path.to_string());
        }
    }
    None
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::VerificationOutcome;

    fn make_result(kind: &str, outcome: VerificationOutcome) -> VerificationResult {
        VerificationResult {
            kind: kind.into(),
            message: format!("{kind} test"),
            outcome,
            backend: "z4-smtlib".into(),
            time_ms: Some(5),
            raw_line: format!(
                "note: tRust [{kind}]: {kind} test -- {} (z4-smtlib, 5ms)",
                match outcome {
                    VerificationOutcome::Proved => "PROVED",
                    VerificationOutcome::Failed => "FAILED",
                    VerificationOutcome::Unknown => "UNKNOWN",
                }
            ),
        }
    }

    #[test]
    fn test_proof_frontier_from_results() {
        let results = vec![
            make_result("overflow:add", VerificationOutcome::Proved),
            make_result("div_by_zero", VerificationOutcome::Failed),
            make_result("bounds", VerificationOutcome::Unknown),
        ];
        let frontier = ProofFrontier::from_results(&results);
        assert_eq!(frontier.proved, 1);
        assert_eq!(frontier.failed, 1);
        assert_eq!(frontier.unknown, 1);
        assert_eq!(frontier.total(), 3);
    }

    #[test]
    fn test_convergence_first_iteration_continues() {
        let mut tracker = ConvergenceTracker::new(10);
        let decision = tracker.observe(ProofFrontier {
            proved: 1,
            failed: 2,
            unknown: 0,
        });
        assert!(matches!(decision, LoopDecision::Continue { .. }));
    }

    #[test]
    fn test_convergence_stable_converges() {
        let mut tracker = ConvergenceTracker::new(10);
        let frontier = ProofFrontier {
            proved: 3,
            failed: 0,
            unknown: 1,
        };
        tracker.observe(frontier.clone());
        let decision = tracker.observe(frontier);
        assert!(matches!(decision, LoopDecision::Converged { stable_rounds: 2 }));
    }

    #[test]
    fn test_convergence_regression_fewer_proofs() {
        let mut tracker = ConvergenceTracker::new(10);
        tracker.observe(ProofFrontier {
            proved: 5,
            failed: 0,
            unknown: 0,
        });
        let decision = tracker.observe(ProofFrontier {
            proved: 3,
            failed: 0,
            unknown: 2,
        });
        assert!(matches!(decision, LoopDecision::Regressed { .. }));
    }

    #[test]
    fn test_convergence_regression_more_failures() {
        let mut tracker = ConvergenceTracker::new(10);
        tracker.observe(ProofFrontier {
            proved: 3,
            failed: 1,
            unknown: 0,
        });
        let decision = tracker.observe(ProofFrontier {
            proved: 3,
            failed: 2,
            unknown: 0,
        });
        assert!(matches!(decision, LoopDecision::Regressed { .. }));
    }

    #[test]
    fn test_convergence_iteration_limit() {
        let mut tracker = ConvergenceTracker::new(2);
        tracker.observe(ProofFrontier {
            proved: 1,
            failed: 1,
            unknown: 0,
        });
        let decision = tracker.observe(ProofFrontier {
            proved: 2,
            failed: 0,
            unknown: 0,
        });
        assert!(matches!(decision, LoopDecision::IterationLimitReached));
    }

    #[test]
    fn test_propose_rewrites_overflow() {
        let results = vec![make_result("overflow:add", VerificationOutcome::Failed)];
        let proposals = propose_rewrites(&results);
        assert_eq!(proposals.len(), 1);
        assert_eq!(proposals[0].kind, "safe_arithmetic");
    }

    #[test]
    fn test_propose_rewrites_div_by_zero() {
        let results = vec![make_result("div_by_zero", VerificationOutcome::Failed)];
        let proposals = propose_rewrites(&results);
        assert_eq!(proposals.len(), 1);
        assert_eq!(proposals[0].kind, "non_zero_check");
    }

    #[test]
    fn test_propose_rewrites_bounds() {
        let results = vec![make_result("bounds", VerificationOutcome::Failed)];
        let proposals = propose_rewrites(&results);
        assert_eq!(proposals.len(), 1);
        assert_eq!(proposals[0].kind, "bounds_check");
    }

    #[test]
    fn test_propose_rewrites_skips_proved() {
        let results = vec![
            make_result("overflow:add", VerificationOutcome::Proved),
            make_result("div_by_zero", VerificationOutcome::Failed),
        ];
        let proposals = propose_rewrites(&results);
        assert_eq!(proposals.len(), 1);
        assert_eq!(proposals[0].kind, "non_zero_check");
    }

    #[test]
    fn test_classify_failure_unknown_kind() {
        let result = make_result("custom_check", VerificationOutcome::Failed);
        let proposals = propose_rewrites(&[result]);
        assert_eq!(proposals.len(), 1);
        assert_eq!(proposals[0].kind, "add_precondition");
    }

    #[test]
    fn test_extract_function_name_from_line() {
        let line = "note: tRust [overflow:add]: arithmetic overflow (Add) -- FAILED (z4, 8ms)";
        assert_eq!(extract_function_name(line), "overflow:add");
    }

    #[test]
    fn test_extract_function_name_fallback() {
        assert_eq!(extract_function_name("random text"), "unknown");
    }

    // -- Backprop engine tests --

    #[test]
    fn test_to_strengthen_proposal_overflow() {
        let proposal = RewriteProposal {
            function: "overflow:add".into(),
            kind: "safe_arithmetic".into(),
            description: "Replace raw arithmetic with checked variant".into(),
        };
        let results = vec![make_result("overflow:add", VerificationOutcome::Failed)];
        let sp = to_strengthen_proposal(&proposal, &results, None);
        assert!(matches!(sp.kind, ProposalKind::SafeArithmetic { .. }));
        assert_eq!(sp.function_name, "overflow:add");
    }

    #[test]
    fn test_to_strengthen_proposal_precondition_fallback() {
        let proposal = RewriteProposal {
            function: "custom_check".into(),
            kind: "add_precondition".into(),
            description: "Add precondition to constrain inputs".into(),
        };
        let sp = to_strengthen_proposal(&proposal, &[], None);
        assert!(matches!(sp.kind, ProposalKind::AddPrecondition { .. }));
    }

    #[test]
    fn test_to_strengthen_proposal_non_zero_check() {
        let proposal = RewriteProposal {
            function: "div_by_zero".into(),
            kind: "non_zero_check".into(),
            description: "Add divisor != 0 assertion".into(),
        };
        let sp = to_strengthen_proposal(&proposal, &[], None);
        assert!(matches!(sp.kind, ProposalKind::AddNonZeroCheck { .. }));
    }

    #[test]
    fn test_to_strengthen_proposal_bounds_check() {
        let proposal = RewriteProposal {
            function: "bounds".into(),
            kind: "bounds_check".into(),
            description: "Add bounds check".into(),
        };
        let sp = to_strengthen_proposal(&proposal, &[], None);
        assert!(matches!(sp.kind, ProposalKind::AddBoundsCheck { .. }));
    }

    #[test]
    fn test_extract_file_path_with_line() {
        let line = "  --> src/lib.rs:10:5";
        assert_eq!(extract_file_path(line), Some("src/lib.rs".into()));
    }

    #[test]
    fn test_extract_file_path_bare() {
        let line = "error in src/main.rs some context";
        assert_eq!(extract_file_path(line), Some("src/main.rs".into()));
    }

    #[test]
    fn test_extract_file_path_none() {
        assert_eq!(extract_file_path("no file reference here"), None);
    }

    #[test]
    fn test_backprop_engine_governance_blocks_test() {
        let mut engine = BackpropEngine::new();
        let proposal = RewriteProposal {
            function: "test_something".into(),
            kind: "safe_arithmetic".into(),
            description: "test".into(),
        };
        let result = engine.apply(&[proposal], &[]);
        // test_ prefix triggers governance TestFunction violation
        assert_eq!(result.governance_skips, 1);
        assert_eq!(result.rewrites_applied, 0);
    }

    #[test]
    fn test_backprop_engine_with_protected() {
        let mut engine = BackpropEngine::with_protected(&["critical_fn".into()]);
        let proposal = RewriteProposal {
            function: "critical_fn".into(),
            kind: "safe_arithmetic".into(),
            description: "test".into(),
        };
        let result = engine.apply(&[proposal], &[]);
        // Protected function blocks non-spec rewrites
        assert_eq!(result.governance_skips, 1);
        assert_eq!(result.rewrites_applied, 0);
    }

    #[test]
    fn test_backprop_engine_empty_proposals() {
        let mut engine = BackpropEngine::new();
        let result = engine.apply(&[], &[]);
        assert_eq!(result.files_modified, 0);
        assert_eq!(result.rewrites_applied, 0);
        assert_eq!(result.governance_skips, 0);
        assert_eq!(result.limit_skips, 0);
    }

    #[test]
    fn test_to_strengthen_proposal_uses_default_source_file() {
        let proposal = RewriteProposal {
            function: "overflow:add".into(),
            kind: "add_precondition".into(),
            description: "Add precondition".into(),
        };
        // Without default_source_file, falls back to function name
        let sp = to_strengthen_proposal(&proposal, &[], None);
        assert_eq!(sp.function_path, "overflow:add");

        // With default_source_file, uses the provided path
        let sp = to_strengthen_proposal(&proposal, &[], Some("/tmp/test.rs"));
        assert_eq!(sp.function_path, "/tmp/test.rs");
    }

    #[test]
    fn test_backprop_engine_applies_rewrite_to_file() {
        // Create a temp file with a function that has an overflow issue
        let dir = std::env::temp_dir().join("trust_rewrite_test");
        std::fs::create_dir_all(&dir).unwrap();
        let file = dir.join("test_rewrite.rs");
        let original_source = "fn add(a: u32, b: u32) -> u32 {\n    a + b\n}\n";
        std::fs::write(&file, original_source).unwrap();

        let file_path_str = file.display().to_string();

        let mut engine = BackpropEngine::new();
        engine.set_default_source_file(file_path_str.clone());

        let proposal = RewriteProposal {
            function: "add".into(),
            kind: "add_precondition".into(),
            description: "a + b does not overflow".into(),
        };

        let result = engine.apply(&[proposal], &[]);

        // Should have applied the rewrite
        assert!(
            result.rewrites_applied > 0,
            "expected rewrites to be applied, got rewrites_applied={}",
            result.rewrites_applied
        );
        assert!(
            result.files_modified > 0,
            "expected files to be modified, got files_modified={}",
            result.files_modified
        );

        // Verify the file was actually modified on disk
        let modified_source = std::fs::read_to_string(&file).unwrap();
        assert_ne!(
            modified_source, original_source,
            "source file should have been modified but was unchanged"
        );
        assert!(
            modified_source.contains("requires"),
            "modified source should contain a #[requires(...)] attribute, got: {modified_source}"
        );

        // Cleanup
        std::fs::remove_file(&file).ok();
        std::fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn test_backprop_engine_iterates_with_file_rewrites() {
        // Simulates multiple iterations of the rewrite loop
        let dir = std::env::temp_dir().join("trust_rewrite_iter_test");
        std::fs::create_dir_all(&dir).unwrap();
        let file = dir.join("test_iter.rs");
        let original = "fn compute(x: u32, y: u32) -> u32 {\n    x + y\n}\n";
        std::fs::write(&file, original).unwrap();

        let file_path_str = file.display().to_string();

        let mut engine = BackpropEngine::new();
        engine.set_default_source_file(file_path_str.clone());

        // First iteration: add a precondition
        let proposal1 = RewriteProposal {
            function: "compute".into(),
            kind: "add_precondition".into(),
            description: "x + y does not overflow".into(),
        };
        let r1 = engine.apply(&[proposal1], &[]);
        assert!(r1.rewrites_applied > 0, "first iteration should apply rewrites");

        let after_first = std::fs::read_to_string(&file).unwrap();
        assert!(after_first.contains("requires"), "should contain requires after first iteration");

        // Second iteration with a different proposal
        let proposal2 = RewriteProposal {
            function: "compute".into(),
            kind: "add_precondition".into(),
            description: "result is positive".into(),
        };
        let r2 = engine.apply(&[proposal2], &[]);
        assert!(r2.rewrites_applied > 0, "second iteration should apply rewrites");

        let after_second = std::fs::read_to_string(&file).unwrap();
        assert_ne!(after_first, after_second, "second iteration should further modify the file");

        // Cleanup
        std::fs::remove_file(&file).ok();
        std::fs::remove_dir_all(&dir).ok();
    }
}
