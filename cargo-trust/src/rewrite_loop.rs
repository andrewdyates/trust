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

use std::collections::BTreeMap;
use std::path::Path;

use serde::Serialize;
use trust_backprop::file_io::{FileRewriteResult, apply_plan_to_files};
use trust_backprop::{
    ApprovalPolicy, ApprovalQueue, ApprovalStatus, AuditAction, AuditEntryBuilder, AuditTrail,
    GovernancePolicy, PendingRewrite, ReverificationResult, RewriteEngine, RewritePlan,
    RewriteTracker, SourceRewrite, UnifiedDiff, apply_plan, classify_rewrite, default_rules,
    format_github, format_unified, generate_diff,
};
use trust_strengthen::{
    FailureAnalysis, FailurePattern, Proposal, ProposalKind, analyze_failure, read_function,
    strengthen, strengthen_with_context,
};
use trust_types::{
    Counterexample, SourceSpan, VerificationCondition, VerificationResult as TrustVr,
};

use crate::report::CompilerDiagnostic;
use crate::types::{VerificationOutcome, VerificationResult};

// ---------------------------------------------------------------------------
// Convergence tracking
// ---------------------------------------------------------------------------

/// Proof frontier snapshot for one iteration.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub(crate) struct ProofFrontier {
    pub(crate) proved: usize,
    pub(crate) failed: usize,
    pub(crate) unknown: usize,
}

impl ProofFrontier {
    pub(crate) fn from_results(results: &[VerificationResult]) -> Self {
        let proved = results.iter().filter(|r| r.outcome == VerificationOutcome::Proved).count();
        let failed = results.iter().filter(|r| r.outcome == VerificationOutcome::Failed).count();
        let unknown = results
            .iter()
            .filter(|r| r.outcome.is_inconclusive() || r.outcome.is_runtime_checked())
            .count();
        Self { proved, failed, unknown }
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
        Self { history: Vec::new(), max_iterations, stable_limit: 2 }
    }

    /// Record a new frontier and return the convergence decision.
    pub(crate) fn observe(&mut self, frontier: ProofFrontier) -> LoopDecision {
        self.history.push(frontier);
        let iteration = self.history.len();

        if iteration >= self.max_iterations {
            return LoopDecision::IterationLimitReached;
        }

        if iteration < 2 {
            return LoopDecision::Continue { verdict: "first iteration" };
        }

        let current = &self.history[iteration - 1];
        let previous = &self.history[iteration - 2];

        // Check for regression.
        if current.proved < previous.proved {
            return LoopDecision::Regressed { reason: "fewer proofs than previous iteration" };
        }
        if current.failed > previous.failed {
            return LoopDecision::Regressed { reason: "more failures than previous iteration" };
        }

        // Check for stability / convergence.
        let stable_rounds = self.trailing_stable_rounds();
        if stable_rounds >= self.stable_limit {
            return LoopDecision::Converged { stable_rounds };
        }

        if current == previous {
            LoopDecision::Continue { verdict: "stable (no change)" }
        } else {
            LoopDecision::Continue { verdict: "improved" }
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
    // Payload for the proposal kind: a spec body for attribute proposals or a
    // replacement/check expression for direct rewrites.
    pub(crate) description: String,
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct RepairArtifact {
    pub(crate) schema_version: &'static str,
    pub(crate) summary: RepairRunSummary,
    pub(crate) iterations: Vec<RepairIteration>,
    pub(crate) audit_trail: AuditTrail,
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct RepairRunSummary {
    pub(crate) iterations: usize,
    pub(crate) succeeded: bool,
    pub(crate) final_frontier: ProofFrontier,
    pub(crate) final_decision: String,
    pub(crate) total_duration_ms: u64,
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct RepairIteration {
    pub(crate) iteration: usize,
    pub(crate) command: Vec<String>,
    pub(crate) exit_code: i32,
    pub(crate) frontier: ProofFrontier,
    pub(crate) results: Vec<VerificationResult>,
    pub(crate) compiler_diagnostics: Vec<CompilerDiagnostic>,
    pub(crate) failures: Vec<RepairFailure>,
    pub(crate) proposals: Vec<RepairProposalRecord>,
    pub(crate) applied_rewrites: Vec<SourceRewrite>,
    pub(crate) pending_rewrites: Vec<PendingRewrite>,
    pub(crate) rewrite_records: Vec<RepairRewriteRecord>,
    pub(crate) governance_skips: usize,
    pub(crate) limit_skips: usize,
    pub(crate) duration_ms: u64,
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct RepairFailure {
    pub(crate) function_path: String,
    pub(crate) function_name: String,
    pub(crate) kind: String,
    pub(crate) pattern: String,
    pub(crate) description: String,
    pub(crate) location: Option<SourceSpan>,
    pub(crate) solver: String,
    pub(crate) time_ms: Option<u64>,
    pub(crate) counterexample: Option<Counterexample>,
    pub(crate) reason: Option<String>,
    pub(crate) source_context: Option<RepairSourceContext>,
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct RepairSourceContext {
    pub(crate) source_file: String,
    pub(crate) signature: String,
    pub(crate) params: Vec<(String, String)>,
    pub(crate) return_type: Option<String>,
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct RepairProposalRecord {
    pub(crate) source_file: String,
    pub(crate) function_name: String,
    pub(crate) kind: String,
    pub(crate) confidence: f64,
    pub(crate) rationale: String,
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct RepairRewriteRecord {
    pub(crate) status: String,
    pub(crate) policy: Option<String>,
    pub(crate) reviewer_notes: Option<String>,
    pub(crate) rewrite: SourceRewrite,
    pub(crate) diff: Option<UnifiedDiff>,
    pub(crate) preview_error: Option<String>,
}

#[derive(Debug, Clone)]
pub(crate) struct StrengthenIteration {
    pub(crate) proposals: Vec<Proposal>,
    pub(crate) failures: Vec<RepairFailure>,
}

impl StrengthenIteration {
    pub(crate) fn summaries(&self) -> Vec<RewriteProposal> {
        self.proposals.iter().map(summarize_proposal).collect()
    }

    pub(crate) fn proposal_records(&self) -> Vec<RepairProposalRecord> {
        self.proposals
            .iter()
            .map(|proposal| RepairProposalRecord {
                source_file: proposal.function_path.clone(),
                function_name: proposal.function_name.clone(),
                kind: proposal_kind_tag(&proposal.kind).to_string(),
                confidence: proposal.confidence,
                rationale: proposal.rationale.clone(),
            })
            .collect()
    }
}

pub(crate) fn strengthen_failures(
    failures: &[VerificationResult],
    default_source_file: Option<&str>,
) -> StrengthenIteration {
    let mut by_function: BTreeMap<String, Vec<&VerificationResult>> = BTreeMap::new();
    for failure in failures.iter().filter(|r| r.outcome == VerificationOutcome::Failed) {
        let key = if failure.function.is_empty() {
            extract_function_name(&failure.raw_line)
        } else {
            failure.function.clone()
        };
        by_function.entry(key).or_default().push(failure);
    }

    let mut proposals = Vec::new();
    let mut repair_failures = Vec::new();

    for (function_path, function_failures) in by_function {
        let function_name = function_path.rsplit("::").next().unwrap_or(&function_path).to_string();
        let source_backed_failures: Vec<&VerificationResult> = function_failures
            .iter()
            .copied()
            .filter(|failure| !has_binary_only_location(failure))
            .collect();
        let source_file = source_backed_failures
            .iter()
            .find_map(|failure| {
                failure
                    .location
                    .as_ref()
                    .map(|span| span.file.as_str())
                    .and_then(source_backed_path)
            })
            .map(str::to_string)
            .or_else(|| {
                if source_backed_failures.is_empty() {
                    None
                } else {
                    default_source_file.and_then(source_backed_path).map(str::to_string)
                }
            });
        let source_ctx =
            source_file.as_deref().and_then(|file| read_function(file, &function_name));

        let analyses: Vec<FailureAnalysis> = source_backed_failures
            .iter()
            .map(|failure| {
                let (vc, result) = to_trust_pair(failure);
                analyze_failure(&vc, &result)
            })
            .collect();

        if !analyses.is_empty() {
            if let Some(ctx) = source_ctx.as_ref() {
                let source_path = source_file.as_deref().unwrap_or(&function_path);
                proposals.extend(strengthen_with_context(
                    source_path,
                    &function_name,
                    &analyses,
                    ctx,
                ));
            } else {
                let source_path = source_file.as_deref().unwrap_or(&function_path);
                proposals.extend(strengthen(source_path, &function_name, &analyses));
            }
        }

        repair_failures.extend(function_failures.into_iter().map(|failure| {
            let source_context = if has_binary_only_location(failure) {
                None
            } else {
                source_ctx.as_ref().map(|ctx| RepairSourceContext {
                    source_file: source_file.clone().unwrap_or_default(),
                    signature: ctx.signature.clone(),
                    params: ctx.params.clone(),
                    return_type: ctx.return_type.clone(),
                })
            };

            RepairFailure {
                function_path: function_path.clone(),
                function_name: function_name.clone(),
                kind: failure.kind.clone(),
                pattern: failure_pattern_label(&to_failure_analysis(failure).pattern).to_string(),
                description: failure.message.clone(),
                location: failure.location.clone(),
                solver: failure.backend.clone(),
                time_ms: failure.time_ms,
                counterexample: failure.counterexample.clone(),
                reason: failure.reason.clone(),
                source_context,
            }
        }));
    }

    StrengthenIteration { proposals, failures: repair_failures }
}

fn source_backed_path(path: &str) -> Option<&str> {
    (!path.is_empty() && !is_binary_only_path(path)).then_some(path)
}

fn has_binary_only_location(result: &VerificationResult) -> bool {
    result.location.as_ref().is_some_and(|span| is_binary_only_path(&span.file))
}

fn is_binary_only_path(path: &str) -> bool {
    path.starts_with("binary:")
}

pub(crate) fn write_repair_artifact(
    output_dir: &Path,
    artifact: &RepairArtifact,
) -> std::io::Result<()> {
    std::fs::create_dir_all(output_dir)?;
    let json = serde_json::to_string_pretty(artifact)
        .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))?;
    std::fs::write(output_dir.join("repair.json"), json)
}

pub(crate) fn write_repair_markdown(
    output_dir: &Path,
    artifact: &RepairArtifact,
) -> std::io::Result<()> {
    std::fs::create_dir_all(output_dir)?;
    std::fs::write(output_dir.join("repair.md"), render_repair_markdown(artifact))
}

pub(crate) fn build_rewrite_records(
    applied_rewrites: &[SourceRewrite],
    pending_rewrites: &[PendingRewrite],
    file_results: &[FileRewriteResult],
) -> Vec<RepairRewriteRecord> {
    let engine = RewriteEngine::new();
    let mut current_sources: BTreeMap<String, String> =
        file_results.iter().map(|result| (result.path.clone(), result.original.clone())).collect();
    let mut records = Vec::new();

    for rewrite in applied_rewrites {
        let current_source = current_sources
            .entry(rewrite.file_path.clone())
            .or_insert_with(|| std::fs::read_to_string(&rewrite.file_path).unwrap_or_default());

        match engine.apply_rewrite(current_source, rewrite) {
            Ok(updated_source) => {
                let diff = generate_diff(current_source, &updated_source, &rewrite.file_path);
                *current_source = updated_source;
                records.push(RepairRewriteRecord {
                    status: "applied".to_string(),
                    policy: Some("auto".to_string()),
                    reviewer_notes: None,
                    rewrite: rewrite.clone(),
                    diff: Some(diff),
                    preview_error: None,
                });
            }
            Err(err) => records.push(RepairRewriteRecord {
                status: "applied".to_string(),
                policy: Some("auto".to_string()),
                reviewer_notes: None,
                rewrite: rewrite.clone(),
                diff: None,
                preview_error: Some(err.to_string()),
            }),
        }
    }

    for pending in pending_rewrites {
        match std::fs::read_to_string(&pending.rewrite.file_path) {
            Ok(source) => match engine.apply_rewrite(&source, &pending.rewrite) {
                Ok(updated_source) => records.push(RepairRewriteRecord {
                    status: pending_status_label(pending.policy).to_string(),
                    policy: Some(approval_policy_label(pending.policy).to_string()),
                    reviewer_notes: pending.reviewer_notes.clone(),
                    rewrite: pending.rewrite.clone(),
                    diff: Some(generate_diff(&source, &updated_source, &pending.rewrite.file_path)),
                    preview_error: None,
                }),
                Err(err) => records.push(RepairRewriteRecord {
                    status: pending_status_label(pending.policy).to_string(),
                    policy: Some(approval_policy_label(pending.policy).to_string()),
                    reviewer_notes: pending.reviewer_notes.clone(),
                    rewrite: pending.rewrite.clone(),
                    diff: None,
                    preview_error: Some(err.to_string()),
                }),
            },
            Err(err) => records.push(RepairRewriteRecord {
                status: pending_status_label(pending.policy).to_string(),
                policy: Some(approval_policy_label(pending.policy).to_string()),
                reviewer_notes: pending.reviewer_notes.clone(),
                rewrite: pending.rewrite.clone(),
                diff: None,
                preview_error: Some(err.to_string()),
            }),
        }
    }

    records
}

pub(crate) fn append_audit_entries(
    trail: &mut AuditTrail,
    iteration: usize,
    rewrite_records: &[RepairRewriteRecord],
) {
    for record in rewrite_records.iter().filter(|record| record.status == "applied") {
        let (old_spec, new_spec, rollback_safe) = rewrite_spec_delta(&record.rewrite);
        let mut entry = AuditEntryBuilder::new(
            AuditAction::RewriteApplied,
            record.rewrite.file_path.clone(),
            record.rewrite.function_name.clone(),
        )
        .iteration(iteration as u32)
        .approval_status(ApprovalStatus::Auto)
        .reverification_result(ReverificationResult::NotRun)
        .rollback_safe(rollback_safe);

        if let Some(old_spec) = old_spec {
            entry = entry.old_spec(old_spec);
        }
        if let Some(new_spec) = new_spec {
            entry = entry.new_spec(new_spec);
        }
        if let Some(diff) = &record.diff {
            entry = entry.before_after_diff(format_unified(diff));
        }

        trail.append(entry);
    }
}

fn render_repair_markdown(artifact: &RepairArtifact) -> String {
    let mut out = String::new();
    out.push_str("# tRust Repair Report\n\n");
    out.push_str(&format!(
        "- Iterations: {}\n- Final frontier: {} proved, {} failed, {} unknown\n- Outcome: {}\n- Total duration: {}ms\n- Audit entries: {}\n\n",
        artifact.summary.iterations,
        artifact.summary.final_frontier.proved,
        artifact.summary.final_frontier.failed,
        artifact.summary.final_frontier.unknown,
        artifact.summary.final_decision,
        artifact.summary.total_duration_ms,
        artifact.audit_trail.entries().len(),
    ));

    for iteration in &artifact.iterations {
        out.push_str(&format!("## Iteration {}\n\n", iteration.iteration));
        out.push_str(&format!(
            "- Command: `{}`\n- Exit code: `{}`\n- Frontier: {} proved, {} failed, {} unknown\n- Diagnostics: {}\n\n",
            iteration.command.join(" "),
            iteration.exit_code,
            iteration.frontier.proved,
            iteration.frontier.failed,
            iteration.frontier.unknown,
            iteration.compiler_diagnostics.len(),
        ));

        if !iteration.failures.is_empty() {
            out.push_str("### Failures\n\n");
            for failure in &iteration.failures {
                out.push_str(&format!(
                    "- `{}` `{}` at `{}`: {}",
                    failure.function_path,
                    failure.kind,
                    failure
                        .location
                        .as_ref()
                        .map(|span| {
                            format!("{}:{}:{}", span.file, span.line_start, span.col_start)
                        })
                        .unwrap_or_else(|| "unknown".to_string()),
                    failure.description,
                ));
                if let Some(counterexample) = &failure.counterexample {
                    out.push_str(&format!(" | counterexample: `{:?}`", counterexample));
                }
                if let Some(reason) = &failure.reason {
                    out.push_str(&format!(" | reason: `{reason}`"));
                }
                out.push('\n');
            }
            out.push('\n');
        }

        if !iteration.proposals.is_empty() {
            out.push_str("### Proposals\n\n");
            for proposal in &iteration.proposals {
                out.push_str(&format!(
                    "- `{}` `{}` ({:.2}): {}\n",
                    proposal.function_name, proposal.kind, proposal.confidence, proposal.rationale,
                ));
            }
            out.push('\n');
        }

        if !iteration.rewrite_records.is_empty() {
            out.push_str("### Rewrite Details\n\n");
            for record in &iteration.rewrite_records {
                out.push_str(&format!(
                    "- `{}` `{}` [{}] {}\n",
                    record.rewrite.function_name,
                    record.rewrite.file_path,
                    record.status,
                    record.rewrite.rationale,
                ));
                if let Some(policy) = &record.policy {
                    out.push_str(&format!("  Policy: `{policy}`\n"));
                }
                if let Some(error) = &record.preview_error {
                    out.push_str(&format!("  Preview error: `{error}`\n"));
                }
                if let Some(diff) = &record.diff {
                    out.push_str(&format!("{}\n", format_github(diff)));
                }
            }
        }
    }

    out
}

fn approval_policy_label(policy: ApprovalPolicy) -> &'static str {
    match policy {
        ApprovalPolicy::Auto => "auto",
        ApprovalPolicy::Review => "review",
        ApprovalPolicy::Block => "block",
        _ => "other",
    }
}

fn pending_status_label(policy: ApprovalPolicy) -> &'static str {
    match policy {
        ApprovalPolicy::Auto => "pending_auto",
        ApprovalPolicy::Review => "pending_review",
        ApprovalPolicy::Block => "blocked",
        _ => "pending_other",
    }
}

pub(crate) fn decision_label(decision: &LoopDecision) -> String {
    match decision {
        LoopDecision::Continue { verdict } => format!("continue:{verdict}"),
        LoopDecision::Converged { stable_rounds } => format!("converged:{stable_rounds}"),
        LoopDecision::Regressed { reason } => format!("regressed:{reason}"),
        LoopDecision::IterationLimitReached => "iteration_limit".to_string(),
    }
}

fn rewrite_spec_delta(rewrite: &SourceRewrite) -> (Option<String>, Option<String>, bool) {
    match &rewrite.kind {
        trust_backprop::RewriteKind::InsertAttribute { attribute } => {
            (None, Some(attribute.clone()), true)
        }
        trust_backprop::RewriteKind::ReplaceExpression { old_text, new_text } => {
            (Some(old_text.clone()), Some(new_text.clone()), false)
        }
        trust_backprop::RewriteKind::InsertAssertion { assertion } => {
            (None, Some(assertion.clone()), true)
        }
        _ => (None, None, false),
    }
}

#[cfg(test)]
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

#[cfg(test)]
/// Classify a verification failure into a rewrite category.
fn classify_failure(result: &VerificationResult) -> (&'static str, &'static str) {
    let kind_lower = result.kind.to_lowercase();
    if kind_lower.contains("overflow") {
        ("safe_arithmetic", "Replace raw arithmetic with checked variant")
    } else if kind_lower.contains("div") && kind_lower.contains("zero") {
        ("non_zero_check", "Add divisor != 0 assertion before division")
    } else if kind_lower.contains("bounds") || kind_lower.contains("oob") {
        ("bounds_check", "Add index < len assertion before array access")
    } else {
        ("add_precondition", "Add precondition to constrain inputs")
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

fn to_failure_analysis(result: &VerificationResult) -> FailureAnalysis {
    let (vc, vr) = to_trust_pair(result);
    analyze_failure(&vc, &vr)
}

fn to_trust_pair(result: &VerificationResult) -> (VerificationCondition, TrustVr) {
    let vc = VerificationCondition {
        kind: crate::report::parse_vc_kind(&result.kind),
        function: if result.function.is_empty() {
            result.kind.clone().into()
        } else {
            result.function.clone().into()
        },
        location: result.location.clone().unwrap_or_else(SourceSpan::default),
        formula: trust_types::Formula::Bool(true),
        contract_metadata: None,
    };
    let vr = match result.outcome {
        VerificationOutcome::Proved => TrustVr::Proved {
            solver: result.backend.clone().into(),
            time_ms: result.time_ms.unwrap_or(0),
            strength: trust_types::ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: None,
        },
        VerificationOutcome::Failed => TrustVr::Failed {
            solver: result.backend.clone().into(),
            time_ms: result.time_ms.unwrap_or(0),
            counterexample: result.counterexample.clone(),
        },
        VerificationOutcome::Unknown => TrustVr::Unknown {
            solver: result.backend.clone().into(),
            time_ms: result.time_ms.unwrap_or(0),
            reason: result.reason.clone().unwrap_or_else(|| "unknown".to_string()),
        },
        VerificationOutcome::RuntimeChecked => TrustVr::Unknown {
            solver: result.backend.clone().into(),
            time_ms: result.time_ms.unwrap_or(0),
            reason: result
                .reason
                .clone()
                .unwrap_or_else(|| "unproved obligation with runtime check".to_string()),
        },
        VerificationOutcome::Timeout => TrustVr::Timeout {
            solver: result.backend.clone().into(),
            timeout_ms: result.time_ms.unwrap_or(0),
        },
    };
    (vc, vr)
}

fn proposal_kind_tag(kind: &ProposalKind) -> &'static str {
    match kind {
        ProposalKind::AddPrecondition { .. } => "precondition",
        ProposalKind::AddPostcondition { .. } => "postcondition",
        ProposalKind::AddInvariant { .. } => "invariant",
        ProposalKind::SafeArithmetic { .. } => "safe_arithmetic",
        ProposalKind::AddBoundsCheck { .. } => "bounds_check",
        ProposalKind::AddNonZeroCheck { .. } => "non_zero_check",
    }
}

fn summarize_proposal(proposal: &Proposal) -> RewriteProposal {
    let description = match &proposal.kind {
        ProposalKind::AddPrecondition { spec_body }
        | ProposalKind::AddPostcondition { spec_body }
        | ProposalKind::AddInvariant { spec_body } => spec_body.clone(),
        ProposalKind::SafeArithmetic { replacement, .. } => replacement.clone(),
        ProposalKind::AddBoundsCheck { check_expr }
        | ProposalKind::AddNonZeroCheck { check_expr } => check_expr.clone(),
    };
    RewriteProposal {
        function: proposal.function_name.clone(),
        kind: proposal_kind_tag(&proposal.kind).to_string(),
        description,
    }
}

fn failure_pattern_label(pattern: &FailurePattern) -> &'static str {
    match pattern {
        FailurePattern::ArithmeticOverflow { .. } => "arithmetic_overflow",
        FailurePattern::DivisionByZero => "division_by_zero",
        FailurePattern::IndexOutOfBounds => "index_out_of_bounds",
        FailurePattern::CastOverflow => "cast_overflow",
        FailurePattern::NegationOverflow => "negation_overflow",
        FailurePattern::ShiftOverflow => "shift_overflow",
        FailurePattern::AssertionFailure { .. } => "assertion_failure",
        FailurePattern::PreconditionViolation { .. } => "precondition_violation",
        FailurePattern::PostconditionViolation => "postcondition_violation",
        FailurePattern::UnreachableReached => "unreachable",
        FailurePattern::Temporal => "temporal",
        FailurePattern::Unknown => "unknown",
    }
}

// ---------------------------------------------------------------------------
// Loop progress display
// ---------------------------------------------------------------------------

/// Print iteration progress to the terminal.
pub(crate) fn print_iteration_header(iteration: usize, max: usize) {
    eprintln!();
    eprintln!("=== tRust Rewrite Loop: Iteration {}/{} ===", iteration + 1, max);
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
        frontier.proved,
        frontier.failed,
        frontier.unknown,
        frontier.total()
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
    /// Rewrites that were applied automatically.
    pub(crate) applied_rewrites: Vec<SourceRewrite>,
    /// Rewrites that require review or were blocked.
    pub(crate) pending_rewrites: Vec<PendingRewrite>,
    /// File-level before/after snapshots for applied rewrites.
    pub(crate) file_results: Vec<FileRewriteResult>,
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

    pub(crate) fn default_source_file(&self) -> Option<&str> {
        self.default_source_file.as_deref()
    }

    /// Apply rewrite proposals to source files.
    ///
    /// Converts CLI-level `RewriteProposal`s into `trust_strengthen::Proposal`s,
    /// checks governance, generates a rewrite plan, and applies it to disk.
    ///
    /// Returns a summary of what was applied and what was skipped.
    #[cfg(test)]
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
            if proposal_has_binary_only_span(proposal, verification_results) {
                governance_skips += 1;
                eprintln!(
                    "    Backprop: skipping `{}` (binary-only span has no source file)",
                    proposal.function
                );
                continue;
            }

            // Check per-function rewrite limit before conversion
            if self.tracker.exceeds_limit(&proposal.function, self.policy.max_rewrites_per_function)
            {
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

        self.apply_strengthen_proposals(&strengthen_proposals, governance_skips, limit_skips)
    }

    pub(crate) fn apply_strengthen_proposals(
        &mut self,
        proposals: &[Proposal],
        mut governance_skips: usize,
        mut limit_skips: usize,
    ) -> BackpropResult {
        if proposals.is_empty() {
            return BackpropResult {
                files_modified: 0,
                rewrites_applied: 0,
                governance_skips,
                limit_skips,
                applied_rewrites: Vec::new(),
                pending_rewrites: Vec::new(),
                file_results: Vec::new(),
            };
        }

        let mut filtered_proposals = Vec::new();
        for proposal in proposals {
            if is_binary_only_path(&proposal.function_path) {
                governance_skips += 1;
                eprintln!(
                    "    Backprop: skipping `{}` (binary-only span has no source file)",
                    proposal.function_name
                );
                continue;
            }

            if self
                .tracker
                .exceeds_limit(&proposal.function_name, self.policy.max_rewrites_per_function)
            {
                limit_skips += 1;
                eprintln!(
                    "    Backprop: skipping `{}` (rewrite limit {} exceeded)",
                    proposal.function_name, self.policy.max_rewrites_per_function
                );
                continue;
            }

            let violations = self.policy.check(proposal);
            if !violations.is_empty() {
                governance_skips += 1;
                eprintln!(
                    "    Backprop: skipping `{}` (governance: {:?})",
                    proposal.function_name, violations
                );
                continue;
            }

            filtered_proposals.push(proposal.clone());
        }

        if filtered_proposals.is_empty() {
            return BackpropResult {
                files_modified: 0,
                rewrites_applied: 0,
                governance_skips,
                limit_skips,
                applied_rewrites: Vec::new(),
                pending_rewrites: Vec::new(),
                file_results: Vec::new(),
            };
        }

        // Generate rewrite plan through trust-backprop (non-strict: skip violations)
        let plan = match apply_plan(&filtered_proposals, &self.policy) {
            Ok(plan) => plan,
            Err(e) => {
                eprintln!("    Backprop: plan generation failed: {e}");
                return BackpropResult {
                    files_modified: 0,
                    rewrites_applied: 0,
                    governance_skips,
                    limit_skips,
                    applied_rewrites: Vec::new(),
                    pending_rewrites: Vec::new(),
                    file_results: Vec::new(),
                };
            }
        };

        if plan.is_empty() {
            return BackpropResult {
                files_modified: 0,
                rewrites_applied: 0,
                governance_skips,
                limit_skips,
                applied_rewrites: Vec::new(),
                pending_rewrites: Vec::new(),
                file_results: Vec::new(),
            };
        }

        let mut auto_plan = RewritePlan::new(plan.summary.clone());
        let mut queue = ApprovalQueue::new();
        let rules = default_rules();

        for rewrite in plan.rewrites {
            match classify_rewrite(&rewrite, &rules) {
                ApprovalPolicy::Auto => auto_plan.rewrites.push(rewrite),
                policy => queue.enqueue(rewrite, policy),
            }
        }

        auto_plan.sort_for_application();
        let applied_rewrites = auto_plan.rewrites.clone();
        let pending_rewrites = queue.drain_all();
        let rewrites_applied = applied_rewrites.len();

        if auto_plan.is_empty() {
            return BackpropResult {
                files_modified: 0,
                rewrites_applied: 0,
                governance_skips,
                limit_skips,
                applied_rewrites,
                pending_rewrites,
                file_results: Vec::new(),
            };
        }

        // Apply the plan to actual files on disk
        match apply_plan_to_files(&auto_plan) {
            Ok(results) => {
                let files_modified = results.len();

                // Record applied rewrites in the tracker
                for rewrite in &applied_rewrites {
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
                    applied_rewrites,
                    pending_rewrites,
                    file_results: results,
                }
            }
            Err(e) => {
                eprintln!("    Backprop: file rewrite failed: {e}");
                BackpropResult {
                    files_modified: 0,
                    rewrites_applied: 0,
                    governance_skips,
                    limit_skips,
                    applied_rewrites: Vec::new(),
                    pending_rewrites,
                    file_results: Vec::new(),
                }
            }
        }
    }
}

#[cfg(test)]
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
        .and_then(|r| {
            r.location
                .as_ref()
                .map(|span| span.file.as_str())
                .and_then(source_backed_path)
                .map(str::to_string)
                .or_else(|| extract_file_path(&r.raw_line))
        })
        .or_else(|| default_source_file.and_then(source_backed_path).map(String::from))
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
        _ => ProposalKind::AddPrecondition { spec_body: proposal.description.clone() },
    };

    Proposal {
        function_path: file_path,
        function_name: proposal.function.clone(),
        kind,
        confidence: 0.8,
        rationale: proposal.description.clone(),
    }
}

#[cfg(test)]
fn proposal_has_binary_only_span(
    proposal: &RewriteProposal,
    verification_results: &[VerificationResult],
) -> bool {
    verification_results.iter().any(|r| {
        r.outcome == VerificationOutcome::Failed
            && r.kind == proposal.function
            && has_binary_only_location(r)
    })
}

#[cfg(test)]
/// Try to extract a file path from a raw compiler diagnostic line.
///
/// Looks for patterns like `/path/to/file.rs:10:5` or `src/file.rs:10`.
fn extract_file_path(line: &str) -> Option<String> {
    // Look for a .rs file reference with line number
    for segment in line.split_whitespace() {
        let cleaned = segment.trim_start_matches('(').trim_end_matches(')');
        if cleaned.ends_with(".rs") || cleaned.contains(".rs:") {
            // Strip line:col suffix
            let path =
                if let Some(idx) = cleaned.find(".rs:") { &cleaned[..idx + 3] } else { cleaned };
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
            function: "crate::test_fn".into(),
            kind: kind.into(),
            message: format!("{kind} test"),
            outcome,
            backend: "z4-smtlib".into(),
            time_ms: Some(5),
            location: None,
            counterexample: None,
            reason: None,
            raw_line: format!(
                "note: tRust [{kind}]: {kind} test -- {} (z4-smtlib, 5ms)",
                outcome.label()
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
        let decision = tracker.observe(ProofFrontier { proved: 1, failed: 2, unknown: 0 });
        assert!(matches!(decision, LoopDecision::Continue { .. }));
    }

    #[test]
    fn test_convergence_stable_converges() {
        let mut tracker = ConvergenceTracker::new(10);
        let frontier = ProofFrontier { proved: 3, failed: 0, unknown: 1 };
        tracker.observe(frontier.clone());
        let decision = tracker.observe(frontier);
        assert!(matches!(decision, LoopDecision::Converged { stable_rounds: 2 }));
    }

    #[test]
    fn test_convergence_regression_fewer_proofs() {
        let mut tracker = ConvergenceTracker::new(10);
        tracker.observe(ProofFrontier { proved: 5, failed: 0, unknown: 0 });
        let decision = tracker.observe(ProofFrontier { proved: 3, failed: 0, unknown: 2 });
        assert!(matches!(decision, LoopDecision::Regressed { .. }));
    }

    #[test]
    fn test_convergence_regression_more_failures() {
        let mut tracker = ConvergenceTracker::new(10);
        tracker.observe(ProofFrontier { proved: 3, failed: 1, unknown: 0 });
        let decision = tracker.observe(ProofFrontier { proved: 3, failed: 2, unknown: 0 });
        assert!(matches!(decision, LoopDecision::Regressed { .. }));
    }

    #[test]
    fn test_convergence_iteration_limit() {
        let mut tracker = ConvergenceTracker::new(2);
        tracker.observe(ProofFrontier { proved: 1, failed: 1, unknown: 0 });
        let decision = tracker.observe(ProofFrontier { proved: 2, failed: 0, unknown: 0 });
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
            description: "a <= u32::MAX - b".into(),
        };

        let result = engine.apply(&[proposal], &[]);

        assert_eq!(result.pending_rewrites.len(), 0);
        assert_eq!(result.rewrites_applied, 1);
        assert_eq!(result.files_modified, 1);

        // Internal spec-strengthening rewrites apply immediately by default.
        let modified_source = std::fs::read_to_string(&file).unwrap();
        assert_ne!(modified_source, original_source);
        assert!(modified_source.contains("#[requires(\"a <= u32::MAX - b\")]"));

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
            description: "x <= u32::MAX - y".into(),
        };
        let r1 = engine.apply(&[proposal1], &[]);
        assert_eq!(r1.rewrites_applied, 1, "internal precondition rewrites should auto-apply");
        assert_eq!(r1.files_modified, 1);
        assert!(r1.pending_rewrites.is_empty(), "first iteration should not queue rewrites");

        let after_first = std::fs::read_to_string(&file).unwrap();
        assert_ne!(after_first, original, "first rewrite should update the source");
        assert!(after_first.contains("#[requires(\"x <= u32::MAX - y\")]"));

        // Second iteration with a different proposal
        let proposal2 = RewriteProposal {
            function: "compute".into(),
            kind: "add_precondition".into(),
            description: "x > 0".into(),
        };
        let r2 = engine.apply(&[proposal2], &[]);
        assert_eq!(r2.rewrites_applied, 1, "second iteration should also auto-apply");
        assert_eq!(r2.files_modified, 1);
        assert!(r2.pending_rewrites.is_empty(), "second iteration should not queue rewrites");

        let after_second = std::fs::read_to_string(&file).unwrap();
        assert_ne!(after_first, after_second, "second rewrite should also update the source");
        assert!(after_second.contains("#[requires(\"x > 0\")]"));

        // Cleanup
        std::fs::remove_file(&file).ok();
        std::fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn test_strengthen_failures_uses_source_context() {
        let dir = std::env::temp_dir().join("trust_strengthen_ctx_test");
        std::fs::create_dir_all(&dir).unwrap();
        let file = dir.join("divide.rs");
        std::fs::write(&file, "fn divide(x: u32, y: u32) -> u32 {\n    x / y\n}\n").unwrap();

        let file_path = file.display().to_string();
        let result = VerificationResult {
            function: "crate::divide".into(),
            kind: "div_by_zero".into(),
            message: "division by zero".into(),
            outcome: VerificationOutcome::Failed,
            backend: "z4-smtlib".into(),
            time_ms: Some(3),
            location: Some(SourceSpan {
                file: file_path.clone(),
                line_start: 1,
                col_start: 1,
                line_end: 1,
                col_end: 10,
            }),
            counterexample: None,
            reason: None,
            raw_line: String::new(),
        };

        let strengthen = strengthen_failures(&[result], None);
        assert!(strengthen.proposals.iter().any(|proposal| {
            matches!(
                &proposal.kind,
                ProposalKind::AddPrecondition { spec_body } if spec_body == "y != 0"
            )
        }));
        assert!(
            strengthen
                .proposals
                .iter()
                .any(|proposal| { matches!(&proposal.kind, ProposalKind::AddNonZeroCheck { .. }) })
        );

        std::fs::remove_file(&file).ok();
        std::fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn test_strengthen_failures_skips_binary_only_span() {
        let result = VerificationResult {
            function: "binary::add".into(),
            kind: "overflow:add".into(),
            message: "overflow".into(),
            outcome: VerificationOutcome::Failed,
            backend: "z4-smtlib".into(),
            time_ms: Some(3),
            location: Some(SourceSpan {
                file: "binary:0x1000".into(),
                line_start: 0,
                col_start: 0,
                line_end: 0,
                col_end: 0,
            }),
            counterexample: None,
            reason: None,
            raw_line: String::new(),
        };

        let strengthen = strengthen_failures(&[result], Some("/tmp/source.rs"));

        assert!(strengthen.proposals.is_empty());
        assert_eq!(strengthen.failures.len(), 1);
        assert!(strengthen.failures[0].source_context.is_none());
    }

    #[test]
    fn test_backprop_engine_apply_skips_binary_span_even_with_default_source_file() {
        let dir = std::env::temp_dir().join("trust_rewrite_binary_gate_test");
        std::fs::create_dir_all(&dir).unwrap();
        let file = dir.join("source.rs");
        let original = "fn add(a: u32, b: u32) -> u32 {\n    a + b\n}\n";
        std::fs::write(&file, original).unwrap();

        let proposal = RewriteProposal {
            function: "overflow:add".into(),
            kind: "add_precondition".into(),
            description: "a <= u32::MAX - b".into(),
        };
        let verification_result = VerificationResult {
            function: "binary::add".into(),
            kind: "overflow:add".into(),
            message: "overflow".into(),
            outcome: VerificationOutcome::Failed,
            backend: "z4-smtlib".into(),
            time_ms: Some(3),
            location: Some(SourceSpan {
                file: "binary:0x1000".into(),
                line_start: 0,
                col_start: 0,
                line_end: 0,
                col_end: 0,
            }),
            counterexample: None,
            reason: None,
            raw_line: String::new(),
        };

        let mut engine = BackpropEngine::new();
        engine.set_default_source_file(file.display().to_string());
        let result = engine.apply(&[proposal], &[verification_result]);

        assert_eq!(result.governance_skips, 1);
        assert_eq!(result.rewrites_applied, 0);
        assert_eq!(result.files_modified, 0);
        assert_eq!(std::fs::read_to_string(&file).unwrap(), original);

        std::fs::remove_file(&file).ok();
        std::fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn test_backprop_engine_skips_binary_proposal_path() {
        let proposal = Proposal {
            function_path: "binary:0x1000".into(),
            function_name: "add".into(),
            kind: ProposalKind::AddPrecondition { spec_body: "a <= u32::MAX - b".into() },
            confidence: 0.8,
            rationale: "prevent overflow".into(),
        };

        let mut engine = BackpropEngine::new();
        let result = engine.apply_strengthen_proposals(&[proposal], 0, 0);

        assert_eq!(result.governance_skips, 1);
        assert_eq!(result.rewrites_applied, 0);
        assert_eq!(result.files_modified, 0);
        assert!(result.pending_rewrites.is_empty());
    }

    #[test]
    fn test_backprop_engine_queues_expression_rewrites_for_review() {
        let dir = std::env::temp_dir().join("trust_rewrite_review_test");
        std::fs::create_dir_all(&dir).unwrap();
        let file = dir.join("review.rs");
        let original = "fn add(a: u32, b: u32) -> u32 {\n    a + b\n}\n";
        std::fs::write(&file, original).unwrap();

        let proposal = Proposal {
            function_path: file.display().to_string(),
            function_name: "add".into(),
            kind: ProposalKind::SafeArithmetic {
                original: "a + b".into(),
                replacement: "a.checked_add(b).expect(\"addition overflow\")".into(),
            },
            confidence: 0.95,
            rationale: "replace unchecked add".into(),
        };

        let mut engine = BackpropEngine::new();
        let result = engine.apply_strengthen_proposals(&[proposal], 0, 0);

        assert_eq!(result.rewrites_applied, 0);
        assert_eq!(result.pending_rewrites.len(), 1);
        assert_eq!(result.pending_rewrites[0].policy, ApprovalPolicy::Review);
        assert_eq!(std::fs::read_to_string(&file).unwrap(), original);

        std::fs::remove_file(&file).ok();
        std::fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn test_build_rewrite_records_includes_structured_diff() {
        let dir = std::env::temp_dir().join("trust_rewrite_record_test");
        std::fs::create_dir_all(&dir).unwrap();
        let file = dir.join("record.rs");
        let original = "fn add(a: u32, b: u32) -> u32 {\n    a + b\n}\n";
        std::fs::write(&file, original).unwrap();

        let rewrite = SourceRewrite {
            file_path: file.display().to_string(),
            offset: 0,
            kind: trust_backprop::RewriteKind::InsertAttribute {
                attribute: "#[requires(\"a <= u32::MAX - b\")]".into(),
            },
            function_name: "add".into(),
            rationale: "prevent overflow".into(),
        };
        let modified = format!("#[requires(\"a <= u32::MAX - b\")]\n{original}");
        let file_results = vec![FileRewriteResult {
            path: file.display().to_string(),
            original: original.into(),
            modified,
            rewrite_count: 1,
        }];

        let records = build_rewrite_records(&[rewrite], &[], &file_results);
        assert_eq!(records.len(), 1);
        assert_eq!(records[0].status, "applied");
        let rendered = format_unified(records[0].diff.as_ref().expect("diff should exist"));
        assert!(rendered.contains("+#[requires(\"a <= u32::MAX - b\")]"));

        std::fs::remove_file(&file).ok();
        std::fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn test_append_audit_entries_captures_diff_and_auto_approval() {
        let diff = generate_diff(
            "fn add(a: u32, b: u32) -> u32 {\n    a + b\n}\n",
            "#[requires(\"a <= u32::MAX - b\")]\nfn add(a: u32, b: u32) -> u32 {\n    a + b\n}\n",
            "src/lib.rs",
        );
        let record = RepairRewriteRecord {
            status: "applied".into(),
            policy: Some("auto".into()),
            reviewer_notes: None,
            rewrite: SourceRewrite {
                file_path: "src/lib.rs".into(),
                offset: 0,
                kind: trust_backprop::RewriteKind::InsertAttribute {
                    attribute: "#[requires(\"a <= u32::MAX - b\")]".into(),
                },
                function_name: "add".into(),
                rationale: "prevent overflow".into(),
            },
            diff: Some(diff),
            preview_error: None,
        };

        let mut trail = AuditTrail::new();
        append_audit_entries(&mut trail, 1, &[record]);

        assert_eq!(trail.entries().len(), 1);
        assert_eq!(trail.entries()[0].approval_status, ApprovalStatus::Auto);
        assert!(
            trail.entries()[0]
                .before_after_diff
                .as_deref()
                .unwrap_or_default()
                .contains("#[requires(\"a <= u32::MAX - b\")]")
        );
    }
}
