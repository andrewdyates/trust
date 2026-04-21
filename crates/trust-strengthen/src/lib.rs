#![allow(dead_code)]
//! trust-strengthen: AI-driven spec inference for the prove-strengthen-backprop loop.
//!
//! Reads proof reports (which VCs failed), analyzes failure patterns, and proposes
//! specifications (preconditions, postconditions, invariants) that would make the
//! code provable. Part of Idea 2 from VISION.md.
//!
//! Author: Andrew Yates <andrew@andrewdyates.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

pub(crate) mod abstract_domains;
pub(crate) mod abstract_invariant;
mod analyzer;
pub(crate) mod backward_inference;
pub(crate) mod caller_propagation;
pub(crate) mod cex_guided;
pub(crate) mod cex_guided_refinement;
// tRust #483: Counterexample-guided spec refinement loop with Formula-level suggestions.
pub(crate) mod cex_refine;
pub(crate) mod confidence;
pub(crate) mod counterexample;
pub(crate) mod ensemble;
pub(crate) mod feedback;
pub(crate) mod feedback_loop;
pub(crate) mod gate_diagnostics;
pub(crate) mod heuristic;
pub(crate) mod heuristic_rules;
// tRust #548: Houdini conjunctive refinement for invariant inference.
pub(crate) mod houdini;
// tRust #550: ICE (Implication CounterExample) guided learning for invariant inference.
pub(crate) mod ice;
pub(crate) mod llm_budget;
pub(crate) mod llm_cache;
pub(crate) mod llm_claude;
pub(crate) mod llm_escalation;
pub(crate) mod llm_inference;
// llm_token_budget: only compiled when LLM feature is enabled (used by llm_claude).
#[cfg(feature = "llm")]
pub(crate) mod llm_token_budget;
pub(crate) mod pattern_library;
pub(crate) mod patterns;
mod proposer;
pub(crate) mod scoring;
pub(crate) mod source_reader;
pub(crate) mod spec_feedback_loop;
pub(crate) mod spec_inference;
pub(crate) mod spec_mining;
pub(crate) mod spec_proposal;
pub(crate) mod spec_quality;
pub(crate) mod strategy;
pub(crate) mod structural_gate;
// tRust #658: Sunder-direct verification oracle for CEGIS loop.
#[cfg(feature = "sunder")]
pub(crate) mod sunder_oracle;
pub(crate) mod template_match;
pub(crate) mod templates;
pub(crate) mod weakest_precondition;
// tRust #793: Loop invariant feedback from sunder via MIR router.
pub(crate) mod invariant_feedback;

pub use analyzer::{FailureAnalysis, FailurePattern, analyze_failure};
pub use caller_propagation::{
    CallerObligation, CallerPropagator, FnVisibility, PropagationResult, SignatureSpec,
};
pub use gate_diagnostics::{
    DiagnosticKind, FixSuggestion, GateDiagnostic, Severity,
    format_diagnostics, suggest_fix,
};
pub use confidence::{
    CalibrationTracker, ConfidenceBreakdown, ConfidenceEstimator, ConfidenceScore,
    ConfidenceWeights, ProposalSource, RankingStrategy, ScoredProposal, rank_proposals,
};
pub use cex_guided::{CexModel, CexValue, CounterexampleAnalyzer};
pub use cex_guided_refinement::{
    CexAnalyzer, Counterexample, RefinementStrategy, RefinementSuggestion,
    apply_refinement, is_spurious, rank_suggestions,
};
// tRust #483: Re-export counterexample-guided refinement loop types.
pub use cex_refine::{
    CexRefinementSuggestion, CounterexampleAnalysis, IterationResult,
    RefineVerifier, RefinementLoop, SpecWeakness, analyze_counterexample,
    suggest_refinement,
};
pub use counterexample::{CounterexampleHint, HintKind};
pub use ensemble::{
    EnsembleGenerator, EnsembleResult, GeneratorConfig,
    ScoredProposal as EnsembleScoredProposal,
    consensus, dedup_proposals as ensemble_dedup, diversity_bonus, vote,
};
pub use feedback::{
    FeedbackCollector, FeedbackError, FeedbackReport, ImprovedProposal, ProposalOutcome,
    StrategyAdjustment, VerificationOutcome,
};
pub use feedback_loop::{
    FeedbackEntry, FeedbackLoop, FeedbackLoopConfig, FeedbackLoopResult,
    FailureClass, analyze_failures, classify_failures,
};
pub use heuristic::{FunctionSignature, HeuristicStrengthener, VerificationFailure};
pub use heuristic_rules::{
    BoundsCheck, DivisionGuard, HeuristicRule, NonNullReturn, OverflowGuard, ResultOk, RuleEngine,
};
pub use llm_budget::{
    ContentPriority, PromptSection, RequestCost, RunCostTracker, TokenBudget,
    TruncationRecord, estimate_tokens, truncate_source_lines, truncate_to_budget,
};
pub use llm_cache::{CacheConfig, CacheStats as LlmCacheStats, ResponseCache};
pub use llm_claude::{ClaudeConfig, ClaudeLlm};
pub use llm_escalation::{
    EscalatedResponse, EscalationPolicy, EscalationTracker, EscalationTrigger,
    ModelTier, send_with_escalation,
};
// llm_token_budget re-exports removed: TokenBudget, estimate_tokens, truncate_to_budget
// are already exported from llm_budget above. TokenPriority alias also removed (no callers).
pub use llm_inference::{
    EscalationConfig, ExistingSpec, InferenceConfig, InferenceResult, LlmSpecInference,
    ThreeViewContext,
};
// Phase 1 re-exports for typed LLM boundary (#599)
// LlmBackend, LlmRequest, LlmResponse, LlmError, NoOpLlm are defined above in this file.
pub use spec_feedback_loop::{
    AlwaysPassVerifier, FailThenPassVerifier, FeedbackLoopConfig as SpecFeedbackLoopConfig,
    IterationOutcome, IterationRecord, SpecFeedbackLoop, SpecFeedbackResult,
    VerificationOracle, VerifyOutcome,
};
// tRust #658: Sunder-direct verification oracle for CEGIS loop.
#[cfg(feature = "sunder")]
pub use sunder_oracle::{SunderDirectOracle, import_stdlib_seed_specs};
pub use spec_inference::{
    InsertionTarget, StrengtheningProposal, infer_binary_search_specs, infer_null_deref,
    infer_specs, infer_specs_with_cex,
};
pub use spec_proposal::{
    SpecKind, SpecProposal, format_suggestions, validate_spec,
};
pub use spec_quality::{
    MetricKind, QualityConfig, QualityEvaluator, QualityMetrics, QualityReport,
    QualityScore, SpecCoverage,
};
pub use pattern_library::{
    CatalogEntry, CatalogMatch, MonotonicDirection, PatternCatalog, PatternCategory,
    PatternDatabase, PatternMatcher, PatternSuggestion, SpecPattern,
    apply_patterns, apply_patterns_with_db, builtin_patterns, instantiate_pattern, match_pattern,
};
pub use patterns::{CodePattern, PatternMatch, PatternLibrary, recognize_patterns, pattern_matches_to_proposals};
pub use proposer::{Proposal, ProposalKind, strengthen, strengthen_with_context};
pub use source_reader::SourceContext;
pub use structural_gate::{GateConfig, GateResult, ScopedVar, StructuralGate};
pub use template_match::{
    FunctionCategory, TemplateMatchResult, classify_function, match_and_propose,
    proposal_from_template,
};
pub use templates::{SpecTemplate, SpecTemplateKind, instantiate_template, standard_templates};
pub use scoring::{
    ScoringWeights, SpecScore, rank_by_score, rank_by_score_weighted,
    score_proposal, score_proposal_weighted,
};
pub use spec_mining::{
    AssertionKind, MinedAssertion, MinedSpec, SpecMiner, TestCase, TestValue,
    format_as_ensures, format_as_requires, merge_specs,
};
pub use strategy::{Strategy, StrategyRecord, StrategySelector, StrategySummary};
pub use weakest_precondition::{Statement, compute_weakest_precondition, substitute, wp_transform};
// tRust #448: Re-export abstract domain hierarchy types.
pub use abstract_domains::{
    AbstractDomainOps, Bound, CongruenceDomain, CongruenceValue,
    IntervalDomain, OctagonDomain, ReducedProduct,
    reduce_interval_congruence, reduce_interval_octagon,
};
pub use abstract_invariant::{
    AbstractDomain, AbstractInferenceConfig, AbstractInferenceResult,
    DomainPrecision, InvariantCandidate, InvariantInferrer,
};
// tRust #548: Re-export Houdini conjunctive refinement types.
pub use houdini::{
    Counterexample as HoudiniCounterexample, HoudiniConfig, HoudiniError,
    HoudiniRefiner, HoudiniResult, HoudiniVerifier,
};
// tRust #550: Re-export ICE learning types.
pub use ice::{
    ConcreteState, IceConfig, IceCounterexample, IceError, IceLearner,
    IceResult, IceVerifier, ImplicationExample,
};
// tRust: Re-export backward_inference types for structured AI Model integration (#364)
pub use backward_inference::{
    FailureDescription, FunctionSummary, InferredSpec, InferredSpecItem,
    SpecCategory, SpecInferenceRequest, SpecParseError, ValidationError,
    ValidationResult as BackwardValidationResult,
    format_inference_prompt, parse_inference_response, validate_inferred_spec,
};
// tRust #793: Re-export loop invariant feedback types.
pub use invariant_feedback::{
    apply_invariant_hints, from_sunder_invariants, rank_invariant_hints, InvariantHint,
};

use trust_types::{CrateVerificationResult, VerificationResult};

/// Configuration for the strengthen pass.
#[derive(Debug, Clone)]
pub struct StrengthenConfig {
    /// Minimum confidence threshold for proposals (0.0-1.0).
    pub min_confidence: f64,
    /// Maximum number of proposals per function.
    pub max_proposals_per_function: usize,
    /// Whether to use LLM for complex spec inference.
    pub use_llm: bool,
}

impl Default for StrengthenConfig {
    fn default() -> Self {
        Self {
            min_confidence: 0.5,
            max_proposals_per_function: 10,
            use_llm: false,
        }
    }
}

// -- LLM Backend typed request/response boundary (Phase 1, #599) --

/// Typed request for the LLM backend.
///
/// Contains the fully-assembled prompt and model parameters. The backend
/// is responsible only for HTTP transport; prompt construction lives in
/// `LlmSpecInference`.
#[derive(Debug, Clone)]
pub struct LlmRequest {
    /// The fully-assembled prompt text.
    pub prompt: String,
    /// Which model to use for this request.
    pub model: String,
    /// Maximum response tokens.
    pub max_response_tokens: u32,
    /// Whether to use tool_use structured output.
    pub use_tool_use: bool,
}

/// Typed response from the LLM backend.
#[derive(Debug, Clone)]
pub struct LlmResponse {
    /// Raw response text (for free-form) or parsed JSON (for tool_use).
    pub content: String,
    /// Whether tool_use was successfully used.
    pub used_tool_use: bool,
    /// Which model actually served this request.
    pub model_used: String,
}

/// Error type for LLM backend transport.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum LlmError {
    /// API request failed with a transport or protocol error.
    #[error("API request failed: {0}")]
    Request(String),
    /// API key not configured in environment or config.
    #[error("API key not configured")]
    MissingApiKey,
    /// Rate limited by the API; caller should retry after the indicated delay.
    #[error("rate limited, retry after {retry_after_ms}ms")]
    RateLimited {
        /// Milliseconds to wait before retrying.
        retry_after_ms: u64,
    },
    /// Circuit breaker is open after repeated failures.
    #[error("circuit breaker open after {failures} consecutive failures")]
    CircuitBreakerOpen {
        /// Number of consecutive failures that tripped the breaker.
        failures: u32,
    },
    /// Request timed out.
    #[error("request timed out after {timeout_secs}s")]
    Timeout {
        /// Timeout duration in seconds.
        timeout_secs: u64,
    },
    /// Server returned an error status code.
    #[error("server error: HTTP {status}")]
    ServerError {
        /// HTTP status code.
        status: u16,
    },
}

/// Trait for LLM backends used by strengthen.
///
/// Abstracted for testability — tests use `NoOpLlm` or mocks, production
/// uses `ClaudeLlm`. The backend is a pure HTTP transport: it sends the
/// request and returns the raw response. Prompt building, response parsing,
/// caching, and escalation live in `LlmSpecInference`.
pub trait LlmBackend: Send + Sync {
    /// Send a typed request to the LLM and return the raw response.
    fn send(&self, request: &LlmRequest) -> Result<LlmResponse, LlmError>;
}

/// A no-op LLM backend for when LLM inference is disabled.
pub struct NoOpLlm;

impl LlmBackend for NoOpLlm {
    fn send(&self, _request: &LlmRequest) -> Result<LlmResponse, LlmError> {
        Ok(LlmResponse {
            content: "[]".into(),
            used_tool_use: false,
            model_used: "none".into(),
        })
    }
}

/// Result of a strengthen pass over a crate's verification results.
#[derive(Debug, Clone)]
pub struct StrengthenOutput {
    /// Proposed specifications, grouped by function.
    pub proposals: Vec<Proposal>,
    /// Number of failures analyzed.
    pub failures_analyzed: usize,
    /// Whether strengthen produced any actionable proposals.
    pub has_proposals: bool,
}

/// Run the strengthen pass over a crate's verification results.
///
/// This is the main entry point. It:
/// 1. Analyzes which VCs failed and why
/// 2. Classifies failures into patterns (overflow, div-by-zero, OOB, etc.)
/// 3. Proposes specs that would make the VCs provable
/// 4. Optionally calls an LLM for complex cases
pub fn run(
    results: &CrateVerificationResult,
    config: &StrengthenConfig,
    llm: &dyn LlmBackend,
) -> StrengthenOutput {
    let mut all_proposals = Vec::new();
    let mut total_failures = 0;

    for func in &results.functions {
        let failures: Vec<_> = func.results.iter()
            .filter(|(_, result)| matches!(result, VerificationResult::Failed { .. }))
            .collect();

        if failures.is_empty() {
            continue;
        }

        total_failures += failures.len();

        // Analyze failure patterns
        let analyses: Vec<_> = failures.iter()
            .map(|(vc, result)| analyzer::analyze_failure(vc, result))
            .collect();

        // Generate pattern-based proposals
        let mut proposals = proposer::strengthen(
            &func.function_path,
            &func.function_name,
            &analyses,
        );

        // Optionally augment with LLM proposals
        if config.use_llm {
            let prompt = llm_claude::build_prompt(
                &func.function_name,
                &func.function_path,
                &analyses,
            );
            let request = LlmRequest {
                prompt,
                model: String::new(), // backend uses its configured default
                max_response_tokens: 1024,
                use_tool_use: false,
            };
            if let Ok(response) = llm.send(&request) {
                let llm_proposals = llm_claude::parse_llm_response(
                    &response.content,
                    &func.function_name,
                    &func.function_path,
                );
                proposals.extend(llm_proposals);
            }
        }

        // Filter by confidence and limit
        proposals.retain(|p| p.confidence >= config.min_confidence);
        proposals.truncate(config.max_proposals_per_function);

        all_proposals.extend(proposals);
    }

    StrengthenOutput {
        has_proposals: !all_proposals.is_empty(),
        proposals: all_proposals,
        failures_analyzed: total_failures,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_types::{BinOp, Formula, FunctionVerificationResult, SourceSpan, Ty, VcKind, VerificationCondition};

    fn make_overflow_failure() -> (VerificationCondition, VerificationResult) {
        let vc = VerificationCondition {
            kind: VcKind::ArithmeticOverflow {
                op: BinOp::Add,
                operand_tys: (Ty::Int { width: 64, signed: false }, Ty::Int { width: 64, signed: false }),
            },
            function: "get_midpoint".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        };
        let result = VerificationResult::Failed {
            solver: "z4".into(),
            time_ms: 1,
            counterexample: None,
        };
        (vc, result)
    }

    fn make_div_zero_failure() -> (VerificationCondition, VerificationResult) {
        let vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "safe_divide".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        };
        let result = VerificationResult::Failed {
            solver: "z4".into(),
            time_ms: 1,
            counterexample: None,
        };
        (vc, result)
    }

    fn make_oob_failure() -> (VerificationCondition, VerificationResult) {
        let vc = VerificationCondition {
            kind: VcKind::IndexOutOfBounds,
            function: "get_element".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        };
        let result = VerificationResult::Failed {
            solver: "z4".into(),
            time_ms: 1,
            counterexample: None,
        };
        (vc, result)
    }

    #[test]
    fn test_strengthen_proposes_overflow_precondition() {
        let results = CrateVerificationResult {
            crate_name: "test".into(),
            functions: vec![FunctionVerificationResult {
                function_path: "test::get_midpoint".into(),
                function_name: "get_midpoint".into(),
                results: vec![make_overflow_failure()],
                from_notes: 0,
                with_assumptions: 0,
            }],
            total_from_notes: 0,
            total_with_assumptions: 0,
        };

        let output = run(&results, &StrengthenConfig::default(), &NoOpLlm);
        assert!(output.has_proposals);
        assert_eq!(output.failures_analyzed, 1);
        assert!(!output.proposals.is_empty());

        let proposal = &output.proposals[0];
        assert!(matches!(proposal.kind, ProposalKind::AddPrecondition { .. }));
        assert!(proposal.confidence > 0.0);
    }

    #[test]
    fn test_strengthen_proposes_div_zero_precondition() {
        let results = CrateVerificationResult {
            crate_name: "test".into(),
            functions: vec![FunctionVerificationResult {
                function_path: "test::safe_divide".into(),
                function_name: "safe_divide".into(),
                results: vec![make_div_zero_failure()],
                from_notes: 0,
                with_assumptions: 0,
            }],
            total_from_notes: 0,
            total_with_assumptions: 0,
        };

        let output = run(&results, &StrengthenConfig::default(), &NoOpLlm);
        assert!(output.has_proposals);
        let proposal = &output.proposals[0];
        assert!(matches!(proposal.kind, ProposalKind::AddPrecondition { .. }));
    }

    #[test]
    fn test_strengthen_proposes_oob_precondition() {
        let results = CrateVerificationResult {
            crate_name: "test".into(),
            functions: vec![FunctionVerificationResult {
                function_path: "test::get_element".into(),
                function_name: "get_element".into(),
                results: vec![make_oob_failure()],
                from_notes: 0,
                with_assumptions: 0,
            }],
            total_from_notes: 0,
            total_with_assumptions: 0,
        };

        let output = run(&results, &StrengthenConfig::default(), &NoOpLlm);
        assert!(output.has_proposals);
        let proposal = &output.proposals[0];
        assert!(matches!(proposal.kind, ProposalKind::AddPrecondition { .. }));
    }

    #[test]
    fn test_strengthen_skips_proved_functions() {
        let results = CrateVerificationResult {
            crate_name: "test".into(),
            functions: vec![FunctionVerificationResult {
                function_path: "test::always_ok".into(),
                function_name: "always_ok".into(),
                results: vec![(
                    VerificationCondition {
                        kind: VcKind::DivisionByZero,
                        function: "always_ok".into(),
                        location: SourceSpan::default(),
                        formula: Formula::Bool(true),
                        contract_metadata: None,
                    },
                    VerificationResult::Proved { solver: "z4".into(), time_ms: 1, strength: trust_types::ProofStrength::smt_unsat(), proof_certificate: None, solver_warnings: None },
                )],
                from_notes: 0,
                with_assumptions: 0,
            }],
            total_from_notes: 0,
            total_with_assumptions: 0,
        };

        let output = run(&results, &StrengthenConfig::default(), &NoOpLlm);
        assert!(!output.has_proposals);
        assert_eq!(output.failures_analyzed, 0);
    }

    #[test]
    fn test_strengthen_respects_confidence_threshold() {
        let results = CrateVerificationResult {
            crate_name: "test".into(),
            functions: vec![FunctionVerificationResult {
                function_path: "test::get_midpoint".into(),
                function_name: "get_midpoint".into(),
                results: vec![make_overflow_failure()],
                from_notes: 0,
                with_assumptions: 0,
            }],
            total_from_notes: 0,
            total_with_assumptions: 0,
        };

        let config = StrengthenConfig {
            min_confidence: 1.0, // impossibly high
            ..Default::default()
        };
        let output = run(&results, &config, &NoOpLlm);
        assert!(!output.has_proposals);
    }

    #[test]
    fn test_strengthen_multiple_failures() {
        let results = CrateVerificationResult {
            crate_name: "test".into(),
            functions: vec![
                FunctionVerificationResult {
                    function_path: "test::get_midpoint".into(),
                    function_name: "get_midpoint".into(),
                    results: vec![make_overflow_failure()],
                    from_notes: 0,
                    with_assumptions: 0,
                },
                FunctionVerificationResult {
                    function_path: "test::safe_divide".into(),
                    function_name: "safe_divide".into(),
                    results: vec![make_div_zero_failure()],
                    from_notes: 0,
                    with_assumptions: 0,
                },
            ],
            total_from_notes: 0,
            total_with_assumptions: 0,
        };

        let output = run(&results, &StrengthenConfig::default(), &NoOpLlm);
        assert!(output.has_proposals);
        assert_eq!(output.failures_analyzed, 2);
        assert!(output.proposals.len() >= 2);
    }
}
