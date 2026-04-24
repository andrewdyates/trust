// trust-strengthen/llm_inference.rs: LLM-driven spec inference with three-view prompting
//
// Implements the "three-view" spec inference approach from issue #188:
// the LLM sees original source + MIR + reconstructed source (three
// perspectives of the same function) for better spec inference.
//
// Uses the existing LlmBackend trait for testability (mock in tests,
// AI Model in production). Integrates with spec_proposal for structured output.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::sync::Mutex;

use crate::analyzer::FailureAnalysis;
use crate::llm_budget::{
    ContentPriority, PromptSection, TokenBudget, TruncationRecord, truncate_to_budget,
};
use crate::llm_cache::{CacheConfig, CacheKey, ResponseCache};
use crate::llm_claude::{build_prompt, parse_llm_response};
use crate::llm_escalation::EscalationTrigger;
use crate::source_reader::SourceContext;
use crate::spec_proposal::{SpecKind, SpecProposal, validate_spec};
use crate::{LlmBackend, LlmRequest};

/// Three-view context for a function: original source, MIR, and reconstructed source.
///
/// This is the key innovation: the LLM sees what the compiler sees (MIR),
/// what the programmer wrote (original), and a decompiled view (reconstructed)
/// that reveals implicit operations like coercions, auto-deref, and macro expansions.
#[derive(Debug, Clone)]
pub struct ThreeViewContext {
    /// The original source code of the function (from SourceSpan).
    pub original_source: Option<String>,
    /// The MIR dump of the function (from rustc MIR pretty printer).
    pub mir_text: Option<String>,
    /// Reconstructed Rust-like source from MIR (reveals compiler-visible structure).
    pub reconstructed_source: Option<String>,
    /// Existing specs already annotated on the function.
    pub existing_specs: Vec<ExistingSpec>,
    /// Extracted source context (param names, types, return type).
    pub source_context: Option<SourceContext>,
}

/// An existing spec annotation already on a function.
#[derive(Debug, Clone)]
pub struct ExistingSpec {
    /// The kind of spec.
    pub kind: SpecKind,
    /// The spec body expression.
    pub body: String,
}

/// Configuration for model escalation within the inference engine (Phase 6, #616).
///
/// When enabled, inference starts with `initial_model` and escalates to
/// `escalation_model` on trigger (empty response, low confidence, parse failure).
/// The `max_escalations` field is a hard budget per engine lifetime.
#[derive(Debug, Clone)]
pub struct EscalationConfig {
    /// Model to start with (default: AI Model-sonnet-4-20250514).
    pub initial_model: String,
    /// Model to escalate to (default: AI Model-opus-4-20250514).
    pub escalation_model: String,
    /// Whether escalation is enabled (default: true).
    pub enabled: bool,
    /// Hard budget: max escalations per engine lifetime (default: 3).
    pub max_escalations: u32,
}

impl Default for EscalationConfig {
    fn default() -> Self {
        Self {
            initial_model: "AI Model-sonnet-4-20250514".into(),
            escalation_model: "AI Model-opus-4-20250514".into(),
            enabled: true,
            max_escalations: 3,
        }
    }
}

impl EscalationConfig {
    /// Confidence threshold percentage for low-confidence escalation trigger.
    /// Proposals with max confidence below this trigger escalation.
    #[must_use]
    pub fn confidence_threshold_pct(&self) -> u32 {
        50 // Default: escalate if all proposals < 50% confidence
    }
}

/// Configuration for the LLM inference engine.
#[derive(Debug, Clone)]
pub struct InferenceConfig {
    /// Maximum number of specs to request per inference call.
    pub max_specs: usize,
    /// Minimum confidence threshold for accepting inferred specs.
    pub min_confidence: f64,
    /// Whether to include MIR in the prompt (can be verbose).
    pub include_mir: bool,
    /// Whether to include reconstructed source.
    pub include_reconstructed: bool,
    /// Whether to validate inferred specs against the function signature.
    pub validate_against_signature: bool,
    /// Token budget for prompt construction (Phase 5, #613).
    ///
    /// Controls maximum prompt size, response allocation, and truncation
    /// behavior. Budget lives here only (not in ClaudeConfig).
    pub token_budget: TokenBudget,
    /// Model escalation configuration (Phase 6, #616).
    pub escalation: EscalationConfig,
}

impl Default for InferenceConfig {
    fn default() -> Self {
        Self {
            max_specs: 5,
            min_confidence: 0.3,
            include_mir: true,
            include_reconstructed: true,
            validate_against_signature: true,
            token_budget: TokenBudget::default(),
            escalation: EscalationConfig::default(),
        }
    }
}

/// Result of one LLM inference call.
#[derive(Debug, Clone)]
pub struct InferenceResult {
    /// Inferred spec proposals.
    pub proposals: Vec<SpecProposal>,
    /// The prompt that was sent (for debugging and refinement).
    pub prompt_used: String,
    /// Number of raw proposals before validation/filtering.
    pub raw_count: usize,
    /// Number of proposals rejected by validation.
    pub validation_rejected: usize,
    /// Whether this result was served from cache (Phase 3, #606).
    pub cache_hit: bool,
    /// Record of truncations applied to fit within the token budget (Phase 5, #613).
    pub truncations_applied: TruncationRecord,
    /// Which model actually served this request (Phase 6, #616).
    pub model_used: String,
    /// Whether model escalation occurred (Phase 6, #616).
    pub escalated: bool,
}

/// The LLM spec inference engine.
///
/// Takes a function's three-view context and failure information,
/// builds a rich prompt, calls the LLM, and returns validated spec proposals.
///
/// Includes response caching (Phase 3, #606): repeated calls with the same
/// prompt, model, and tool_use flag return cached responses. The cache is
/// keyed by SHA-256(prompt + model + tool_use) and validates against a
/// source_hash to detect stale entries.
pub struct LlmSpecInference<'a> {
    backend: &'a dyn LlmBackend,
    config: InferenceConfig,
    /// Response cache wrapped in Mutex for Send + Sync (Phase 3, #606).
    cache: Mutex<ResponseCache>,
    /// Whether to bypass the cache for this engine instance.
    bypass_cache: bool,
    /// Lifetime escalation count for budget enforcement (Phase 6, #616).
    escalation_count: Mutex<u32>,
}

impl<'a> LlmSpecInference<'a> {
    /// Create a new inference engine with the given backend and config.
    #[must_use]
    pub fn new(backend: &'a dyn LlmBackend, config: InferenceConfig) -> Self {
        Self {
            backend,
            config,
            cache: Mutex::new(ResponseCache::new()),
            bypass_cache: false,
            escalation_count: Mutex::new(0),
        }
    }

    /// Create a new inference engine with a custom cache configuration.
    #[must_use]
    pub fn with_cache_config(
        backend: &'a dyn LlmBackend,
        config: InferenceConfig,
        cache_config: CacheConfig,
    ) -> Self {
        Self {
            backend,
            config,
            cache: Mutex::new(ResponseCache::with_config(cache_config)),
            bypass_cache: false,
            escalation_count: Mutex::new(0),
        }
    }

    /// Set whether to bypass the cache. When true, all requests go to the backend.
    pub fn set_bypass_cache(&mut self, bypass: bool) {
        self.bypass_cache = bypass;
    }

    /// Access the cache statistics.
    #[must_use]
    pub fn cache_stats(&self) -> crate::llm_cache::CacheStats {
        self.cache.lock().expect("cache lock poisoned").stats().clone()
    }

    /// Number of escalations used across the engine's lifetime (Phase 6, #616).
    #[must_use]
    pub fn escalation_count(&self) -> u32 {
        *self.escalation_count.lock().expect("escalation count lock")
    }

    /// Detect which escalation trigger applies after parsing/validation.
    ///
    /// Returns `None` if no trigger fires. Triggers are evaluated in priority order:
    /// 1. `EmptyOrUnparseableResponse` — no proposals parsed at all
    /// 2. `AllProposalsRejected` — all proposals failed validation
    /// 3. `LowConfidenceOnly` — all accepted proposals below threshold
    fn detect_escalation_trigger(
        &self,
        raw_proposals: &[crate::proposer::Proposal],
        filtered_proposals: &[SpecProposal],
        validation_rejected: usize,
    ) -> Option<EscalationTrigger> {
        if raw_proposals.is_empty() {
            return Some(EscalationTrigger::EmptyResponse);
        }
        if !raw_proposals.is_empty() && filtered_proposals.is_empty() && validation_rejected > 0 {
            // All proposals rejected by validation → treat as parse/quality failure
            return Some(EscalationTrigger::ParseFailure);
        }
        if filtered_proposals.is_empty() {
            return Some(EscalationTrigger::EmptyResponse);
        }
        // Check if all proposals have low confidence
        let max_conf =
            filtered_proposals.iter().map(|p| (p.confidence * 100.0) as u32).max().unwrap_or(0);
        let threshold = self.config.escalation.confidence_threshold_pct();
        if max_conf < threshold {
            return Some(EscalationTrigger::LowConfidence { max_confidence: max_conf });
        }
        None
    }

    /// Infer specs for a function using the three-view context and failure analysis.
    ///
    /// This is the main entry point. It:
    /// 1. Builds a three-view prompt
    /// 2. Checks cache for a prior response (Phase 3, #606)
    /// 3. On miss, calls the LLM backend and caches the response
    /// 4. Parses and validates the response
    /// 5. Returns structured SpecProposal objects
    ///
    /// The `source_hash` parameter is used for cache invalidation: if the
    /// source code changes, cached responses for that function are discarded.
    /// Pass 0 to disable source-hash invalidation.
    pub fn infer(
        &self,
        function_name: &str,
        function_path: &str,
        context: &ThreeViewContext,
        failures: &[FailureAnalysis],
        iteration: usize,
    ) -> InferenceResult {
        self.infer_with_source_hash(function_name, function_path, context, failures, iteration, 0)
    }

    /// Infer specs with explicit source hash for cache invalidation.
    ///
    /// Same as [`infer`] but takes a `source_hash` for cache invalidation.
    /// When the source code of the function changes, pass a different hash
    /// to ensure stale cached responses are discarded.
    ///
    /// Phase 6 (#616): When escalation is enabled, the method evaluates
    /// escalation triggers after parsing/validation. If all proposals are
    /// rejected, confidence is too low, or the response is empty/unparseable,
    /// it retries with the escalation model (subject to `max_escalations` budget).
    pub fn infer_with_source_hash(
        &self,
        function_name: &str,
        function_path: &str,
        context: &ThreeViewContext,
        failures: &[FailureAnalysis],
        iteration: usize,
        source_hash: u64,
    ) -> InferenceResult {
        let initial_model = if self.config.escalation.enabled {
            self.config.escalation.initial_model.clone()
        } else {
            String::new() // backend uses its configured default
        };
        let use_tool_use = false;

        // Phase 5 (#613): Build prompt with budget-aware truncation
        let (prompt, truncation_record) =
            self.build_three_view_prompt(function_name, context, failures, use_tool_use);

        // Phase 3 (#606): Check cache before calling backend
        let cache_key = CacheKey::new(&prompt, &initial_model, use_tool_use);
        if !self.bypass_cache {
            let mut cache = self.cache.lock().expect("cache lock poisoned");
            if let Some(cached_response) = cache.get(&cache_key, source_hash) {
                let raw_proposals =
                    parse_llm_response(&cached_response.content, function_name, function_path);
                let raw_count = raw_proposals.len();
                let (proposals, validation_rejected) = self.validate_and_filter(
                    &raw_proposals,
                    function_name,
                    function_path,
                    context,
                    iteration,
                );
                return InferenceResult {
                    proposals,
                    prompt_used: prompt,
                    raw_count,
                    validation_rejected,
                    cache_hit: true,
                    truncations_applied: truncation_record,
                    model_used: cached_response.model_used.clone(),
                    escalated: false,
                };
            }
        }

        // Build typed request and send to backend
        let max_response_tokens = self.config.token_budget.max_response_tokens as u32;
        let request = LlmRequest {
            prompt: prompt.clone(),
            model: initial_model,
            max_response_tokens,
            use_tool_use,
        };

        // Call the LLM backend, then parse the response into proposals
        let (raw_proposals, response_for_cache, model_used) = match self.backend.send(&request) {
            Ok(response) => {
                let proposals = parse_llm_response(&response.content, function_name, function_path);
                let model = response.model_used.clone();
                (proposals, Some(response), model)
            }
            Err(_) => (Vec::new(), None, String::new()),
        };
        let raw_count = raw_proposals.len();

        // Convert to SpecProposals and validate
        let (proposals, validation_rejected) = self.validate_and_filter(
            &raw_proposals,
            function_name,
            function_path,
            context,
            iteration,
        );

        // Phase 6 (#616): Evaluate escalation triggers after parsing/validation
        let escalation_cfg = &self.config.escalation;
        if escalation_cfg.enabled
            && proposals.is_empty()
            && let Some(trigger) =
                self.detect_escalation_trigger(&raw_proposals, &proposals, validation_rejected)
        {
            let mut esc_count = self.escalation_count.lock().expect("escalation count lock");
            if *esc_count < escalation_cfg.max_escalations {
                *esc_count += 1;
                drop(esc_count); // release lock before backend call

                // Enrich prompt with failure reason from prior attempt
                let enriched_prompt = format!(
                    "{}\n\n## Prior Attempt Failed\n\n\
                         The previous attempt with the initial model failed: {}.\n\
                         Please provide higher-quality specifications.",
                    prompt, trigger,
                );

                let escalation_request = LlmRequest {
                    prompt: enriched_prompt,
                    model: escalation_cfg.escalation_model.clone(),
                    max_response_tokens,
                    use_tool_use,
                };

                if let Ok(esc_response) = self.backend.send(&escalation_request) {
                    let esc_proposals =
                        parse_llm_response(&esc_response.content, function_name, function_path);
                    let esc_raw_count = esc_proposals.len();
                    let esc_model = esc_response.model_used.clone();

                    // Cache the escalated response
                    if !self.bypass_cache {
                        let esc_cache_key =
                            CacheKey::new(&prompt, &escalation_cfg.escalation_model, use_tool_use);
                        let mut cache = self.cache.lock().expect("cache lock poisoned");
                        cache.insert(esc_cache_key, esc_response, source_hash);
                    }

                    let (esc_filtered, esc_rejected) = self.validate_and_filter(
                        &esc_proposals,
                        function_name,
                        function_path,
                        context,
                        iteration,
                    );

                    return InferenceResult {
                        proposals: esc_filtered,
                        prompt_used: prompt,
                        raw_count: esc_raw_count,
                        validation_rejected: esc_rejected,
                        cache_hit: false,
                        truncations_applied: truncation_record,
                        model_used: esc_model,
                        escalated: true,
                    };
                }
            } else {
                eprintln!(
                    "[trust-strengthen] escalation budget exhausted ({}/{}) for {}",
                    *esc_count, escalation_cfg.max_escalations, function_name,
                );
            }
        }

        // Cache the initial response on success
        if !self.bypass_cache
            && let Some(response) = response_for_cache
        {
            let mut cache = self.cache.lock().expect("cache lock poisoned");
            cache.insert(cache_key, response, source_hash);
        }

        InferenceResult {
            proposals,
            prompt_used: prompt,
            raw_count,
            validation_rejected,
            cache_hit: false,
            truncations_applied: truncation_record,
            model_used,
            escalated: false,
        }
    }

    /// Infer specs with counterexample refinement.
    ///
    /// When a previous inference attempt produced specs that failed VC checking,
    /// this method adds the counterexample to the prompt to help the LLM refine.
    #[allow(clippy::too_many_arguments)]
    pub fn infer_with_counterexample(
        &self,
        function_name: &str,
        function_path: &str,
        context: &ThreeViewContext,
        failures: &[FailureAnalysis],
        prior_specs: &[SpecProposal],
        counterexample: &str,
        iteration: usize,
    ) -> InferenceResult {
        let use_tool_use = false;
        let (base_prompt, truncation_record) =
            self.build_three_view_prompt(function_name, context, failures, use_tool_use);

        let prior_text = prior_specs
            .iter()
            .map(|s| format!("  - {}", s.to_attribute()))
            .collect::<Vec<_>>()
            .join("\n");

        let refined_prompt = format!(
            "{base_prompt}\n\n\
             ## Prior Attempt (Failed Verification)\n\n\
             The following specs were previously proposed but failed:\n\
             {prior_text}\n\n\
             Counterexample from the solver:\n\
             ```\n\
             {counterexample}\n\
             ```\n\n\
             Please propose REFINED specs that handle this counterexample. \
             The refined specs should be strictly stronger than the prior attempt."
        );

        let max_response_tokens = self.config.token_budget.max_response_tokens as u32;
        let refined_request = LlmRequest {
            prompt: refined_prompt.clone(),
            model: String::new(),
            max_response_tokens,
            use_tool_use,
        };

        let (raw_proposals, model_used) = match self.backend.send(&refined_request) {
            Ok(response) => {
                let model = response.model_used.clone();
                (parse_llm_response(&response.content, function_name, function_path), model)
            }
            Err(_) => (Vec::new(), String::new()),
        };
        let raw_count = raw_proposals.len();

        let (proposals, validation_rejected) = self.validate_and_filter(
            &raw_proposals,
            function_name,
            function_path,
            context,
            iteration,
        );

        InferenceResult {
            proposals,
            prompt_used: refined_prompt,
            raw_count,
            validation_rejected,
            cache_hit: false,
            truncations_applied: truncation_record,
            model_used,
            escalated: false,
        }
    }

    /// Validate and filter raw proposals against the function signature and
    /// confidence threshold. Returns `(accepted_proposals, validation_rejected_count)`.
    fn validate_and_filter(
        &self,
        raw_proposals: &[crate::proposer::Proposal],
        function_name: &str,
        function_path: &str,
        context: &ThreeViewContext,
        iteration: usize,
    ) -> (Vec<SpecProposal>, usize) {
        let mut proposals = Vec::new();
        let mut validation_rejected = 0;

        for raw in raw_proposals {
            if let Some(mut spec) = SpecProposal::from_proposal_kind(
                &raw.kind,
                function_path,
                function_name,
                raw.confidence,
                &raw.rationale,
                iteration,
            ) {
                if self.config.validate_against_signature
                    && let Some(ref src_ctx) = context.source_context
                {
                    let param_names: Vec<String> =
                        src_ctx.params.iter().map(|(n, _)| n.clone()).collect();
                    let return_type = src_ctx.return_type.as_deref();
                    let errors = validate_spec(&spec, &param_names, return_type);
                    spec.validation_errors = errors;
                    spec.validated = true;
                }

                if spec.confidence >= self.config.min_confidence
                    && (!self.config.validate_against_signature
                        || spec.validation_errors.is_empty())
                {
                    proposals.push(spec);
                } else if !spec.validation_errors.is_empty() {
                    validation_rejected += 1;
                }
            }
        }

        proposals.truncate(self.config.max_specs);
        (proposals, validation_rejected)
    }

    /// Build the three-view prompt for the LLM, applying token budget truncation.
    ///
    /// Returns `(prompt_text, truncation_record)`. When the assembled prompt
    /// exceeds the token budget, lowest-priority sections are removed first.
    fn build_three_view_prompt(
        &self,
        function_name: &str,
        context: &ThreeViewContext,
        failures: &[FailureAnalysis],
        use_tool_use: bool,
    ) -> (String, TruncationRecord) {
        let safety_margin = self.config.token_budget.safety_margin;

        // Build the source text for the base prompt: use original source if available,
        // else reconstructed, else a placeholder
        let source_for_base = context
            .original_source
            .as_deref()
            .or(context.reconstructed_source.as_deref())
            .unwrap_or("// source unavailable");

        // Use the existing build_prompt for the base structure (signature + failures + instructions)
        let base = build_prompt(function_name, source_for_base, failures);

        // Build prioritized sections for budget management (Phase 5, #613)
        let mut prompt_sections = Vec::new();

        // The base prompt contains signature + failure descriptions + instructions.
        // We treat it as highest-priority (Signature level) since it's the core prompt.
        prompt_sections.push(PromptSection::new(
            ContentPriority::Signature,
            base.clone(),
            safety_margin,
        ));

        // Section: Original source (additional three-view copy)
        if let Some(ref original) = context.original_source {
            prompt_sections.push(PromptSection::new(
                ContentPriority::OriginalSource,
                format!("## View 1: Original Source\n\n```rust\n{original}\n```"),
                safety_margin,
            ));
        }

        // Section: MIR (optional, can be very verbose)
        if self.config.include_mir
            && let Some(ref mir) = context.mir_text
        {
            prompt_sections.push(PromptSection::new(
                ContentPriority::MirText,
                format!(
                    "## View 2: MIR (Compiler Internal Representation)\n\n\
                         This shows the function after type checking, borrow checking, \
                         and monomorphization. It reveals implicit operations.\n\n\
                         ```\n{mir}\n```"
                ),
                safety_margin,
            ));
        }

        // Section: Reconstructed source (optional)
        if self.config.include_reconstructed
            && let Some(ref reconstructed) = context.reconstructed_source
        {
            prompt_sections.push(PromptSection::new(
                ContentPriority::ReconstructedSource,
                format!(
                    "## View 3: Reconstructed Source (from MIR)\n\n\
                         This is source code reconstructed from the compiler's internal \
                         representation. It shows what the compiler actually sees, including \
                         macro expansions, trait resolution, and implicit coercions.\n\n\
                         ```rust\n{reconstructed}\n```"
                ),
                safety_margin,
            ));
        }

        // Section: Existing specs
        if !context.existing_specs.is_empty() {
            let specs_text: Vec<String> = context
                .existing_specs
                .iter()
                .map(|s| format!("#[{}(\"{}\")]", s.kind, s.body))
                .collect();
            prompt_sections.push(PromptSection::new(
                ContentPriority::ExistingSpecs,
                format!(
                    "## Existing Specifications\n\n{}\n\n\
                     These specs are already annotated on the function. \
                     New specs should be consistent with them.",
                    specs_text.join("\n")
                ),
                safety_margin,
            ));
        }

        // Apply token budget truncation (Phase 5, #613)
        let effective_budget = self.config.token_budget.effective_prompt_budget(use_tool_use);
        let (surviving, truncation_record) = truncate_to_budget(&prompt_sections, effective_budget);

        // Assemble the final prompt from surviving sections
        if surviving.len() <= 1 {
            // Only the base prompt survived (or no sections at all)
            let prompt = surviving.first().map(|s| s.content.clone()).unwrap_or(base);
            (prompt, truncation_record)
        } else {
            // Base prompt is first, then three-view sections
            let base_text = &surviving[0].content;
            let three_view_parts: Vec<&str> =
                surviving[1..].iter().map(|s| s.content.as_str()).collect();
            let three_view_text = three_view_parts.join("\n\n");
            let prompt = format!(
                "{base_text}\n\n\
                 ## Three-View Analysis\n\n\
                 The following views provide additional context about the function. \
                 Use all available views to infer the most precise specifications.\n\n\
                 {three_view_text}"
            );
            (prompt, truncation_record)
        }
    }
}

#[cfg(test)]
mod tests {
    use trust_types::{BinOp, Ty, VcKind};

    use super::*;
    use crate::analyzer::{FailureAnalysis, FailurePattern};
    use crate::source_reader::extract_function;

    /// Mock LLM that returns a canned JSON response via the typed `send()` interface.
    struct MockInferenceLlm {
        response_json: String,
    }

    impl MockInferenceLlm {
        fn with_response(json: &str) -> Self {
            Self { response_json: json.to_string() }
        }
    }

    impl LlmBackend for MockInferenceLlm {
        fn send(
            &self,
            _request: &crate::LlmRequest,
        ) -> Result<crate::LlmResponse, crate::LlmError> {
            Ok(crate::LlmResponse {
                content: self.response_json.clone(),
                used_tool_use: false,
                model_used: "mock".into(),
            })
        }
    }

    fn overflow_failure() -> FailureAnalysis {
        FailureAnalysis {
            vc_kind: VcKind::ArithmeticOverflow {
                op: BinOp::Add,
                operand_tys: (
                    Ty::Int { width: 64, signed: false },
                    Ty::Int { width: 64, signed: false },
                ),
            },
            function: "get_midpoint".into(),
            pattern: FailurePattern::ArithmeticOverflow { op: BinOp::Add },
            solver: Some("z4".into()),
        }
    }

    fn midpoint_context() -> ThreeViewContext {
        let source = "fn get_midpoint(a: usize, b: usize) -> usize {\n    (a + b) / 2\n}";
        ThreeViewContext {
            original_source: Some(source.into()),
            mir_text: Some("bb0: { _3 = Add(_1, _2); _0 = Div(_3, const 2_usize); }".into()),
            reconstructed_source: Some(
                "fn get_midpoint(a: usize, b: usize) -> usize {\n    \
                 let _3: usize = a + b; // may overflow!\n    \
                 let _0: usize = _3 / 2;\n    \
                 return _0;\n}"
                    .into(),
            ),
            existing_specs: Vec::new(),
            source_context: extract_function(source, "get_midpoint"),
        }
    }

    // --- ThreeViewContext ---

    #[test]
    fn test_three_view_context_with_all_views() {
        let ctx = midpoint_context();
        assert!(ctx.original_source.is_some());
        assert!(ctx.mir_text.is_some());
        assert!(ctx.reconstructed_source.is_some());
        assert!(ctx.source_context.is_some());
    }

    #[test]
    fn test_three_view_context_minimal() {
        let ctx = ThreeViewContext {
            original_source: None,
            mir_text: None,
            reconstructed_source: None,
            existing_specs: Vec::new(),
            source_context: None,
        };
        assert!(ctx.original_source.is_none());
    }

    // --- LlmSpecInference ---

    #[test]
    fn test_infer_basic() {
        let mock = MockInferenceLlm::with_response(
            r#"[{"kind": "precondition", "spec_body": "a <= usize::MAX - b", "confidence": 0.9, "rationale": "Overflow guard"}]"#,
        );
        let engine = LlmSpecInference::new(&mock, InferenceConfig::default());

        let result = engine.infer(
            "get_midpoint",
            "test::get_midpoint",
            &midpoint_context(),
            &[overflow_failure()],
            1,
        );

        assert_eq!(result.raw_count, 1);
        assert_eq!(result.proposals.len(), 1);
        assert_eq!(result.proposals[0].kind, SpecKind::Requires);
        assert_eq!(result.proposals[0].spec_body, "a <= usize::MAX - b");
        assert_eq!(result.proposals[0].iteration, 1);
        assert!(result.proposals[0].validated);
        assert!(result.proposals[0].validation_errors.is_empty());
    }

    #[test]
    fn test_infer_filters_by_confidence() {
        let mock = MockInferenceLlm::with_response(
            r#"[
                {"kind": "precondition", "spec_body": "a > 0", "confidence": 0.1, "rationale": "Low confidence"},
                {"kind": "precondition", "spec_body": "b > 0", "confidence": 0.8, "rationale": "High confidence"}
            ]"#,
        );
        let config = InferenceConfig { min_confidence: 0.5, ..Default::default() };
        let engine = LlmSpecInference::new(&mock, config);

        let result = engine.infer(
            "get_midpoint",
            "test::get_midpoint",
            &midpoint_context(),
            &[overflow_failure()],
            1,
        );

        assert_eq!(result.raw_count, 2);
        // Only the high-confidence one should pass
        assert_eq!(result.proposals.len(), 1);
        assert_eq!(result.proposals[0].spec_body, "b > 0");
    }

    #[test]
    fn test_infer_validates_against_signature() {
        let mock = MockInferenceLlm::with_response(
            r#"[{"kind": "precondition", "spec_body": "result > 0", "confidence": 0.9, "rationale": "Bad: uses result in requires"}]"#,
        );
        let engine = LlmSpecInference::new(&mock, InferenceConfig::default());

        let result = engine.infer(
            "get_midpoint",
            "test::get_midpoint",
            &midpoint_context(),
            &[overflow_failure()],
            1,
        );

        // "result" in a requires clause should be rejected by validation
        assert_eq!(result.raw_count, 1);
        assert_eq!(result.validation_rejected, 1);
        assert!(result.proposals.is_empty());
    }

    #[test]
    fn test_infer_without_validation() {
        let mock = MockInferenceLlm::with_response(
            r#"[{"kind": "precondition", "spec_body": "result > 0", "confidence": 0.9, "rationale": "Would normally fail validation"}]"#,
        );
        let config = InferenceConfig { validate_against_signature: false, ..Default::default() };
        let engine = LlmSpecInference::new(&mock, config);

        let result = engine.infer(
            "get_midpoint",
            "test::get_midpoint",
            &midpoint_context(),
            &[overflow_failure()],
            1,
        );

        // Without validation, the proposal should pass through
        assert_eq!(result.proposals.len(), 1);
    }

    #[test]
    fn test_infer_respects_max_specs() {
        let mock = MockInferenceLlm::with_response(
            r#"[
                {"kind": "precondition", "spec_body": "a > 0", "confidence": 0.9, "rationale": "r1"},
                {"kind": "precondition", "spec_body": "b > 0", "confidence": 0.8, "rationale": "r2"},
                {"kind": "postcondition", "spec_body": "result < a", "confidence": 0.7, "rationale": "r3"}
            ]"#,
        );
        let config = InferenceConfig { max_specs: 2, ..Default::default() };
        let engine = LlmSpecInference::new(&mock, config);

        let result = engine.infer(
            "get_midpoint",
            "test::get_midpoint",
            &midpoint_context(),
            &[overflow_failure()],
            1,
        );

        assert!(result.proposals.len() <= 2);
    }

    #[test]
    fn test_infer_with_empty_failures() {
        let mock = MockInferenceLlm::with_response("[]");
        let engine = LlmSpecInference::new(&mock, InferenceConfig::default());

        let result =
            engine.infer("get_midpoint", "test::get_midpoint", &midpoint_context(), &[], 1);

        assert_eq!(result.raw_count, 0);
        assert!(result.proposals.is_empty());
    }

    // --- Prompt building ---

    #[test]
    fn test_prompt_contains_three_views() {
        let mock = MockInferenceLlm::with_response("[]");
        let engine = LlmSpecInference::new(&mock, InferenceConfig::default());
        let ctx = midpoint_context();

        let (prompt, _record) =
            engine.build_three_view_prompt("get_midpoint", &ctx, &[overflow_failure()], false);

        assert!(prompt.contains("View 1: Original Source"), "should have original source view");
        assert!(prompt.contains("View 2: MIR"), "should have MIR view");
        assert!(
            prompt.contains("View 3: Reconstructed Source"),
            "should have reconstructed source view"
        );
        assert!(prompt.contains("Three-View Analysis"), "should have three-view section");
    }

    #[test]
    fn test_prompt_without_mir() {
        let mock = MockInferenceLlm::with_response("[]");
        let config = InferenceConfig { include_mir: false, ..Default::default() };
        let engine = LlmSpecInference::new(&mock, config);
        let ctx = midpoint_context();

        let (prompt, _record) =
            engine.build_three_view_prompt("get_midpoint", &ctx, &[overflow_failure()], false);

        assert!(!prompt.contains("View 2: MIR"), "MIR view should be excluded");
    }

    #[test]
    fn test_prompt_with_existing_specs() {
        let mock = MockInferenceLlm::with_response("[]");
        let engine = LlmSpecInference::new(&mock, InferenceConfig::default());
        let mut ctx = midpoint_context();
        ctx.existing_specs = vec![ExistingSpec { kind: SpecKind::Requires, body: "a > 0".into() }];

        let (prompt, _record) =
            engine.build_three_view_prompt("get_midpoint", &ctx, &[overflow_failure()], false);

        assert!(prompt.contains("Existing Specifications"), "should include existing specs");
        assert!(prompt.contains("a > 0"), "should show existing spec body");
    }

    #[test]
    fn test_prompt_minimal_context() {
        let mock = MockInferenceLlm::with_response("[]");
        let engine = LlmSpecInference::new(&mock, InferenceConfig::default());
        let ctx = ThreeViewContext {
            original_source: None,
            mir_text: None,
            reconstructed_source: None,
            existing_specs: Vec::new(),
            source_context: None,
        };

        let (prompt, _record) =
            engine.build_three_view_prompt("func", &ctx, &[overflow_failure()], false);

        // Should still produce a valid prompt with at least the base prompt
        assert!(prompt.contains("func"), "should contain function name");
    }

    // --- Token budget integration tests (Phase 5, #613) ---

    #[test]
    fn test_budget_truncation_with_large_mir() {
        let mock = MockInferenceLlm::with_response(
            r#"[{"kind": "precondition", "spec_body": "a <= usize::MAX - b", "confidence": 0.9, "rationale": "Overflow guard"}]"#,
        );
        let config = InferenceConfig {
            token_budget: TokenBudget {
                max_prompt_tokens: 200, // Very small budget to force truncation
                ..Default::default()
            },
            ..Default::default()
        };
        let engine = LlmSpecInference::new(&mock, config);

        // Build context with a large MIR dump
        let mut ctx = midpoint_context();
        ctx.mir_text = Some("bb0: { _1 = Add(_2, _3); }\n".repeat(500));

        let result =
            engine.infer("get_midpoint", "test::get_midpoint", &ctx, &[overflow_failure()], 1);

        // Truncation should have been applied
        assert!(result.truncations_applied.was_truncated);
        assert!(!result.truncations_applied.sections_removed.is_empty());
        // Should still produce proposals from the (truncated) prompt
        assert!(!result.proposals.is_empty());
    }

    #[test]
    fn test_budget_no_truncation_when_within_budget() {
        let mock = MockInferenceLlm::with_response("[]");
        let engine = LlmSpecInference::new(&mock, InferenceConfig::default());
        let ctx = midpoint_context();

        let result =
            engine.infer("get_midpoint", "test::get_midpoint", &ctx, &[overflow_failure()], 1);

        // Default budget is 24K tokens, midpoint context is tiny
        assert!(!result.truncations_applied.was_truncated);
        assert!(result.truncations_applied.sections_removed.is_empty());
    }

    #[test]
    fn test_budget_response_tokens_from_config() {
        use crate::llm_budget::TokenBudget;
        let config = InferenceConfig {
            token_budget: TokenBudget { max_response_tokens: 4096, ..Default::default() },
            ..Default::default()
        };
        assert_eq!(config.token_budget.max_response_tokens, 4096);
    }

    // --- Counterexample refinement ---

    #[test]
    fn test_infer_with_counterexample() {
        let mock = MockInferenceLlm::with_response(
            r#"[{"kind": "precondition", "spec_body": "a <= usize::MAX / 2 && b <= usize::MAX / 2", "confidence": 0.95, "rationale": "Tighter bound from counterexample"}]"#,
        );
        let engine = LlmSpecInference::new(&mock, InferenceConfig::default());

        let prior_specs = vec![SpecProposal {
            function_path: "test::get_midpoint".into(),
            function_name: "get_midpoint".into(),
            kind: SpecKind::Requires,
            spec_body: "a > 0".into(),
            confidence: 0.7,
            rationale: "too weak".into(),
            iteration: 1,
            validated: true,
            validation_errors: Vec::new(),
        }];

        let result = engine.infer_with_counterexample(
            "get_midpoint",
            "test::get_midpoint",
            &midpoint_context(),
            &[overflow_failure()],
            &prior_specs,
            "a = 18446744073709551615, b = 1",
            2,
        );

        assert!(!result.proposals.is_empty());
        assert_eq!(result.proposals[0].iteration, 2);
        assert!(
            result.prompt_used.contains("Prior Attempt"),
            "prompt should mention prior attempt"
        );
        assert!(
            result.prompt_used.contains("Counterexample"),
            "prompt should include counterexample"
        );
    }

    #[test]
    fn test_counterexample_prompt_contains_prior_specs() {
        let mock = MockInferenceLlm::with_response("[]");
        let engine = LlmSpecInference::new(&mock, InferenceConfig::default());

        let prior_specs = vec![
            SpecProposal {
                function_path: "test::f".into(),
                function_name: "f".into(),
                kind: SpecKind::Requires,
                spec_body: "a > 0".into(),
                confidence: 0.7,
                rationale: "old".into(),
                iteration: 1,
                validated: true,
                validation_errors: Vec::new(),
            },
            SpecProposal {
                function_path: "test::f".into(),
                function_name: "f".into(),
                kind: SpecKind::Ensures,
                spec_body: "result > a".into(),
                confidence: 0.6,
                rationale: "old".into(),
                iteration: 1,
                validated: true,
                validation_errors: Vec::new(),
            },
        ];

        let result = engine.infer_with_counterexample(
            "get_midpoint",
            "test::get_midpoint",
            &midpoint_context(),
            &[overflow_failure()],
            &prior_specs,
            "a = MAX, b = 1",
            2,
        );

        assert!(
            result.prompt_used.contains("#[requires(\"a > 0\")]"),
            "should include prior requires"
        );
        assert!(
            result.prompt_used.contains("#[ensures(\"result > a\")]"),
            "should include prior ensures"
        );
    }

    // --- Phase 6 (#616): Escalation integration tests ---

    /// Mock LLM that returns different responses based on the model requested.
    struct EscalationAwareMock {
        sonnet_response: String,
        opus_response: String,
        call_count: std::sync::atomic::AtomicU32,
    }

    impl EscalationAwareMock {
        fn new(sonnet_response: &str, opus_response: &str) -> Self {
            Self {
                sonnet_response: sonnet_response.into(),
                opus_response: opus_response.into(),
                call_count: std::sync::atomic::AtomicU32::new(0),
            }
        }

        fn calls(&self) -> u32 {
            self.call_count.load(std::sync::atomic::Ordering::Relaxed)
        }
    }

    impl LlmBackend for EscalationAwareMock {
        fn send(&self, request: &crate::LlmRequest) -> Result<crate::LlmResponse, crate::LlmError> {
            self.call_count.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            let content = if request.model.contains("opus") {
                self.opus_response.clone()
            } else {
                self.sonnet_response.clone()
            };
            Ok(crate::LlmResponse {
                content,
                used_tool_use: false,
                model_used: request.model.clone(),
            })
        }
    }

    #[test]
    fn test_escalation_config_defaults() {
        let cfg = EscalationConfig::default();
        assert_eq!(cfg.initial_model, "AI Model-sonnet-4-20250514");
        assert_eq!(cfg.escalation_model, "AI Model-opus-4-20250514");
        assert!(cfg.enabled);
        assert_eq!(cfg.max_escalations, 3);
    }

    #[test]
    fn test_inference_result_has_model_used() {
        let mock = MockInferenceLlm::with_response(
            r#"[{"kind": "precondition", "spec_body": "a > 0", "confidence": 0.9, "rationale": "ok"}]"#,
        );
        let engine = LlmSpecInference::new(&mock, InferenceConfig::default());
        let result = engine.infer(
            "get_midpoint",
            "test::get_midpoint",
            &midpoint_context(),
            &[overflow_failure()],
            1,
        );
        // MockInferenceLlm returns "mock" as model_used
        assert_eq!(result.model_used, "mock");
        assert!(!result.escalated);
    }

    #[test]
    fn test_empty_response_triggers_escalation() {
        let mock = EscalationAwareMock::new(
            "[]", // Sonnet returns empty
            r#"[{"kind": "precondition", "spec_body": "a <= usize::MAX - b", "confidence": 0.9, "rationale": "Overflow guard"}]"#,
        );
        let config = InferenceConfig {
            escalation: EscalationConfig { enabled: true, ..Default::default() },
            ..Default::default()
        };
        let engine = LlmSpecInference::new(&mock, config);
        let result = engine.infer(
            "get_midpoint",
            "test::get_midpoint",
            &midpoint_context(),
            &[overflow_failure()],
            1,
        );
        assert!(result.escalated, "should have escalated");
        assert!(!result.proposals.is_empty(), "should have proposals from escalated model");
        assert!(result.model_used.contains("opus"), "should have used opus");
        assert_eq!(mock.calls(), 2, "should have made 2 backend calls");
    }

    #[test]
    fn test_low_confidence_triggers_escalation() {
        let mock = EscalationAwareMock::new(
            // Sonnet returns low confidence (0.2 < 0.3 min_confidence threshold)
            r#"[{"kind": "precondition", "spec_body": "a > 0", "confidence": 0.2, "rationale": "weak"}]"#,
            // Opus returns high confidence
            r#"[{"kind": "precondition", "spec_body": "a <= usize::MAX - b", "confidence": 0.9, "rationale": "strong"}]"#,
        );
        let config = InferenceConfig {
            min_confidence: 0.3,
            escalation: EscalationConfig { enabled: true, ..Default::default() },
            ..Default::default()
        };
        let engine = LlmSpecInference::new(&mock, config);
        let result = engine.infer(
            "get_midpoint",
            "test::get_midpoint",
            &midpoint_context(),
            &[overflow_failure()],
            1,
        );
        // Low confidence proposals are filtered out, triggering escalation
        assert!(result.escalated);
        assert!(!result.proposals.is_empty());
    }

    #[test]
    fn test_max_escalations_budget_prevents_further_calls() {
        let mock = EscalationAwareMock::new("[]", "[]");
        let config = InferenceConfig {
            escalation: EscalationConfig {
                enabled: true,
                max_escalations: 1,
                ..Default::default()
            },
            ..Default::default()
        };
        let engine = LlmSpecInference::new(&mock, config);

        // First call uses 1 escalation
        let _r1 = engine.infer("f1", "test::f1", &midpoint_context(), &[overflow_failure()], 1);
        assert_eq!(engine.escalation_count(), 1);

        // Second call should NOT escalate (budget exhausted)
        let _r2 = engine.infer("f2", "test::f2", &midpoint_context(), &[overflow_failure()], 1);
        assert_eq!(engine.escalation_count(), 1, "should not have escalated again");
        // First call: 2 backend calls (initial + escalation), second: 1 (initial only)
        assert_eq!(mock.calls(), 3);
    }

    #[test]
    fn test_escalation_disabled_no_escalation() {
        let mock = EscalationAwareMock::new(
            "[]",
            r#"[{"kind": "precondition", "spec_body": "a > 0", "confidence": 0.9, "rationale": "ok"}]"#,
        );
        let config = InferenceConfig {
            escalation: EscalationConfig { enabled: false, ..Default::default() },
            ..Default::default()
        };
        let engine = LlmSpecInference::new(&mock, config);
        let result = engine.infer(
            "get_midpoint",
            "test::get_midpoint",
            &midpoint_context(),
            &[overflow_failure()],
            1,
        );
        assert!(!result.escalated);
        assert!(result.proposals.is_empty(), "should be empty since sonnet returns []");
        assert_eq!(mock.calls(), 1, "should only call once");
    }

    #[test]
    fn test_sonnet_success_no_escalation() {
        let mock = EscalationAwareMock::new(
            r#"[{"kind": "precondition", "spec_body": "a <= usize::MAX - b", "confidence": 0.9, "rationale": "Overflow guard"}]"#,
            "should not be called",
        );
        let config = InferenceConfig {
            escalation: EscalationConfig { enabled: true, ..Default::default() },
            ..Default::default()
        };
        let engine = LlmSpecInference::new(&mock, config);
        let result = engine.infer(
            "get_midpoint",
            "test::get_midpoint",
            &midpoint_context(),
            &[overflow_failure()],
            1,
        );
        assert!(!result.escalated);
        assert!(!result.proposals.is_empty());
        assert_eq!(mock.calls(), 1, "should only call sonnet");
    }
}
