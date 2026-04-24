// trust-strengthen/llm_claude.rs: AI Model API backend for LLM-driven spec inference
//
// Implements LlmBackend by calling the AI Provider Messages API.
// Gated behind the "llm" feature flag (requires reqwest).
//
// Includes retry with exponential backoff and circuit breaker (Phase 2, #602).
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

// Without the "llm" feature, internal helpers (RetryConfig, CircuitBreaker,
// ClaudeConfig, RateLimitInfo, etc.) are only exercised by tests. With "llm"
// enabled, everything is used by the real HTTP codepath. A file-level allow
// avoids duplicating `#[cfg(feature = "llm")]` guards on each item.
#![allow(dead_code)]

use std::sync::Mutex;
use std::time::{Duration, Instant};

use serde::{Deserialize, Serialize};

use crate::analyzer::{FailureAnalysis, FailurePattern};
use crate::proposer::{Proposal, ProposalKind};
use crate::{LlmBackend, LlmError, LlmRequest, LlmResponse};

/// Error type for AI Model API interactions.
#[derive(Debug, thiserror::Error)]
pub enum ClaudeError {
    #[error("API request failed: {0}")]
    Request(String),
    #[error("failed to parse API response: {0}")]
    Parse(String),
    #[error("ANTHROPIC_API_KEY not set")]
    MissingApiKey,
}

// -- Retry configuration --

/// Configuration for exponential backoff retry behavior.
#[derive(Debug, Clone)]
pub struct RetryConfig {
    /// Maximum number of retry attempts (default: 3).
    pub max_retries: u32,
    /// Initial backoff duration in milliseconds (default: 1000).
    pub initial_backoff_ms: u64,
    /// Maximum backoff duration in milliseconds (default: 16000).
    pub max_backoff_ms: u64,
    /// Backoff multiplier applied after each retry (default: 2.0).
    pub backoff_multiplier: f64,
    /// Per-request timeout in seconds (default: 60).
    pub request_timeout_secs: u64,
}

impl Default for RetryConfig {
    fn default() -> Self {
        Self {
            max_retries: 3,
            initial_backoff_ms: 1000,
            max_backoff_ms: 16_000,
            backoff_multiplier: 2.0,
            request_timeout_secs: 60,
        }
    }
}

impl RetryConfig {
    /// Compute the backoff duration for the given attempt (0-indexed).
    ///
    /// Uses exponential backoff with deterministic jitter. The base delay
    /// is `initial_backoff_ms * multiplier^attempt`, capped at `max_backoff_ms`.
    /// A deterministic jitter factor (varying by attempt number) avoids
    /// thundering herd without requiring a `rand` dependency.
    pub(crate) fn backoff_ms(&self, attempt: u32) -> u64 {
        let exp = self.backoff_multiplier.powi(attempt as i32);
        let base = (self.initial_backoff_ms as f64 * exp) as u64;
        let capped = base.min(self.max_backoff_ms);
        // Deterministic jitter: vary by attempt number.
        let jitter_pct = match attempt % 4 {
            0 => 100,
            1 => 75,
            2 => 88,
            3 => 63,
            _ => 100,
        };
        capped * jitter_pct / 100
    }
}

// -- Circuit breaker --

/// Circuit breaker states for the AI Model API backend.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CircuitState {
    /// Normal operation: requests flow through.
    Closed,
    /// Too many failures: all requests are rejected immediately.
    Open,
    /// Cooling down: one probe request is allowed through.
    HalfOpen,
}

/// Circuit breaker that trips after consecutive failures and recovers
/// after a cooldown period.
///
/// Tracks consecutive failures. After `failure_threshold` consecutive
/// failures it transitions to `Open`, rejecting all requests with
/// `LlmError::CircuitBreakerOpen`. After `cooldown` elapses it moves
/// to `HalfOpen` and allows one probe request. If the probe succeeds
/// the breaker resets to `Closed`; if it fails, back to `Open`.
#[derive(Debug)]
pub struct CircuitBreaker {
    state: CircuitState,
    consecutive_failures: u32,
    failure_threshold: u32,
    cooldown: Duration,
    last_failure_time: Option<Instant>,
}

impl CircuitBreaker {
    /// Create a new circuit breaker with the given threshold and cooldown.
    pub fn new(failure_threshold: u32, cooldown: Duration) -> Self {
        Self {
            state: CircuitState::Closed,
            consecutive_failures: 0,
            failure_threshold,
            cooldown,
            last_failure_time: None,
        }
    }

    /// Check whether a request is allowed through the breaker.
    ///
    /// Returns `Ok(())` if allowed, `Err(LlmError::CircuitBreakerOpen)` if not.
    pub fn check(&mut self) -> Result<(), LlmError> {
        match self.state {
            CircuitState::Closed | CircuitState::HalfOpen => Ok(()),
            CircuitState::Open => {
                if let Some(last) = self.last_failure_time
                    && last.elapsed() >= self.cooldown
                {
                    self.state = CircuitState::HalfOpen;
                    return Ok(());
                }
                Err(LlmError::CircuitBreakerOpen { failures: self.consecutive_failures })
            }
        }
    }

    /// Record a successful request. Resets the breaker to `Closed`.
    pub fn record_success(&mut self) {
        self.consecutive_failures = 0;
        self.state = CircuitState::Closed;
        self.last_failure_time = None;
    }

    /// Record a failed request. May trip the breaker to `Open`.
    pub fn record_failure(&mut self) {
        self.consecutive_failures += 1;
        self.last_failure_time = Some(Instant::now());
        if self.consecutive_failures >= self.failure_threshold {
            self.state = CircuitState::Open;
        }
    }

    /// Current state of the breaker.
    pub fn state(&self) -> CircuitState {
        self.state
    }

    /// Number of consecutive failures recorded.
    pub fn consecutive_failures(&self) -> u32 {
        self.consecutive_failures
    }
}

impl Default for CircuitBreaker {
    fn default() -> Self {
        Self::new(5, Duration::from_secs(60))
    }
}

/// Information parsed from AI Provider rate-limit response headers.
#[derive(Debug, Clone, Copy, Default)]
pub(crate) struct RateLimitInfo {
    /// Remaining requests in the current window, if reported.
    pub remaining: Option<u64>,
    /// Seconds until the rate limit window resets, if reported.
    pub reset_secs: Option<u64>,
    /// Retry-after value in seconds from the `retry-after` header.
    pub retry_after_secs: Option<u64>,
}

// -- AI Model config and backend --

/// Configuration for the AI Model LLM backend.
#[derive(Debug, Clone)]
pub struct ClaudeConfig {
    /// AI Provider API key. If None, reads from ANTHROPIC_API_KEY env var.
    pub api_key: Option<String>,
    /// Model to use (default: AI Model-sonnet-4-20250514).
    pub model: String,
    /// Maximum tokens in the response.
    pub max_tokens: u32,
    /// API base URL.
    pub base_url: String,
    /// Whether to use tool_use for structured output (default: true).
    pub use_tool_use: bool,
    /// Retry configuration for transient failures.
    pub retry: RetryConfig,
}

impl Default for ClaudeConfig {
    fn default() -> Self {
        Self {
            api_key: None,
            model: "AI Model-sonnet-4-20250514".into(),
            max_tokens: 1024,
            base_url: "https://api.AI Provider.com".into(),
            use_tool_use: true,
            retry: RetryConfig::default(),
        }
    }
}

/// AI Model API backend for spec inference.
///
/// Sends function source + failure analysis to AI Model and parses
/// structured spec proposals from the response. Includes retry with
/// exponential backoff and circuit breaker protection.
pub struct ClaudeLlm {
    config: ClaudeConfig,
    #[cfg(feature = "llm")]
    client: reqwest::blocking::Client,
    circuit_breaker: Mutex<CircuitBreaker>,
}

impl ClaudeLlm {
    /// Create a new AI Model LLM backend with the given config.
    pub fn new(config: ClaudeConfig) -> Self {
        Self {
            #[cfg(feature = "llm")]
            client: reqwest::blocking::Client::builder()
                .timeout(Duration::from_secs(config.retry.request_timeout_secs))
                .build()
                .expect("failed to build reqwest client"),
            config,
            circuit_breaker: Mutex::new(CircuitBreaker::default()),
        }
    }

    /// Create a new AI Model LLM backend with a custom circuit breaker.
    pub fn with_circuit_breaker(config: ClaudeConfig, circuit_breaker: CircuitBreaker) -> Self {
        Self {
            #[cfg(feature = "llm")]
            client: reqwest::blocking::Client::builder()
                .timeout(Duration::from_secs(config.retry.request_timeout_secs))
                .build()
                .expect("failed to build reqwest client"),
            config,
            circuit_breaker: Mutex::new(circuit_breaker),
        }
    }

    /// Resolve the API key from config or environment.
    fn api_key(&self) -> Result<String, ClaudeError> {
        if let Some(key) = &self.config.api_key {
            Ok(key.clone())
        } else {
            std::env::var("ANTHROPIC_API_KEY").map_err(|_| ClaudeError::MissingApiKey)
        }
    }

    /// Classify an HTTP status code into a retry decision.
    fn classify_status(status: u16) -> RetryDecision {
        if status == 429 {
            RetryDecision::RetryRateLimited
        } else if status >= 500 {
            RetryDecision::RetryServerError { status }
        } else if status >= 400 {
            RetryDecision::Fail
        } else {
            RetryDecision::Success
        }
    }
}

/// Internal retry classification for HTTP responses.
enum RetryDecision {
    Success,
    RetryRateLimited,
    RetryServerError { status: u16 },
    Fail,
}

/// Parse rate-limit information from HTTP response headers.
#[cfg(feature = "llm")]
fn parse_rate_limit_headers(headers: &reqwest::header::HeaderMap) -> RateLimitInfo {
    let parse_header = |name: &str| -> Option<u64> {
        headers.get(name).and_then(|v| v.to_str().ok()).and_then(|s| s.parse::<u64>().ok())
    };
    RateLimitInfo {
        remaining: parse_header("x-ratelimit-limit-requests")
            .or_else(|| parse_header("x-ratelimit-remaining-requests")),
        reset_secs: parse_header("x-ratelimit-reset-requests")
            .or_else(|| parse_header("AI Provider-ratelimit-requests-reset")),
        retry_after_secs: parse_header("retry-after"),
    }
}

/// Build the prompt for spec inference from failures.
pub(crate) fn build_prompt(
    function_name: &str,
    source: &str,
    failures: &[FailureAnalysis],
) -> String {
    let failure_descriptions: Vec<String> = failures.iter().map(format_failure).collect();

    format!(
        r#"You are a formal verification expert. Analyze this Rust function and its verification failures, then propose specifications (preconditions, postconditions, or invariants) that would make the function provable.

## Function: `{function_name}`

```rust
{source}
```

## Verification Failures

{failures_text}

## Instructions

Propose specifications as JSON. Each proposal should be one of:
- `precondition`: An expression for `#[requires("...")]`
- `postcondition`: An expression for `#[ensures("...")]`
- `invariant`: An expression for `#[invariant("...")]`

Respond with ONLY a JSON array of proposals. Each proposal has:
- `kind`: one of "precondition", "postcondition", "invariant"
- `spec_body`: the specification expression as a string
- `confidence`: a number from 0.0 to 1.0
- `rationale`: a brief explanation

Example:
```json
[
  {{
    "kind": "precondition",
    "spec_body": "a <= u64::MAX - b",
    "confidence": 0.9,
    "rationale": "Prevents addition overflow"
  }}
]
```"#,
        function_name = function_name,
        source = source,
        failures_text = failure_descriptions.join("\n"),
    )
}

/// Format a single failure analysis for the prompt.
fn format_failure(analysis: &FailureAnalysis) -> String {
    let pattern_desc = match &analysis.pattern {
        FailurePattern::ArithmeticOverflow { op } => {
            format!("Arithmetic overflow ({op:?})")
        }
        FailurePattern::DivisionByZero => "Division by zero".into(),
        FailurePattern::IndexOutOfBounds => "Index out of bounds".into(),
        FailurePattern::CastOverflow => "Cast overflow".into(),
        FailurePattern::NegationOverflow => "Negation overflow".into(),
        FailurePattern::ShiftOverflow => "Shift overflow".into(),
        FailurePattern::AssertionFailure { message } => {
            format!("Assertion failure: {message}")
        }
        FailurePattern::PreconditionViolation { callee } => {
            format!("Precondition violation on call to {callee}")
        }
        FailurePattern::PostconditionViolation => "Postcondition violation".into(),
        FailurePattern::UnreachableReached => "Unreachable code reached".into(),
        FailurePattern::Temporal => "Temporal property violation".into(),
        FailurePattern::Unknown => "Unknown failure".into(),
    };
    let solver = analysis.solver.as_deref().unwrap_or("unknown");
    format!("- **{pattern_desc}** in `{}` (solver: {solver})", analysis.function)
}

// -- Tool use types for structured output (Phase 4, #610) --

/// Schema for a single proposal in the `propose_specifications` tool input.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct ToolProposalSchema {
    pub kind: String,
    pub spec_body: String,
    pub confidence: f64,
    pub rationale: String,
}

/// The input payload for the `propose_specifications` tool.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct ToolUseInput {
    pub proposals: Vec<ToolProposalSchema>,
}

/// A tool definition sent in the API request.
#[derive(Debug, Serialize)]
struct ToolDefinition {
    name: String,
    description: String,
    input_schema: serde_json::Value,
}

/// Tool choice mode for the API request.
#[derive(Debug, Serialize)]
struct ToolChoice {
    #[serde(rename = "type")]
    choice_type: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    name: Option<String>,
}

/// Build the `propose_specifications` tool definition for the AI Model API.
pub(crate) fn build_tool_definition() -> serde_json::Value {
    serde_json::json!({
        "name": "propose_specifications",
        "description": "Propose formal verification specifications (preconditions, postconditions, invariants) for a Rust function based on analysis of verification failures.",
        "input_schema": {
            "type": "object",
            "properties": {
                "proposals": {
                    "type": "array",
                    "description": "List of specification proposals",
                    "items": {
                        "type": "object",
                        "properties": {
                            "kind": {
                                "type": "string",
                                "enum": ["precondition", "postcondition", "invariant"],
                                "description": "Type of specification"
                            },
                            "spec_body": {
                                "type": "string",
                                "description": "The specification expression (e.g. for #[requires(\"...\")])"
                            },
                            "confidence": {
                                "type": "number",
                                "minimum": 0.0,
                                "maximum": 1.0,
                                "description": "Confidence score from 0.0 to 1.0"
                            },
                            "rationale": {
                                "type": "string",
                                "description": "Brief explanation of why this specification is needed"
                            }
                        },
                        "required": ["kind", "spec_body", "confidence", "rationale"]
                    }
                }
            },
            "required": ["proposals"]
        }
    })
}

/// Parse a tool_use response into Proposal structs.
///
/// When the model returns a `tool_use` content block for `propose_specifications`,
/// the input is already structured JSON matching `ToolUseInput`. This avoids
/// the fragile free-form JSON extraction used by `parse_llm_response`.
pub(crate) fn parse_tool_use_response(
    input_json: &str,
    function_name: &str,
    function_path: &str,
) -> Vec<Proposal> {
    let input: ToolUseInput = match serde_json::from_str(input_json) {
        Ok(i) => i,
        Err(_) => return vec![],
    };

    input
        .proposals
        .into_iter()
        .filter_map(|p| {
            convert_llm_proposal(
                LlmProposal {
                    kind: p.kind,
                    spec_body: p.spec_body,
                    confidence: p.confidence,
                    rationale: p.rationale,
                },
                function_name,
                function_path,
            )
        })
        .collect()
}

// -- API request/response types --

#[derive(Serialize)]
struct MessagesRequest {
    model: String,
    max_tokens: u32,
    messages: Vec<Message>,
    #[serde(skip_serializing_if = "Option::is_none")]
    tools: Option<Vec<serde_json::Value>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    tool_choice: Option<serde_json::Value>,
}

#[derive(Serialize)]
struct Message {
    role: String,
    content: String,
}

#[derive(Deserialize)]
struct MessagesResponse {
    content: Vec<ContentBlock>,
}

/// Content block from the AI Model API, supporting both text and tool_use responses.
#[derive(Debug, Deserialize)]
#[serde(tag = "type")]
enum ContentBlock {
    #[serde(rename = "text")]
    Text { text: String },
    #[serde(rename = "tool_use")]
    ToolUse { id: String, name: String, input: serde_json::Value },
}

/// A single proposal as returned by AI Model's JSON response.
#[derive(Debug, Deserialize)]
pub(crate) struct LlmProposal {
    pub kind: String,
    pub spec_body: String,
    pub confidence: f64,
    pub rationale: String,
}

/// Parse AI Model's JSON response into Proposal structs.
pub(crate) fn parse_llm_response(
    response_text: &str,
    function_name: &str,
    function_path: &str,
) -> Vec<Proposal> {
    let json_text = extract_json_array(response_text);

    let proposals: Vec<LlmProposal> = match serde_json::from_str(&json_text) {
        Ok(p) => p,
        Err(_) => return vec![],
    };

    proposals
        .into_iter()
        .filter_map(|p| convert_llm_proposal(p, function_name, function_path))
        .collect()
}

/// Extract a JSON array from text that may contain markdown code fences.
fn extract_json_array(text: &str) -> String {
    if let Some(start) = text.find("```json") {
        let after_fence = &text[start + 7..];
        if let Some(end) = after_fence.find("```") {
            return after_fence[..end].trim().to_string();
        }
    }
    if let Some(start) = text.find("```") {
        let after_fence = &text[start + 3..];
        if let Some(end) = after_fence.find("```") {
            let inner = after_fence[..end].trim();
            if inner.starts_with('[') {
                return inner.to_string();
            }
        }
    }
    let trimmed = text.trim();
    if trimmed.starts_with('[') {
        return trimmed.to_string();
    }
    if let (Some(start), Some(end)) = (text.find('['), text.rfind(']'))
        && start < end
    {
        return text[start..=end].to_string();
    }
    text.to_string()
}

/// Convert an LlmProposal to a typed Proposal.
fn convert_llm_proposal(
    p: LlmProposal,
    function_name: &str,
    function_path: &str,
) -> Option<Proposal> {
    let kind = match p.kind.as_str() {
        "precondition" => ProposalKind::AddPrecondition { spec_body: p.spec_body },
        "postcondition" => ProposalKind::AddPostcondition { spec_body: p.spec_body },
        "invariant" => ProposalKind::AddInvariant { spec_body: p.spec_body },
        _ => return None,
    };

    Some(Proposal {
        function_path: function_path.into(),
        function_name: function_name.into(),
        kind,
        confidence: p.confidence.clamp(0.0, 1.0),
        rationale: p.rationale,
    })
}

impl LlmBackend for ClaudeLlm {
    fn send(&self, request: &LlmRequest) -> Result<LlmResponse, LlmError> {
        // Check circuit breaker before attempting any request.
        {
            let mut cb = self.circuit_breaker.lock().expect("circuit breaker lock poisoned");
            cb.check()?;
        }

        #[cfg(feature = "llm")]
        {
            let api_key = self.api_key().map_err(|_| LlmError::MissingApiKey)?;

            let model = if request.model.is_empty() {
                self.config.model.clone()
            } else {
                request.model.clone()
            };

            let max_tokens = if request.max_response_tokens > 0 {
                request.max_response_tokens
            } else {
                self.config.max_tokens
            };

            // Include tool definitions when tool_use is requested.
            let use_tools = request.use_tool_use && self.config.use_tool_use;
            let (tools, tool_choice) = if use_tools {
                (
                    Some(vec![build_tool_definition()]),
                    Some(serde_json::json!({
                        "type": "tool",
                        "name": "propose_specifications",
                    })),
                )
            } else {
                (None, None)
            };

            // Apply token budget: truncate prompt if it exceeds the model's
            // context window minus reserved response tokens.
            let budget = crate::llm_token_budget::TokenBudget::new(
                200_000, // AI Model Sonnet context window
                max_tokens as usize,
            );
            let prompt = if crate::llm_token_budget::estimate_tokens(&request.prompt)
                > budget.max_prompt_tokens
            {
                // Treat the entire prompt as a single FunctionBody-priority section
                // for truncation. Callers that want finer-grained priority control
                // should use `truncate_to_budget` directly before calling `send()`.
                crate::llm_token_budget::truncate_to_budget(
                    vec![(crate::llm_token_budget::Priority::FunctionBody, request.prompt.clone())],
                    &budget,
                )
            } else {
                request.prompt.clone()
            };

            let msg_request = MessagesRequest {
                model: model.clone(),
                max_tokens,
                messages: vec![Message { role: "user".into(), content: prompt }],
                tools,
                tool_choice,
            };

            let url = format!("{}/v1/messages", self.config.base_url);
            let retry_config = &self.config.retry;
            let mut last_err: Option<LlmError> = None;

            for attempt in 0..=retry_config.max_retries {
                if attempt > 0 {
                    let backoff = retry_config.backoff_ms(attempt - 1);
                    eprintln!(
                        "[trust-strengthen] retry {attempt}/{} after {backoff}ms backoff",
                        retry_config.max_retries,
                    );
                    std::thread::sleep(Duration::from_millis(backoff));
                }

                let send_result = self
                    .client
                    .post(&url)
                    .header("x-api-key", &api_key)
                    .header("AI Provider-version", "2023-06-01")
                    .header("content-type", "application/json")
                    .json(&msg_request)
                    .send();

                let response = match send_result {
                    Ok(r) => r,
                    Err(e) => {
                        let is_timeout = e.is_timeout();
                        let err = if is_timeout {
                            LlmError::Timeout { timeout_secs: retry_config.request_timeout_secs }
                        } else {
                            LlmError::Request(e.to_string())
                        };
                        let mut cb =
                            self.circuit_breaker.lock().expect("circuit breaker lock poisoned");
                        cb.record_failure();
                        last_err = Some(err);
                        continue;
                    }
                };

                let status = response.status().as_u16();
                match Self::classify_status(status) {
                    RetryDecision::Success => {
                        let mut cb =
                            self.circuit_breaker.lock().expect("circuit breaker lock poisoned");
                        cb.record_success();

                        let body: MessagesResponse = response.json().map_err(|e| {
                            LlmError::Request(format!("failed to parse response: {e}"))
                        })?;

                        // Check for tool_use blocks first (structured output).
                        // If the model used the propose_specifications tool,
                        // serialize the input as JSON for downstream parsing.
                        let mut tool_use_json: Option<String> = None;
                        let mut text_parts: Vec<String> = Vec::new();

                        for block in body.content {
                            match block {
                                ContentBlock::ToolUse { name, input, .. }
                                    if name == "propose_specifications" =>
                                {
                                    tool_use_json =
                                        Some(serde_json::to_string(&input).unwrap_or_default());
                                }
                                ContentBlock::Text { text } => {
                                    text_parts.push(text);
                                }
                                // Ignore tool_use blocks for unknown tools.
                                ContentBlock::ToolUse { .. } => {}
                            }
                        }

                        if let Some(json) = tool_use_json {
                            return Ok(LlmResponse {
                                content: json,
                                used_tool_use: true,
                                model_used: model,
                            });
                        }

                        // Fallback: plain text response.
                        return Ok(LlmResponse {
                            content: text_parts.join("\n"),
                            used_tool_use: false,
                            model_used: model,
                        });
                    }
                    RetryDecision::RetryRateLimited => {
                        let rate_info = parse_rate_limit_headers(response.headers());
                        let wait_ms = rate_info
                            .retry_after_secs
                            .map(|s| s * 1000)
                            .unwrap_or_else(|| retry_config.backoff_ms(attempt));
                        eprintln!(
                            "[trust-strengthen] rate limited (429), waiting {wait_ms}ms \
                             (remaining: {remaining:?}, reset: {reset:?}s)",
                            remaining = rate_info.remaining,
                            reset = rate_info.reset_secs,
                        );
                        std::thread::sleep(Duration::from_millis(wait_ms));
                        let mut cb =
                            self.circuit_breaker.lock().expect("circuit breaker lock poisoned");
                        cb.record_failure();
                        last_err = Some(LlmError::RateLimited { retry_after_ms: wait_ms });
                    }
                    RetryDecision::RetryServerError { status } => {
                        let mut cb =
                            self.circuit_breaker.lock().expect("circuit breaker lock poisoned");
                        cb.record_failure();
                        eprintln!("[trust-strengthen] server error (HTTP {status}), will retry");
                        last_err = Some(LlmError::ServerError { status });
                    }
                    RetryDecision::Fail => {
                        let mut cb =
                            self.circuit_breaker.lock().expect("circuit breaker lock poisoned");
                        cb.record_failure();
                        return Err(LlmError::Request(format!("HTTP {status}")));
                    }
                }
            }

            Err(last_err.unwrap_or_else(|| {
                LlmError::Request("exhausted retries with no error recorded".into())
            }))
        }

        #[cfg(not(feature = "llm"))]
        {
            let _ = request;
            Err(LlmError::Request("llm feature not enabled".into()))
        }
    }
}

#[cfg(test)]
mod tests {
    use trust_types::{BinOp, Ty, VcKind};

    use super::*;
    use crate::analyzer::{FailureAnalysis, FailurePattern};

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

    fn div_zero_failure() -> FailureAnalysis {
        FailureAnalysis {
            vc_kind: VcKind::DivisionByZero,
            function: "safe_divide".into(),
            pattern: FailurePattern::DivisionByZero,
            solver: Some("z4".into()),
        }
    }

    // -- Prompt generation tests --

    #[test]
    fn test_build_prompt_contains_function_name() {
        let prompt = build_prompt(
            "get_midpoint",
            "fn get_midpoint(a: u64, b: u64) -> u64 { a + b }",
            &[overflow_failure()],
        );
        assert!(prompt.contains("get_midpoint"));
        assert!(prompt.contains("fn get_midpoint"));
        assert!(prompt.contains("Arithmetic overflow"));
    }

    #[test]
    fn test_build_prompt_contains_failure_info() {
        let prompt = build_prompt(
            "safe_divide",
            "fn safe_divide(a: u64, b: u64) -> u64 { a / b }",
            &[div_zero_failure()],
        );
        assert!(prompt.contains("Division by zero"));
        assert!(prompt.contains("z4"));
    }

    #[test]
    fn test_build_prompt_multiple_failures() {
        let failures = vec![overflow_failure(), div_zero_failure()];
        let prompt = build_prompt("compute", "fn compute() {}", &failures);
        assert!(prompt.contains("Arithmetic overflow"));
        assert!(prompt.contains("Division by zero"));
    }

    #[test]
    fn test_build_prompt_contains_json_instructions() {
        let prompt = build_prompt("f", "fn f() {}", &[overflow_failure()]);
        assert!(prompt.contains("JSON"));
        assert!(prompt.contains("precondition"));
        assert!(prompt.contains("postcondition"));
        assert!(prompt.contains("invariant"));
    }

    // -- JSON parsing tests --

    #[test]
    fn test_parse_valid_json_precondition() {
        let json = r#"[
            {
                "kind": "precondition",
                "spec_body": "a <= u64::MAX - b",
                "confidence": 0.9,
                "rationale": "Prevents addition overflow"
            }
        ]"#;
        let proposals = parse_llm_response(json, "get_midpoint", "test::get_midpoint");
        assert_eq!(proposals.len(), 1);
        assert_eq!(proposals[0].function_name, "get_midpoint");
        assert_eq!(proposals[0].function_path, "test::get_midpoint");
        assert!(
            matches!(&proposals[0].kind, ProposalKind::AddPrecondition { spec_body } if spec_body == "a <= u64::MAX - b")
        );
        assert!((proposals[0].confidence - 0.9).abs() < f64::EPSILON);
        assert_eq!(proposals[0].rationale, "Prevents addition overflow");
    }

    #[test]
    fn test_parse_valid_json_postcondition() {
        let json = r#"[{"kind": "postcondition", "spec_body": "result >= a && result >= b", "confidence": 0.8, "rationale": "Max returns the larger value"}]"#;
        let proposals = parse_llm_response(json, "max", "test::max");
        assert_eq!(proposals.len(), 1);
        assert!(
            matches!(&proposals[0].kind, ProposalKind::AddPostcondition { spec_body } if spec_body == "result >= a && result >= b")
        );
    }

    #[test]
    fn test_parse_valid_json_invariant() {
        let json = r#"[{"kind": "invariant", "spec_body": "i < len", "confidence": 0.85, "rationale": "Loop index stays in bounds"}]"#;
        let proposals = parse_llm_response(json, "search", "test::search");
        assert_eq!(proposals.len(), 1);
        assert!(
            matches!(&proposals[0].kind, ProposalKind::AddInvariant { spec_body } if spec_body == "i < len")
        );
    }

    #[test]
    fn test_parse_multiple_proposals() {
        let json = r#"[
            {"kind": "precondition", "spec_body": "b != 0", "confidence": 0.95, "rationale": "Divisor must be non-zero"},
            {"kind": "postcondition", "spec_body": "result * b + a % b == a", "confidence": 0.7, "rationale": "Division identity"}
        ]"#;
        let proposals = parse_llm_response(json, "divide", "test::divide");
        assert_eq!(proposals.len(), 2);
        assert!(matches!(&proposals[0].kind, ProposalKind::AddPrecondition { .. }));
        assert!(matches!(&proposals[1].kind, ProposalKind::AddPostcondition { .. }));
    }

    #[test]
    fn test_parse_json_in_markdown_fences() {
        let response = "Here's the analysis:\n\n```json\n[{\"kind\": \"precondition\", \"spec_body\": \"x > 0\", \"confidence\": 0.9, \"rationale\": \"Must be positive\"}]\n```\n\nThis ensures safety.";
        let proposals = parse_llm_response(response, "f", "test::f");
        assert_eq!(proposals.len(), 1);
        assert!(
            matches!(&proposals[0].kind, ProposalKind::AddPrecondition { spec_body } if spec_body == "x > 0")
        );
    }

    #[test]
    fn test_parse_json_in_plain_fences() {
        let response = "```\n[{\"kind\": \"precondition\", \"spec_body\": \"n < 64\", \"confidence\": 0.85, \"rationale\": \"Shift bounds\"}]\n```";
        let proposals = parse_llm_response(response, "shift", "test::shift");
        assert_eq!(proposals.len(), 1);
    }

    #[test]
    fn test_parse_invalid_json_returns_empty() {
        let proposals = parse_llm_response("not json at all", "f", "test::f");
        assert!(proposals.is_empty());
    }

    #[test]
    fn test_parse_empty_array() {
        let proposals = parse_llm_response("[]", "f", "test::f");
        assert!(proposals.is_empty());
    }

    #[test]
    fn test_parse_unknown_kind_filtered() {
        let json = r#"[
            {"kind": "precondition", "spec_body": "x > 0", "confidence": 0.9, "rationale": "ok"},
            {"kind": "magic_spell", "spec_body": "abracadabra", "confidence": 0.1, "rationale": "not a real kind"}
        ]"#;
        let proposals = parse_llm_response(json, "f", "test::f");
        assert_eq!(proposals.len(), 1);
        assert!(matches!(&proposals[0].kind, ProposalKind::AddPrecondition { .. }));
    }

    #[test]
    fn test_parse_confidence_clamped() {
        let json = r#"[{"kind": "precondition", "spec_body": "x > 0", "confidence": 1.5, "rationale": "over-confident"}]"#;
        let proposals = parse_llm_response(json, "f", "test::f");
        assert_eq!(proposals.len(), 1);
        assert!((proposals[0].confidence - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_parse_negative_confidence_clamped() {
        let json = r#"[{"kind": "postcondition", "spec_body": "result > 0", "confidence": -0.5, "rationale": "negative"}]"#;
        let proposals = parse_llm_response(json, "f", "test::f");
        assert_eq!(proposals.len(), 1);
        assert!(proposals[0].confidence.abs() < f64::EPSILON);
    }

    // -- extract_json_array tests --

    #[test]
    fn test_extract_raw_array() {
        assert_eq!(extract_json_array("[1,2,3]"), "[1,2,3]");
    }

    #[test]
    fn test_extract_from_markdown_fence() {
        let text = "Here:\n```json\n[1]\n```\nDone.";
        assert_eq!(extract_json_array(text), "[1]");
    }

    #[test]
    fn test_extract_bracket_fallback() {
        let text = "The answer is [1, 2] in this context";
        assert_eq!(extract_json_array(text), "[1, 2]");
    }

    // -- ClaudeLlm unit tests (no network) --

    #[test]
    fn test_claude_llm_send_without_llm_feature() {
        let llm = ClaudeLlm::new(ClaudeConfig::default());
        let request = crate::LlmRequest {
            prompt: "test".into(),
            model: String::new(),
            max_response_tokens: 1024,
            use_tool_use: false,
        };
        let result = llm.send(&request);
        assert!(result.is_err());
    }

    #[test]
    fn test_claude_config_defaults() {
        let config = ClaudeConfig::default();
        assert_eq!(config.model, "AI Model-sonnet-4-20250514");
        assert_eq!(config.max_tokens, 1024);
        assert_eq!(config.base_url, "https://api.AI Provider.com");
        assert!(config.api_key.is_none());
        assert_eq!(config.retry.max_retries, 3);
        assert_eq!(config.retry.initial_backoff_ms, 1000);
        assert_eq!(config.retry.max_backoff_ms, 16_000);
    }

    #[test]
    fn test_api_key_from_config() {
        let config = ClaudeConfig { api_key: Some("test-key-123".into()), ..Default::default() };
        let llm = ClaudeLlm::new(config);
        assert_eq!(llm.api_key().expect("should have key"), "test-key-123");
    }

    // -- RetryConfig tests --

    #[test]
    fn test_retry_config_defaults() {
        let rc = RetryConfig::default();
        assert_eq!(rc.max_retries, 3);
        assert_eq!(rc.initial_backoff_ms, 1000);
        assert_eq!(rc.max_backoff_ms, 16_000);
        assert!((rc.backoff_multiplier - 2.0).abs() < f64::EPSILON);
        assert_eq!(rc.request_timeout_secs, 60);
    }

    #[test]
    fn test_backoff_exponential_growth() {
        let rc = RetryConfig {
            initial_backoff_ms: 1000,
            max_backoff_ms: 60_000,
            backoff_multiplier: 2.0,
            ..Default::default()
        };
        assert_eq!(rc.backoff_ms(0), 1000);
        assert_eq!(rc.backoff_ms(1), 1500);
        assert_eq!(rc.backoff_ms(2), 3520);
        assert_eq!(rc.backoff_ms(3), 5040);
    }

    #[test]
    fn test_backoff_capped_at_max() {
        let rc = RetryConfig {
            initial_backoff_ms: 1000,
            max_backoff_ms: 3000,
            backoff_multiplier: 2.0,
            ..Default::default()
        };
        assert_eq!(rc.backoff_ms(2), 2640);
        assert_eq!(rc.backoff_ms(5), 2250);
    }

    #[test]
    fn test_backoff_jitter_varies_by_attempt() {
        let rc = RetryConfig::default();
        let b0 = rc.backoff_ms(0);
        let b1 = rc.backoff_ms(1);
        assert_ne!(b0, b1);
    }

    // -- CircuitBreaker tests --

    #[test]
    fn test_circuit_breaker_starts_closed() {
        let cb = CircuitBreaker::default();
        assert_eq!(cb.state(), CircuitState::Closed);
        assert_eq!(cb.consecutive_failures(), 0);
    }

    #[test]
    fn test_circuit_breaker_allows_requests_when_closed() {
        let mut cb = CircuitBreaker::default();
        assert!(cb.check().is_ok());
    }

    #[test]
    fn test_circuit_breaker_trips_after_threshold() {
        let mut cb = CircuitBreaker::new(3, Duration::from_secs(60));
        cb.record_failure();
        assert_eq!(cb.state(), CircuitState::Closed);
        cb.record_failure();
        assert_eq!(cb.state(), CircuitState::Closed);
        cb.record_failure();
        assert_eq!(cb.state(), CircuitState::Open);
        assert_eq!(cb.consecutive_failures(), 3);
    }

    #[test]
    fn test_circuit_breaker_rejects_when_open() {
        let mut cb = CircuitBreaker::new(2, Duration::from_secs(300));
        cb.record_failure();
        cb.record_failure();
        assert_eq!(cb.state(), CircuitState::Open);
        let err = cb.check().unwrap_err();
        assert!(
            matches!(err, LlmError::CircuitBreakerOpen { failures: 2 }),
            "expected CircuitBreakerOpen with 2 failures, got {err:?}"
        );
    }

    #[test]
    fn test_circuit_breaker_resets_on_success() {
        let mut cb = CircuitBreaker::new(3, Duration::from_secs(60));
        cb.record_failure();
        cb.record_failure();
        assert_eq!(cb.consecutive_failures(), 2);
        cb.record_success();
        assert_eq!(cb.state(), CircuitState::Closed);
        assert_eq!(cb.consecutive_failures(), 0);
    }

    #[test]
    fn test_circuit_breaker_half_open_on_success_resets() {
        let mut cb = CircuitBreaker::new(2, Duration::from_millis(1));
        cb.record_failure();
        cb.record_failure();
        assert_eq!(cb.state(), CircuitState::Open);
        std::thread::sleep(Duration::from_millis(5));
        assert!(cb.check().is_ok());
        assert_eq!(cb.state(), CircuitState::HalfOpen);
        cb.record_success();
        assert_eq!(cb.state(), CircuitState::Closed);
        assert_eq!(cb.consecutive_failures(), 0);
    }

    #[test]
    fn test_circuit_breaker_half_open_on_failure_reopens() {
        let mut cb = CircuitBreaker::new(2, Duration::from_millis(1));
        cb.record_failure();
        cb.record_failure();
        assert_eq!(cb.state(), CircuitState::Open);
        std::thread::sleep(Duration::from_millis(5));
        assert!(cb.check().is_ok());
        assert_eq!(cb.state(), CircuitState::HalfOpen);
        cb.record_failure();
        assert_eq!(cb.state(), CircuitState::Open);
    }

    #[test]
    fn test_circuit_breaker_open_before_cooldown() {
        let mut cb = CircuitBreaker::new(1, Duration::from_secs(300));
        cb.record_failure();
        assert_eq!(cb.state(), CircuitState::Open);
        assert!(cb.check().is_err());
    }

    #[test]
    fn test_circuit_breaker_failures_accumulate_below_threshold() {
        let mut cb = CircuitBreaker::new(5, Duration::from_secs(60));
        for i in 1..5 {
            cb.record_failure();
            assert_eq!(cb.consecutive_failures(), i);
            assert_eq!(cb.state(), CircuitState::Closed);
        }
        cb.record_failure();
        assert_eq!(cb.state(), CircuitState::Open);
    }

    // -- Status classification tests --

    #[test]
    fn test_classify_status_200() {
        assert!(matches!(ClaudeLlm::classify_status(200), RetryDecision::Success));
    }

    #[test]
    fn test_classify_status_429() {
        assert!(matches!(ClaudeLlm::classify_status(429), RetryDecision::RetryRateLimited));
    }

    #[test]
    fn test_classify_status_500() {
        assert!(matches!(
            ClaudeLlm::classify_status(500),
            RetryDecision::RetryServerError { status: 500 }
        ));
    }

    #[test]
    fn test_classify_status_503() {
        assert!(matches!(
            ClaudeLlm::classify_status(503),
            RetryDecision::RetryServerError { status: 503 }
        ));
    }

    #[test]
    fn test_classify_status_400() {
        assert!(matches!(ClaudeLlm::classify_status(400), RetryDecision::Fail));
    }

    #[test]
    fn test_classify_status_401() {
        assert!(matches!(ClaudeLlm::classify_status(401), RetryDecision::Fail));
    }

    // -- Format failure tests --

    #[test]
    fn test_format_failure_overflow() {
        let desc = format_failure(&overflow_failure());
        assert!(desc.contains("Arithmetic overflow"));
        assert!(desc.contains("get_midpoint"));
        assert!(desc.contains("z4"));
    }

    #[test]
    fn test_format_failure_div_zero() {
        let desc = format_failure(&div_zero_failure());
        assert!(desc.contains("Division by zero"));
    }

    #[test]
    fn test_format_failure_no_solver() {
        let analysis = FailureAnalysis {
            vc_kind: VcKind::IndexOutOfBounds,
            function: "get".into(),
            pattern: FailurePattern::IndexOutOfBounds,
            solver: None,
        };
        let desc = format_failure(&analysis);
        assert!(desc.contains("unknown"));
    }

    // -- RateLimitInfo tests --

    #[test]
    fn test_rate_limit_info_default() {
        let info = RateLimitInfo::default();
        assert!(info.remaining.is_none());
        assert!(info.reset_secs.is_none());
        assert!(info.retry_after_secs.is_none());
    }

    // -- MockLlm for integration-style tests --

    struct MockClaudeLlm {
        response: String,
    }

    impl LlmBackend for MockClaudeLlm {
        fn send(
            &self,
            _request: &crate::LlmRequest,
        ) -> Result<crate::LlmResponse, crate::LlmError> {
            Ok(crate::LlmResponse {
                content: self.response.clone(),
                used_tool_use: false,
                model_used: "mock".into(),
            })
        }
    }

    #[test]
    fn test_mock_llm_integration() {
        let mock = MockClaudeLlm {
            response: r#"[
                {"kind": "precondition", "spec_body": "a <= u64::MAX - b", "confidence": 0.9, "rationale": "Overflow guard"},
                {"kind": "postcondition", "spec_body": "result == (a + b) / 2", "confidence": 0.85, "rationale": "Midpoint definition"}
            ]"#.into(),
        };
        let response = mock
            .send(&crate::LlmRequest {
                prompt: "test".into(),
                model: String::new(),
                max_response_tokens: 1024,
                use_tool_use: false,
            })
            .expect("mock should not fail");
        let proposals = parse_llm_response(&response.content, "get_midpoint", "get_midpoint");
        assert_eq!(proposals.len(), 2);
        assert!(
            matches!(&proposals[0].kind, ProposalKind::AddPrecondition { spec_body } if spec_body == "a <= u64::MAX - b")
        );
        assert!(
            matches!(&proposals[1].kind, ProposalKind::AddPostcondition { spec_body } if spec_body == "result == (a + b) / 2")
        );
    }

    #[test]
    fn test_mock_llm_bad_response() {
        let mock = MockClaudeLlm { response: "I don't understand the question.".into() };
        let response = mock
            .send(&crate::LlmRequest {
                prompt: "test".into(),
                model: String::new(),
                max_response_tokens: 1024,
                use_tool_use: false,
            })
            .expect("mock should not fail");
        let proposals = parse_llm_response(&response.content, "f", "f");
        assert!(proposals.is_empty());
    }

    #[test]
    fn test_mock_llm_partial_valid() {
        let mock = MockClaudeLlm {
            response: r#"[
                {"kind": "precondition", "spec_body": "x > 0", "confidence": 0.9, "rationale": "Valid"},
                {"kind": "teleport", "spec_body": "beam me up", "confidence": 0.1, "rationale": "Invalid kind"}
            ]"#.into(),
        };
        let response = mock
            .send(&crate::LlmRequest {
                prompt: "test".into(),
                model: String::new(),
                max_response_tokens: 1024,
                use_tool_use: false,
            })
            .expect("mock should not fail");
        let proposals = parse_llm_response(&response.content, "f", "f");
        assert_eq!(proposals.len(), 1);
    }

    // -- Full pipeline test with mock --

    #[test]
    fn test_strengthen_with_mock_llm() {
        use trust_types::{
            CrateVerificationResult, Formula, FunctionVerificationResult, SourceSpan,
            VerificationCondition, VerificationResult,
        };
        let mock = MockClaudeLlm {
            response: r#"[{"kind": "precondition", "spec_body": "a <= u64::MAX - b", "confidence": 0.9, "rationale": "LLM overflow guard"}]"#.into(),
        };
        let vc = VerificationCondition {
            kind: VcKind::ArithmeticOverflow {
                op: BinOp::Add,
                operand_tys: (
                    Ty::Int { width: 64, signed: false },
                    Ty::Int { width: 64, signed: false },
                ),
            },
            function: "get_midpoint".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        };
        let results = CrateVerificationResult {
            crate_name: "test".into(),
            functions: vec![FunctionVerificationResult {
                function_path: "test::get_midpoint".into(),
                function_name: "get_midpoint".into(),
                results: vec![(
                    vc,
                    VerificationResult::Failed {
                        solver: "z4".into(),
                        time_ms: 1,
                        counterexample: None,
                    },
                )],
                from_notes: 0,
                with_assumptions: 0,
            }],
            total_from_notes: 0,
            total_with_assumptions: 0,
        };
        let config = crate::StrengthenConfig { use_llm: true, ..Default::default() };
        let output = crate::run(&results, &config, &mock);
        assert!(output.has_proposals);
        assert!(output.proposals.len() >= 3);
        let llm_proposal = output.proposals.iter().find(|p| {
            matches!(&p.kind, ProposalKind::AddPrecondition { spec_body } if spec_body == "a <= u64::MAX - b")
        });
        assert!(llm_proposal.is_some(), "LLM proposal should be present");
    }

    // -- NoOpLlm tests --

    #[test]
    fn test_noop_llm_returns_empty_response() {
        let noop = crate::NoOpLlm;
        let request = crate::LlmRequest {
            prompt: "test prompt".into(),
            model: String::new(),
            max_response_tokens: 1024,
            use_tool_use: false,
        };
        let response = noop.send(&request).expect("NoOpLlm should never fail");
        assert_eq!(response.content, "[]");
        assert!(!response.used_tool_use);
        assert_eq!(response.model_used, "none");
    }

    // -- Phase 4: tool_use structured output tests (#610) --

    #[test]
    fn test_build_tool_definition_has_required_fields() {
        let tool = build_tool_definition();
        assert_eq!(tool["name"], "propose_specifications");
        assert!(tool["description"].as_str().unwrap().contains("verification"));
        let schema = &tool["input_schema"];
        assert_eq!(schema["type"], "object");
        let props = &schema["properties"]["proposals"]["items"]["properties"];
        assert!(props["kind"].is_object());
        assert!(props["spec_body"].is_object());
        assert!(props["confidence"].is_object());
        assert!(props["rationale"].is_object());
    }

    #[test]
    fn test_build_tool_definition_kind_enum() {
        let tool = build_tool_definition();
        let kind_enum =
            &tool["input_schema"]["properties"]["proposals"]["items"]["properties"]["kind"]["enum"];
        let values: Vec<&str> =
            kind_enum.as_array().unwrap().iter().map(|v| v.as_str().unwrap()).collect();
        assert_eq!(values, vec!["precondition", "postcondition", "invariant"]);
    }

    #[test]
    fn test_build_tool_definition_required_fields() {
        let tool = build_tool_definition();
        let required = &tool["input_schema"]["properties"]["proposals"]["items"]["required"];
        let fields: Vec<&str> =
            required.as_array().unwrap().iter().map(|v| v.as_str().unwrap()).collect();
        assert!(fields.contains(&"kind"));
        assert!(fields.contains(&"spec_body"));
        assert!(fields.contains(&"confidence"));
        assert!(fields.contains(&"rationale"));
    }

    #[test]
    fn test_parse_tool_use_response_valid() {
        let input = r#"{"proposals": [
            {"kind": "precondition", "spec_body": "a <= u64::MAX - b", "confidence": 0.9, "rationale": "Overflow guard"}
        ]}"#;
        let proposals = parse_tool_use_response(input, "get_midpoint", "test::get_midpoint");
        assert_eq!(proposals.len(), 1);
        assert_eq!(proposals[0].function_name, "get_midpoint");
        assert_eq!(proposals[0].function_path, "test::get_midpoint");
        assert!(matches!(
            &proposals[0].kind,
            ProposalKind::AddPrecondition { spec_body } if spec_body == "a <= u64::MAX - b"
        ));
        assert!((proposals[0].confidence - 0.9).abs() < f64::EPSILON);
    }

    #[test]
    fn test_parse_tool_use_response_multiple_proposals() {
        let input = r#"{"proposals": [
            {"kind": "precondition", "spec_body": "b != 0", "confidence": 0.95, "rationale": "No div by zero"},
            {"kind": "postcondition", "spec_body": "result * b <= a", "confidence": 0.8, "rationale": "Division bound"},
            {"kind": "invariant", "spec_body": "i < len", "confidence": 0.85, "rationale": "Loop bound"}
        ]}"#;
        let proposals = parse_tool_use_response(input, "divide", "test::divide");
        assert_eq!(proposals.len(), 3);
        assert!(matches!(&proposals[0].kind, ProposalKind::AddPrecondition { .. }));
        assert!(matches!(&proposals[1].kind, ProposalKind::AddPostcondition { .. }));
        assert!(matches!(&proposals[2].kind, ProposalKind::AddInvariant { .. }));
    }

    #[test]
    fn test_parse_tool_use_response_invalid_json() {
        let proposals = parse_tool_use_response("not json", "f", "f");
        assert!(proposals.is_empty());
    }

    #[test]
    fn test_parse_tool_use_response_empty_proposals() {
        let input = r#"{"proposals": []}"#;
        let proposals = parse_tool_use_response(input, "f", "f");
        assert!(proposals.is_empty());
    }

    #[test]
    fn test_parse_tool_use_response_unknown_kind_filtered() {
        let input = r#"{"proposals": [
            {"kind": "precondition", "spec_body": "x > 0", "confidence": 0.9, "rationale": "ok"},
            {"kind": "magic", "spec_body": "nope", "confidence": 0.1, "rationale": "bad"}
        ]}"#;
        let proposals = parse_tool_use_response(input, "f", "f");
        assert_eq!(proposals.len(), 1);
        assert!(matches!(&proposals[0].kind, ProposalKind::AddPrecondition { .. }));
    }

    #[test]
    fn test_parse_tool_use_response_confidence_clamped() {
        let input = r#"{"proposals": [
            {"kind": "precondition", "spec_body": "x > 0", "confidence": 1.5, "rationale": "over"}
        ]}"#;
        let proposals = parse_tool_use_response(input, "f", "f");
        assert_eq!(proposals.len(), 1);
        assert!((proposals[0].confidence - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_content_block_deserialize_text() {
        let json = r#"{"type": "text", "text": "Hello world"}"#;
        let block: ContentBlock = serde_json::from_str(json).expect("should parse text block");
        match block {
            ContentBlock::Text { text } => assert_eq!(text, "Hello world"),
            _ => panic!("expected Text variant"),
        }
    }

    #[test]
    fn test_content_block_deserialize_tool_use() {
        let json = r#"{
            "type": "tool_use",
            "id": "toolu_123",
            "name": "propose_specifications",
            "input": {"proposals": []}
        }"#;
        let block: ContentBlock = serde_json::from_str(json).expect("should parse tool_use block");
        match block {
            ContentBlock::ToolUse { id, name, input } => {
                assert_eq!(id, "toolu_123");
                assert_eq!(name, "propose_specifications");
                assert!(input["proposals"].as_array().unwrap().is_empty());
            }
            _ => panic!("expected ToolUse variant"),
        }
    }

    #[test]
    fn test_content_block_deserialize_mixed_response() {
        let json = r#"{"content": [
            {"type": "text", "text": "Here are my proposals:"},
            {"type": "tool_use", "id": "toolu_456", "name": "propose_specifications", "input": {
                "proposals": [{"kind": "precondition", "spec_body": "n > 0", "confidence": 0.9, "rationale": "Positive input"}]
            }}
        ]}"#;
        let response: MessagesResponse =
            serde_json::from_str(json).expect("should parse mixed response");
        assert_eq!(response.content.len(), 2);
        assert!(
            matches!(&response.content[0], ContentBlock::Text { text } if text == "Here are my proposals:")
        );
        assert!(
            matches!(&response.content[1], ContentBlock::ToolUse { name, .. } if name == "propose_specifications")
        );
    }

    #[test]
    fn test_messages_request_serialization_without_tools() {
        let request = MessagesRequest {
            model: "AI Model-sonnet-4-20250514".into(),
            max_tokens: 1024,
            messages: vec![Message { role: "user".into(), content: "test".into() }],
            tools: None,
            tool_choice: None,
        };
        let json = serde_json::to_value(&request).expect("should serialize");
        assert!(json.get("tools").is_none());
        assert!(json.get("tool_choice").is_none());
        assert_eq!(json["model"], "AI Model-sonnet-4-20250514");
    }

    #[test]
    fn test_messages_request_serialization_with_tools() {
        let request = MessagesRequest {
            model: "AI Model-sonnet-4-20250514".into(),
            max_tokens: 1024,
            messages: vec![Message { role: "user".into(), content: "test".into() }],
            tools: Some(vec![build_tool_definition()]),
            tool_choice: Some(
                serde_json::json!({"type": "tool", "name": "propose_specifications"}),
            ),
        };
        let json = serde_json::to_value(&request).expect("should serialize");
        let tools = json["tools"].as_array().expect("tools should be array");
        assert_eq!(tools.len(), 1);
        assert_eq!(tools[0]["name"], "propose_specifications");
        assert_eq!(json["tool_choice"]["type"], "tool");
        assert_eq!(json["tool_choice"]["name"], "propose_specifications");
    }

    #[test]
    fn test_tool_use_input_round_trip() {
        let input = ToolUseInput {
            proposals: vec![ToolProposalSchema {
                kind: "precondition".into(),
                spec_body: "x > 0".into(),
                confidence: 0.9,
                rationale: "Must be positive".into(),
            }],
        };
        let json = serde_json::to_string(&input).expect("should serialize");
        let parsed: ToolUseInput = serde_json::from_str(&json).expect("should deserialize");
        assert_eq!(parsed.proposals.len(), 1);
        assert_eq!(parsed.proposals[0].kind, "precondition");
        assert_eq!(parsed.proposals[0].spec_body, "x > 0");
    }

    #[test]
    fn test_claude_config_use_tool_use_default_true() {
        let config = ClaudeConfig::default();
        assert!(config.use_tool_use);
    }

    /// Mock that simulates a tool_use response for testing the fallback path.
    struct MockToolUseLlm {
        use_tool_use: bool,
    }

    impl LlmBackend for MockToolUseLlm {
        fn send(
            &self,
            _request: &crate::LlmRequest,
        ) -> Result<crate::LlmResponse, crate::LlmError> {
            if self.use_tool_use {
                // Simulate structured tool_use response
                let input = ToolUseInput {
                    proposals: vec![ToolProposalSchema {
                        kind: "precondition".into(),
                        spec_body: "a <= u64::MAX - b".into(),
                        confidence: 0.95,
                        rationale: "Overflow guard via tool_use".into(),
                    }],
                };
                Ok(crate::LlmResponse {
                    content: serde_json::to_string(&input).expect("serialize input"),
                    used_tool_use: true,
                    model_used: "mock-tool-use".into(),
                })
            } else {
                // Simulate plain text fallback
                Ok(crate::LlmResponse {
                    content: r#"[{"kind": "precondition", "spec_body": "a <= u64::MAX - b", "confidence": 0.9, "rationale": "Overflow guard via text"}]"#.into(),
                    used_tool_use: false,
                    model_used: "mock-text".into(),
                })
            }
        }
    }

    #[test]
    fn test_fallback_tool_use_to_text_parsing() {
        // When used_tool_use is true, content is ToolUseInput JSON
        let mock = MockToolUseLlm { use_tool_use: true };
        let response = mock
            .send(&crate::LlmRequest {
                prompt: "test".into(),
                model: String::new(),
                max_response_tokens: 1024,
                use_tool_use: true,
            })
            .expect("should succeed");
        assert!(response.used_tool_use);
        let proposals =
            parse_tool_use_response(&response.content, "get_midpoint", "test::get_midpoint");
        assert_eq!(proposals.len(), 1);
        assert!((proposals[0].confidence - 0.95).abs() < f64::EPSILON);

        // When used_tool_use is false, content is free-form text
        let mock = MockToolUseLlm { use_tool_use: false };
        let response = mock
            .send(&crate::LlmRequest {
                prompt: "test".into(),
                model: String::new(),
                max_response_tokens: 1024,
                use_tool_use: false,
            })
            .expect("should succeed");
        assert!(!response.used_tool_use);
        let proposals = parse_llm_response(&response.content, "get_midpoint", "test::get_midpoint");
        assert_eq!(proposals.len(), 1);
        assert!((proposals[0].confidence - 0.9).abs() < f64::EPSILON);
    }

    #[test]
    fn test_parse_tool_use_missing_proposals_key() {
        // If the input JSON doesn't have the "proposals" key, it should fail gracefully
        let input = r#"{"other_field": "value"}"#;
        let proposals = parse_tool_use_response(input, "f", "f");
        assert!(proposals.is_empty());
    }
}
