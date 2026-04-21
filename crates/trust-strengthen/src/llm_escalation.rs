// trust-strengthen/llm_escalation.rs: Model escalation for AI Model API spec inference
//
// Implements tiered model escalation (Phase 6, #616): when a lower-tier model
// fails (empty response, low confidence, parse failure), the system automatically
// retries with a higher-tier model. This improves spec inference quality for
// complex functions without wasting expensive model capacity on easy cases.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::{LlmBackend, LlmError, LlmRequest, LlmResponse};

/// Model tiers ordered by capability and cost.
///
/// Escalation proceeds Fast -> Balanced -> Strong. Each tier maps to a
/// concrete AI Provider model ID.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ModelTier {
    /// Fastest and cheapest: AI Model Haiku.
    Fast,
    /// Default balance of speed and quality: AI Model Sonnet.
    Balanced,
    /// Highest capability for complex inference: AI Model Opus.
    Strong,
}

impl ModelTier {
    /// Return the AI Provider model ID for this tier.
    #[must_use]
    pub fn model_id(&self) -> &'static str {
        match self {
            Self::Fast => "AI Model-haiku-4-20250514",
            Self::Balanced => "AI Model-sonnet-4-20250514",
            Self::Strong => "AI Model-opus-4-20250514",
        }
    }

    /// Return the next higher tier, if one exists.
    #[must_use]
    pub fn next(&self) -> Option<Self> {
        match self {
            Self::Fast => Some(Self::Balanced),
            Self::Balanced => Some(Self::Strong),
            Self::Strong => None,
        }
    }

    /// Return all tiers in ascending order.
    #[must_use]
    pub fn all() -> &'static [Self] {
        &[Self::Fast, Self::Balanced, Self::Strong]
    }
}

impl std::fmt::Display for ModelTier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Fast => write!(f, "Fast(haiku)"),
            Self::Balanced => write!(f, "Balanced(sonnet)"),
            Self::Strong => write!(f, "Strong(opus)"),
        }
    }
}

/// Reasons that trigger escalation to a higher model tier.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EscalationTrigger {
    /// The model returned an empty response (no proposals).
    EmptyResponse,
    /// All proposals had confidence below the threshold.
    LowConfidence {
        /// The highest confidence seen in the response.
        max_confidence: u32,
    },
    /// The response could not be parsed as valid proposals.
    ParseFailure,
    /// The backend returned a transient error (timeout, server error).
    TransientError,
}

impl std::fmt::Display for EscalationTrigger {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::EmptyResponse => write!(f, "empty response"),
            Self::LowConfidence { max_confidence } => {
                write!(f, "low confidence (max: 0.{max_confidence:02})")
            }
            Self::ParseFailure => write!(f, "parse failure"),
            Self::TransientError => write!(f, "transient error"),
        }
    }
}

/// Policy governing when and how to escalate between model tiers.
#[derive(Debug, Clone)]
pub struct EscalationPolicy {
    /// Maximum number of escalations allowed per inference call.
    pub max_escalations: u32,
    /// Maximum attempts at each tier before escalating.
    pub max_attempts_per_tier: u32,
    /// Confidence threshold: proposals below this trigger escalation.
    /// Stored as integer percentage (0-100) to avoid floating point in config.
    pub confidence_threshold_pct: u32,
    /// Which triggers are enabled for escalation.
    pub enabled_triggers: Vec<EscalationTrigger>,
    /// Starting tier for inference requests.
    pub starting_tier: ModelTier,
}

impl Default for EscalationPolicy {
    fn default() -> Self {
        Self {
            max_escalations: 2,
            max_attempts_per_tier: 1,
            confidence_threshold_pct: 50,
            starting_tier: ModelTier::Balanced,
            enabled_triggers: vec![
                EscalationTrigger::EmptyResponse,
                EscalationTrigger::LowConfidence { max_confidence: 0 },
                EscalationTrigger::ParseFailure,
                EscalationTrigger::TransientError,
            ],
        }
    }
}

impl EscalationPolicy {
    /// Check whether a given trigger type is enabled in this policy.
    ///
    /// For `LowConfidence`, matches regardless of the specific max_confidence value
    /// (the threshold check is done separately in `should_escalate`).
    #[must_use]
    pub fn trigger_enabled(&self, trigger: &EscalationTrigger) -> bool {
        self.enabled_triggers.iter().any(|t| {
            std::mem::discriminant(t) == std::mem::discriminant(trigger)
        })
    }
}

/// Tracks escalation state across retries within a single inference call.
#[derive(Debug)]
pub struct EscalationTracker {
    policy: EscalationPolicy,
    current_tier: ModelTier,
    escalations_used: u32,
    attempts_at_current_tier: u32,
    /// History of (tier, trigger) pairs for diagnostics.
    history: Vec<(ModelTier, EscalationTrigger)>,
}

impl EscalationTracker {
    /// Create a new tracker with the given policy.
    #[must_use]
    pub fn new(policy: EscalationPolicy) -> Self {
        let starting_tier = policy.starting_tier;
        Self {
            policy,
            current_tier: starting_tier,
            escalations_used: 0,
            attempts_at_current_tier: 0,
            history: Vec::new(),
        }
    }

    /// The current model tier.
    #[must_use]
    pub fn current_tier(&self) -> ModelTier {
        self.current_tier
    }

    /// The model ID for the current tier.
    #[must_use]
    pub fn current_model_id(&self) -> &'static str {
        self.current_tier.model_id()
    }

    /// Number of escalations performed so far.
    #[must_use]
    pub fn escalations_used(&self) -> u32 {
        self.escalations_used
    }

    /// Escalation history: each (tier, trigger) where an escalation occurred.
    #[must_use]
    pub fn history(&self) -> &[(ModelTier, EscalationTrigger)] {
        &self.history
    }

    /// Record an attempt at the current tier.
    pub fn record_attempt(&mut self) {
        self.attempts_at_current_tier += 1;
    }

    /// Determine whether to escalate based on the given trigger.
    ///
    /// Returns `Some(next_tier)` if escalation should proceed, `None` if
    /// escalation is exhausted or the trigger is not enabled.
    #[must_use]
    pub fn should_escalate(&self, trigger: &EscalationTrigger) -> Option<ModelTier> {
        // Check escalation budget
        if self.escalations_used >= self.policy.max_escalations {
            return None;
        }

        // Check per-tier attempt budget
        if self.attempts_at_current_tier < self.policy.max_attempts_per_tier {
            return None;
        }

        // Check if this trigger type is enabled
        if !self.policy.trigger_enabled(trigger) {
            return None;
        }

        // For LowConfidence, check against the policy threshold
        if let EscalationTrigger::LowConfidence { max_confidence } = trigger
            && *max_confidence >= self.policy.confidence_threshold_pct {
                return None;
            }

        // Get next tier
        self.current_tier.next()
    }

    /// Execute the escalation: advance to the next tier.
    ///
    /// Call this after `should_escalate` returns `Some(tier)`.
    /// Panics if `next_tier` is not the expected next tier.
    pub fn escalate(&mut self, trigger: EscalationTrigger, next_tier: ModelTier) {
        debug_assert_eq!(
            self.current_tier.next(),
            Some(next_tier),
            "escalation must advance to the next tier"
        );
        self.history.push((self.current_tier, trigger));
        self.current_tier = next_tier;
        self.escalations_used += 1;
        self.attempts_at_current_tier = 0;
    }
}

/// Result of an escalated inference call.
#[derive(Debug)]
pub struct EscalatedResponse {
    /// The LLM response (from whichever tier succeeded).
    pub response: LlmResponse,
    /// Which tier produced the response.
    pub tier_used: ModelTier,
    /// Number of escalations that occurred.
    pub escalations: u32,
    /// Escalation history for diagnostics.
    pub history: Vec<(ModelTier, EscalationTrigger)>,
}

/// Send a request with automatic model escalation on failure.
///
/// Starts at the tracker's current tier and escalates on triggers.
/// The `evaluate` callback inspects each response and returns either
/// `Ok(())` (accept) or `Err(trigger)` (escalate).
pub fn send_with_escalation<F>(
    backend: &dyn LlmBackend,
    base_request: &LlmRequest,
    tracker: &mut EscalationTracker,
    mut evaluate: F,
) -> Result<EscalatedResponse, LlmError>
where
    F: FnMut(&LlmResponse) -> Result<(), EscalationTrigger>,
{
    loop {
        tracker.record_attempt();

        // Build request with the current tier's model
        let request = LlmRequest {
            model: tracker.current_model_id().to_string(),
            prompt: base_request.prompt.clone(),
            max_response_tokens: base_request.max_response_tokens,
            use_tool_use: base_request.use_tool_use,
        };

        let result = backend.send(&request);

        match result {
            Ok(response) => {
                match evaluate(&response) {
                    Ok(()) => {
                        // Response accepted
                        return Ok(EscalatedResponse {
                            response,
                            tier_used: tracker.current_tier(),
                            escalations: tracker.escalations_used(),
                            history: tracker.history().to_vec(),
                        });
                    }
                    Err(trigger) => {
                        // Response rejected; try escalation
                        if let Some(next_tier) = tracker.should_escalate(&trigger) {
                            tracker.escalate(trigger, next_tier);
                            continue;
                        }
                        // No more escalation possible; return what we have
                        return Ok(EscalatedResponse {
                            response,
                            tier_used: tracker.current_tier(),
                            escalations: tracker.escalations_used(),
                            history: tracker.history().to_vec(),
                        });
                    }
                }
            }
            Err(LlmError::Timeout { .. } | LlmError::ServerError { .. }) => {
                let trigger = EscalationTrigger::TransientError;
                if let Some(next_tier) = tracker.should_escalate(&trigger) {
                    tracker.escalate(trigger, next_tier);
                    continue;
                }
                return Err(result.unwrap_err());
            }
            Err(e) => return Err(e),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicU32, Ordering};

    // -- ModelTier tests --

    #[test]
    fn test_model_tier_model_ids() {
        assert_eq!(ModelTier::Fast.model_id(), "AI Model-haiku-4-20250514");
        assert_eq!(ModelTier::Balanced.model_id(), "AI Model-sonnet-4-20250514");
        assert_eq!(ModelTier::Strong.model_id(), "AI Model-opus-4-20250514");
    }

    #[test]
    fn test_model_tier_next() {
        assert_eq!(ModelTier::Fast.next(), Some(ModelTier::Balanced));
        assert_eq!(ModelTier::Balanced.next(), Some(ModelTier::Strong));
        assert_eq!(ModelTier::Strong.next(), None);
    }

    #[test]
    fn test_model_tier_ordering() {
        assert!(ModelTier::Fast < ModelTier::Balanced);
        assert!(ModelTier::Balanced < ModelTier::Strong);
    }

    #[test]
    fn test_model_tier_all() {
        let all = ModelTier::all();
        assert_eq!(all.len(), 3);
        assert_eq!(all[0], ModelTier::Fast);
        assert_eq!(all[1], ModelTier::Balanced);
        assert_eq!(all[2], ModelTier::Strong);
    }

    #[test]
    fn test_model_tier_display() {
        assert_eq!(format!("{}", ModelTier::Fast), "Fast(haiku)");
        assert_eq!(format!("{}", ModelTier::Balanced), "Balanced(sonnet)");
        assert_eq!(format!("{}", ModelTier::Strong), "Strong(opus)");
    }

    // -- EscalationPolicy tests --

    #[test]
    fn test_default_policy() {
        let policy = EscalationPolicy::default();
        assert_eq!(policy.max_escalations, 2);
        assert_eq!(policy.max_attempts_per_tier, 1);
        assert_eq!(policy.confidence_threshold_pct, 50);
        assert_eq!(policy.starting_tier, ModelTier::Balanced);
        assert_eq!(policy.enabled_triggers.len(), 4);
    }

    #[test]
    fn test_trigger_enabled() {
        let policy = EscalationPolicy::default();
        assert!(policy.trigger_enabled(&EscalationTrigger::EmptyResponse));
        assert!(policy.trigger_enabled(&EscalationTrigger::ParseFailure));
        assert!(policy.trigger_enabled(&EscalationTrigger::TransientError));
        assert!(policy.trigger_enabled(&EscalationTrigger::LowConfidence {
            max_confidence: 30,
        }));
    }

    #[test]
    fn test_trigger_enabled_subset() {
        let policy = EscalationPolicy {
            enabled_triggers: vec![EscalationTrigger::EmptyResponse],
            ..Default::default()
        };
        assert!(policy.trigger_enabled(&EscalationTrigger::EmptyResponse));
        assert!(!policy.trigger_enabled(&EscalationTrigger::ParseFailure));
        assert!(!policy.trigger_enabled(&EscalationTrigger::TransientError));
    }

    // -- EscalationTracker tests --

    #[test]
    fn test_tracker_starts_at_policy_tier() {
        let policy = EscalationPolicy {
            starting_tier: ModelTier::Fast,
            ..Default::default()
        };
        let tracker = EscalationTracker::new(policy);
        assert_eq!(tracker.current_tier(), ModelTier::Fast);
        assert_eq!(tracker.escalations_used(), 0);
        assert!(tracker.history().is_empty());
    }

    #[test]
    fn test_tracker_record_attempt() {
        let mut tracker = EscalationTracker::new(EscalationPolicy::default());
        assert_eq!(tracker.attempts_at_current_tier, 0);
        tracker.record_attempt();
        assert_eq!(tracker.attempts_at_current_tier, 1);
    }

    #[test]
    fn test_should_escalate_empty_response() {
        let policy = EscalationPolicy {
            starting_tier: ModelTier::Fast,
            max_attempts_per_tier: 1,
            ..Default::default()
        };
        let mut tracker = EscalationTracker::new(policy);
        tracker.record_attempt();

        let result = tracker.should_escalate(&EscalationTrigger::EmptyResponse);
        assert_eq!(result, Some(ModelTier::Balanced));
    }

    #[test]
    fn test_should_escalate_not_enough_attempts() {
        let policy = EscalationPolicy {
            starting_tier: ModelTier::Fast,
            max_attempts_per_tier: 2,
            ..Default::default()
        };
        let mut tracker = EscalationTracker::new(policy);
        tracker.record_attempt(); // only 1 of 2

        let result = tracker.should_escalate(&EscalationTrigger::EmptyResponse);
        assert_eq!(result, None); // not enough attempts yet
    }

    #[test]
    fn test_should_escalate_budget_exhausted() {
        let policy = EscalationPolicy {
            starting_tier: ModelTier::Fast,
            max_escalations: 1,
            max_attempts_per_tier: 1,
            ..Default::default()
        };
        let mut tracker = EscalationTracker::new(policy);

        // First escalation: Fast -> Balanced
        tracker.record_attempt();
        let next = tracker.should_escalate(&EscalationTrigger::EmptyResponse);
        assert_eq!(next, Some(ModelTier::Balanced));
        tracker.escalate(EscalationTrigger::EmptyResponse, ModelTier::Balanced);

        // Second escalation: budget exhausted
        tracker.record_attempt();
        let next = tracker.should_escalate(&EscalationTrigger::EmptyResponse);
        assert_eq!(next, None);
    }

    #[test]
    fn test_should_escalate_at_top_tier() {
        let policy = EscalationPolicy {
            starting_tier: ModelTier::Strong,
            max_attempts_per_tier: 1,
            ..Default::default()
        };
        let mut tracker = EscalationTracker::new(policy);
        tracker.record_attempt();

        let result = tracker.should_escalate(&EscalationTrigger::EmptyResponse);
        assert_eq!(result, None); // no tier above Strong
    }

    #[test]
    fn test_should_escalate_low_confidence_below_threshold() {
        let policy = EscalationPolicy {
            starting_tier: ModelTier::Fast,
            max_attempts_per_tier: 1,
            confidence_threshold_pct: 50,
            ..Default::default()
        };
        let mut tracker = EscalationTracker::new(policy);
        tracker.record_attempt();

        // 30% < 50% threshold -> should escalate
        let result = tracker.should_escalate(&EscalationTrigger::LowConfidence {
            max_confidence: 30,
        });
        assert_eq!(result, Some(ModelTier::Balanced));
    }

    #[test]
    fn test_should_escalate_low_confidence_above_threshold() {
        let policy = EscalationPolicy {
            starting_tier: ModelTier::Fast,
            max_attempts_per_tier: 1,
            confidence_threshold_pct: 50,
            ..Default::default()
        };
        let mut tracker = EscalationTracker::new(policy);
        tracker.record_attempt();

        // 60% >= 50% threshold -> should NOT escalate
        let result = tracker.should_escalate(&EscalationTrigger::LowConfidence {
            max_confidence: 60,
        });
        assert_eq!(result, None);
    }

    #[test]
    fn test_should_escalate_disabled_trigger() {
        let policy = EscalationPolicy {
            starting_tier: ModelTier::Fast,
            max_attempts_per_tier: 1,
            enabled_triggers: vec![EscalationTrigger::EmptyResponse],
            ..Default::default()
        };
        let mut tracker = EscalationTracker::new(policy);
        tracker.record_attempt();

        // ParseFailure is not enabled
        let result = tracker.should_escalate(&EscalationTrigger::ParseFailure);
        assert_eq!(result, None);
    }

    #[test]
    fn test_escalate_advances_tier() {
        let policy = EscalationPolicy {
            starting_tier: ModelTier::Fast,
            max_attempts_per_tier: 1,
            ..Default::default()
        };
        let mut tracker = EscalationTracker::new(policy);
        tracker.record_attempt();

        tracker.escalate(EscalationTrigger::EmptyResponse, ModelTier::Balanced);
        assert_eq!(tracker.current_tier(), ModelTier::Balanced);
        assert_eq!(tracker.escalations_used(), 1);
        assert_eq!(tracker.attempts_at_current_tier, 0); // reset
        assert_eq!(tracker.history().len(), 1);
        assert_eq!(tracker.history()[0].0, ModelTier::Fast);
    }

    #[test]
    fn test_full_escalation_chain() {
        let policy = EscalationPolicy {
            starting_tier: ModelTier::Fast,
            max_escalations: 2,
            max_attempts_per_tier: 1,
            ..Default::default()
        };
        let mut tracker = EscalationTracker::new(policy);

        // Fast -> Balanced
        tracker.record_attempt();
        let next = tracker.should_escalate(&EscalationTrigger::EmptyResponse);
        assert_eq!(next, Some(ModelTier::Balanced));
        tracker.escalate(EscalationTrigger::EmptyResponse, ModelTier::Balanced);

        // Balanced -> Strong
        tracker.record_attempt();
        let next = tracker.should_escalate(&EscalationTrigger::ParseFailure);
        assert_eq!(next, Some(ModelTier::Strong));
        tracker.escalate(EscalationTrigger::ParseFailure, ModelTier::Strong);

        assert_eq!(tracker.current_tier(), ModelTier::Strong);
        assert_eq!(tracker.escalations_used(), 2);
        assert_eq!(tracker.history().len(), 2);
    }

    #[test]
    fn test_escalation_trigger_display() {
        assert_eq!(
            format!("{}", EscalationTrigger::EmptyResponse),
            "empty response"
        );
        assert_eq!(
            format!("{}", EscalationTrigger::ParseFailure),
            "parse failure"
        );
        assert_eq!(
            format!("{}", EscalationTrigger::TransientError),
            "transient error"
        );
        assert_eq!(
            format!(
                "{}",
                EscalationTrigger::LowConfidence {
                    max_confidence: 30
                }
            ),
            "low confidence (max: 0.30)"
        );
    }

    // -- send_with_escalation integration tests --

    /// Mock backend that tracks which models receive requests.
    struct EscalationMockLlm {
        call_count: AtomicU32,
        /// Response content per call (indexed by call_count).
        responses: Vec<Result<String, LlmError>>,
    }

    impl EscalationMockLlm {
        fn new(responses: Vec<Result<String, LlmError>>) -> Self {
            Self {
                call_count: AtomicU32::new(0),
                responses,
            }
        }
    }

    impl LlmBackend for EscalationMockLlm {
        fn send(&self, request: &LlmRequest) -> Result<LlmResponse, LlmError> {
            let idx = self.call_count.fetch_add(1, Ordering::Relaxed) as usize;
            match self.responses.get(idx) {
                Some(Ok(content)) => Ok(LlmResponse {
                    content: content.clone(),
                    used_tool_use: false,
                    model_used: request.model.clone(),
                }),
                Some(Err(_)) => Err(LlmError::ServerError { status: 500 }),
                None => Ok(LlmResponse {
                    content: "[]".into(),
                    used_tool_use: false,
                    model_used: request.model.clone(),
                }),
            }
        }
    }

    #[test]
    fn test_send_with_escalation_no_escalation_needed() {
        let mock = EscalationMockLlm::new(vec![Ok(
            r#"[{"kind":"precondition","spec_body":"x > 0","confidence":0.9,"rationale":"ok"}]"#
                .into(),
        )]);
        let policy = EscalationPolicy {
            starting_tier: ModelTier::Fast,
            ..Default::default()
        };
        let mut tracker = EscalationTracker::new(policy);
        let request = LlmRequest {
            prompt: "test".into(),
            model: String::new(),
            max_response_tokens: 1024,
            use_tool_use: false,
        };

        let result = send_with_escalation(&mock, &request, &mut tracker, |_resp| Ok(()));
        let resp = result.expect("should succeed");
        assert_eq!(resp.tier_used, ModelTier::Fast);
        assert_eq!(resp.escalations, 0);
        assert!(resp.history.is_empty());
        assert_eq!(resp.response.model_used, "AI Model-haiku-4-20250514");
    }

    #[test]
    fn test_send_with_escalation_one_escalation() {
        let mock = EscalationMockLlm::new(vec![
            Ok("[]".into()),           // Fast: empty
            Ok(r#"[{"kind":"precondition","spec_body":"x > 0","confidence":0.9,"rationale":"ok"}]"#.into()), // Balanced: good
        ]);
        let policy = EscalationPolicy {
            starting_tier: ModelTier::Fast,
            max_attempts_per_tier: 1,
            ..Default::default()
        };
        let mut tracker = EscalationTracker::new(policy);
        let request = LlmRequest {
            prompt: "test".into(),
            model: String::new(),
            max_response_tokens: 1024,
            use_tool_use: false,
        };

        let call = AtomicU32::new(0);
        let result = send_with_escalation(&mock, &request, &mut tracker, |resp| {
            let n = call.fetch_add(1, Ordering::Relaxed);
            if n == 0 && resp.content == "[]" {
                Err(EscalationTrigger::EmptyResponse)
            } else {
                Ok(())
            }
        });

        let resp = result.expect("should succeed");
        assert_eq!(resp.tier_used, ModelTier::Balanced);
        assert_eq!(resp.escalations, 1);
        assert_eq!(resp.history.len(), 1);
        assert_eq!(resp.history[0].0, ModelTier::Fast);
        assert_eq!(resp.response.model_used, "AI Model-sonnet-4-20250514");
    }

    #[test]
    fn test_send_with_escalation_full_chain() {
        let mock = EscalationMockLlm::new(vec![
            Ok("[]".into()),     // Fast: empty
            Ok("bad json".into()), // Balanced: parse failure
            Ok(r#"[{"kind":"precondition","spec_body":"x > 0","confidence":0.9,"rationale":"ok"}]"#.into()), // Strong: good
        ]);
        let policy = EscalationPolicy {
            starting_tier: ModelTier::Fast,
            max_escalations: 2,
            max_attempts_per_tier: 1,
            ..Default::default()
        };
        let mut tracker = EscalationTracker::new(policy);
        let request = LlmRequest {
            prompt: "test".into(),
            model: String::new(),
            max_response_tokens: 1024,
            use_tool_use: false,
        };

        let call = AtomicU32::new(0);
        let result = send_with_escalation(&mock, &request, &mut tracker, |_resp| {
            let n = call.fetch_add(1, Ordering::Relaxed);
            match n {
                0 => Err(EscalationTrigger::EmptyResponse),
                1 => Err(EscalationTrigger::ParseFailure),
                _ => Ok(()),
            }
        });

        let resp = result.expect("should succeed");
        assert_eq!(resp.tier_used, ModelTier::Strong);
        assert_eq!(resp.escalations, 2);
        assert_eq!(resp.response.model_used, "AI Model-opus-4-20250514");
    }

    #[test]
    fn test_send_with_escalation_returns_last_response_when_exhausted() {
        let mock = EscalationMockLlm::new(vec![
            Ok("[]".into()), // Fast: empty
            Ok("[]".into()), // Balanced: empty
            Ok("[]".into()), // Strong: still empty
        ]);
        let policy = EscalationPolicy {
            starting_tier: ModelTier::Fast,
            max_escalations: 2,
            max_attempts_per_tier: 1,
            ..Default::default()
        };
        let mut tracker = EscalationTracker::new(policy);
        let request = LlmRequest {
            prompt: "test".into(),
            model: String::new(),
            max_response_tokens: 1024,
            use_tool_use: false,
        };

        let result = send_with_escalation(&mock, &request, &mut tracker, |response| {
            if response.content == "[]" {
                Err(EscalationTrigger::EmptyResponse)
            } else {
                Ok(())
            }
        });

        // Should still return Ok with the last response
        let resp = result.expect("should return last response");
        assert_eq!(resp.tier_used, ModelTier::Strong);
        assert_eq!(resp.escalations, 2);
        assert_eq!(resp.response.content, "[]");
    }

    #[test]
    fn test_send_with_escalation_transient_error() {
        let mock = EscalationMockLlm::new(vec![
            Err(LlmError::ServerError { status: 500 }), // Fast: server error
            Ok(r#"[{"kind":"precondition","spec_body":"x > 0","confidence":0.9,"rationale":"ok"}]"#.into()), // Balanced: good
        ]);
        let policy = EscalationPolicy {
            starting_tier: ModelTier::Fast,
            max_attempts_per_tier: 1,
            ..Default::default()
        };
        let mut tracker = EscalationTracker::new(policy);
        let request = LlmRequest {
            prompt: "test".into(),
            model: String::new(),
            max_response_tokens: 1024,
            use_tool_use: false,
        };

        let result = send_with_escalation(&mock, &request, &mut tracker, |_| Ok(()));
        let resp = result.expect("should succeed after escalation");
        assert_eq!(resp.tier_used, ModelTier::Balanced);
        assert_eq!(resp.escalations, 1);
    }

    #[test]
    fn test_send_with_escalation_non_transient_error() {
        let mock = EscalationMockLlm::new(vec![]);
        // Override send to return a non-transient error
        struct NonTransientMock;
        impl LlmBackend for NonTransientMock {
            fn send(&self, _request: &LlmRequest) -> Result<LlmResponse, LlmError> {
                Err(LlmError::MissingApiKey)
            }
        }

        let policy = EscalationPolicy {
            starting_tier: ModelTier::Fast,
            ..Default::default()
        };
        let mut tracker = EscalationTracker::new(policy);
        let request = LlmRequest {
            prompt: "test".into(),
            model: String::new(),
            max_response_tokens: 1024,
            use_tool_use: false,
        };

        let result = send_with_escalation(&NonTransientMock, &request, &mut tracker, |_| Ok(()));
        assert!(result.is_err());
        // Non-transient errors should NOT trigger escalation
        assert_eq!(tracker.escalations_used(), 0);

        // Suppress unused warning
        let _ = mock;
    }

    #[test]
    fn test_tracker_current_model_id() {
        let policy = EscalationPolicy {
            starting_tier: ModelTier::Balanced,
            ..Default::default()
        };
        let tracker = EscalationTracker::new(policy);
        assert_eq!(tracker.current_model_id(), "AI Model-sonnet-4-20250514");
    }
}
