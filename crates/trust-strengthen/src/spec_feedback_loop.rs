// trust-strengthen/spec_feedback_loop.rs: Spec inference feedback loop orchestrator
//
// Closes the loop: LLM infers specs -> VCs generated -> verification checks them ->
// on failure, counterexample refines the next inference round -> on success,
// specs are proposed back to source.
//
// This is the core architecture of "Idea 2" from VISION.md.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::analyzer::FailureAnalysis;
use crate::llm_inference::{InferenceConfig, LlmSpecInference, ThreeViewContext};
use crate::spec_proposal::{SpecProposal, format_suggestions};
use crate::LlmBackend;

/// Outcome of verifying a set of inferred specs.
#[derive(Debug, Clone)]
pub enum VerifyOutcome {
    /// All VCs passed: specs are valid.
    AllPassed,
    /// Some VCs failed, with counterexample text for refinement.
    Failed {
        /// Human-readable counterexample from the solver.
        counterexample: String,
        /// Which specs failed.
        failed_specs: Vec<SpecProposal>,
    },
    /// Verification encountered an error (timeout, solver crash, etc.).
    Error {
        /// Error description.
        message: String,
    },
}

/// Trait for the verification oracle used by the feedback loop.
///
/// Abstracted so tests can use a mock verifier. In production, this calls
/// trust-vcgen -> trust-router -> dMATH tools.
pub trait VerificationOracle: Send + Sync {
    /// Check whether a set of spec proposals are valid for the given function.
    ///
    /// Returns `AllPassed` if the specs make all VCs provable,
    /// `Failed` with a counterexample if not, or `Error` on infrastructure failure.
    fn verify_specs(
        &self,
        function_path: &str,
        specs: &[SpecProposal],
    ) -> VerifyOutcome;
}

/// A mock verifier that always passes (for testing).
pub struct AlwaysPassVerifier;

impl VerificationOracle for AlwaysPassVerifier {
    fn verify_specs(&self, _: &str, _: &[SpecProposal]) -> VerifyOutcome {
        VerifyOutcome::AllPassed
    }
}

/// A mock verifier that fails N times with a counterexample, then passes.
pub struct FailThenPassVerifier {
    /// Number of times to fail before passing.
    fail_count: std::sync::atomic::AtomicUsize,
    /// Counterexample text to return on failure.
    counterexample: String,
}

impl FailThenPassVerifier {
    /// Create a verifier that fails `n` times then passes.
    #[must_use]
    pub fn new(n: usize, counterexample: &str) -> Self {
        Self {
            fail_count: std::sync::atomic::AtomicUsize::new(n),
            counterexample: counterexample.to_string(),
        }
    }
}

impl VerificationOracle for FailThenPassVerifier {
    fn verify_specs(
        &self,
        _function_path: &str,
        specs: &[SpecProposal],
    ) -> VerifyOutcome {
        let remaining = self
            .fail_count
            .fetch_sub(1, std::sync::atomic::Ordering::SeqCst);
        if remaining > 0 {
            VerifyOutcome::Failed {
                counterexample: self.counterexample.clone(),
                failed_specs: specs.to_vec(),
            }
        } else {
            VerifyOutcome::AllPassed
        }
    }
}

/// Configuration for the spec feedback loop.
#[derive(Debug, Clone)]
pub struct FeedbackLoopConfig {
    /// Maximum number of inference/verification iterations.
    pub max_iterations: usize,
    /// LLM inference configuration.
    pub inference_config: InferenceConfig,
    /// Whether to stop early on the first successful set of specs.
    pub stop_on_first_success: bool,
}

impl Default for FeedbackLoopConfig {
    fn default() -> Self {
        Self {
            max_iterations: 5,
            inference_config: InferenceConfig::default(),
            stop_on_first_success: true,
        }
    }
}

/// Record of a single feedback loop iteration.
#[derive(Debug, Clone)]
pub struct IterationRecord {
    /// Which iteration (1-based).
    pub iteration: usize,
    /// Specs inferred in this iteration.
    pub inferred_specs: Vec<SpecProposal>,
    /// Verification outcome.
    pub outcome: IterationOutcome,
    /// The inference result metadata.
    pub inference_raw_count: usize,
    pub inference_validation_rejected: usize,
}

/// Simplified outcome for the iteration record.
#[derive(Debug, Clone)]
pub enum IterationOutcome {
    /// Specs passed verification.
    Passed,
    /// Specs failed verification.
    Failed { counterexample: String },
    /// No specs were inferred.
    NoSpecs,
    /// Verification errored.
    Error { message: String },
}

/// Result of running the full feedback loop.
#[derive(Debug, Clone)]
pub struct SpecFeedbackResult {
    /// Final accepted specs (empty if no iteration succeeded).
    pub accepted_specs: Vec<SpecProposal>,
    /// History of all iterations.
    pub iterations: Vec<IterationRecord>,
    /// Whether the loop converged (found valid specs).
    pub converged: bool,
    /// Total iterations run.
    pub total_iterations: usize,
    /// Formatted suggestion text (for display/backprop).
    pub suggestion_text: String,
}

/// The spec inference feedback loop orchestrator.
///
/// Coordinates LLM inference, verification, and counterexample-driven refinement
/// in a closed loop until specs converge or the iteration budget is exhausted.
pub struct SpecFeedbackLoop<'a> {
    llm: &'a dyn LlmBackend,
    verifier: &'a dyn VerificationOracle,
    config: FeedbackLoopConfig,
}

impl<'a> SpecFeedbackLoop<'a> {
    /// Create a new feedback loop with the given components.
    #[must_use]
    pub fn new(
        llm: &'a dyn LlmBackend,
        verifier: &'a dyn VerificationOracle,
        config: FeedbackLoopConfig,
    ) -> Self {
        Self {
            llm,
            verifier,
            config,
        }
    }

    /// Run the feedback loop for a single function.
    ///
    /// 1. Infer specs from the LLM using three-view context
    /// 2. Verify the inferred specs
    /// 3. On failure: refine with counterexample and repeat
    /// 4. On success: return accepted specs
    /// 5. Repeat up to max_iterations
    pub fn run(
        &self,
        function_name: &str,
        function_path: &str,
        context: &ThreeViewContext,
        failures: &[FailureAnalysis],
    ) -> SpecFeedbackResult {
        let engine =
            LlmSpecInference::new(self.llm, self.config.inference_config.clone());
        let mut iterations: Vec<IterationRecord> = Vec::new();
        let mut prior_specs: Vec<SpecProposal> = Vec::new();
        let mut last_counterexample: Option<String> = None;

        for iter_num in 1..=self.config.max_iterations {
            // Step 1: Infer specs
            let inference_result = if let Some(ref cex) = last_counterexample {
                engine.infer_with_counterexample(
                    function_name,
                    function_path,
                    context,
                    failures,
                    &prior_specs,
                    cex,
                    iter_num,
                )
            } else {
                engine.infer(function_name, function_path, context, failures, iter_num)
            };

            // Step 2: Check if we got any specs
            if inference_result.proposals.is_empty() {
                iterations.push(IterationRecord {
                    iteration: iter_num,
                    inferred_specs: Vec::new(),
                    outcome: IterationOutcome::NoSpecs,
                    inference_raw_count: inference_result.raw_count,
                    inference_validation_rejected: inference_result.validation_rejected,
                });
                // No specs to verify -- break if this is a repeated failure
                if iter_num > 1 {
                    break;
                }
                continue;
            }

            // Step 3: Verify the inferred specs
            let verify_outcome =
                self.verifier.verify_specs(function_path, &inference_result.proposals);

            match verify_outcome {
                VerifyOutcome::AllPassed => {
                    iterations.push(IterationRecord {
                        iteration: iter_num,
                        inferred_specs: inference_result.proposals.clone(),
                        outcome: IterationOutcome::Passed,
                        inference_raw_count: inference_result.raw_count,
                        inference_validation_rejected: inference_result.validation_rejected,
                    });

                    let suggestion_text = format_suggestions(&inference_result.proposals);

                    return SpecFeedbackResult {
                        accepted_specs: inference_result.proposals,
                        iterations,
                        converged: true,
                        total_iterations: iter_num,
                        suggestion_text,
                    };
                }
                VerifyOutcome::Failed {
                    counterexample,
                    failed_specs: _,
                } => {
                    iterations.push(IterationRecord {
                        iteration: iter_num,
                        inferred_specs: inference_result.proposals.clone(),
                        outcome: IterationOutcome::Failed {
                            counterexample: counterexample.clone(),
                        },
                        inference_raw_count: inference_result.raw_count,
                        inference_validation_rejected: inference_result.validation_rejected,
                    });

                    // Prepare for next iteration with counterexample refinement
                    prior_specs = inference_result.proposals;
                    last_counterexample = Some(counterexample);
                }
                VerifyOutcome::Error { message } => {
                    iterations.push(IterationRecord {
                        iteration: iter_num,
                        inferred_specs: inference_result.proposals.clone(),
                        outcome: IterationOutcome::Error {
                            message: message.clone(),
                        },
                        inference_raw_count: inference_result.raw_count,
                        inference_validation_rejected: inference_result.validation_rejected,
                    });
                    // On error, break the loop
                    break;
                }
            }
        }

        // Did not converge
        let total = iterations.len();
        SpecFeedbackResult {
            accepted_specs: Vec::new(),
            iterations,
            converged: false,
            total_iterations: total,
            suggestion_text: String::new(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analyzer::{FailureAnalysis, FailurePattern};
    use crate::llm_inference::ThreeViewContext;
    use crate::source_reader::extract_function;
    use crate::{LlmError, LlmRequest, LlmResponse};
    use trust_types::{BinOp, Ty, VcKind};

    /// Mock LLM that returns progressively better specs on each call.
    struct ProgressiveMockLlm {
        responses: Vec<String>,
        call_count: std::sync::atomic::AtomicUsize,
    }

    impl ProgressiveMockLlm {
        fn new(responses: Vec<String>) -> Self {
            Self {
                responses,
                call_count: std::sync::atomic::AtomicUsize::new(0),
            }
        }

        fn single(json: &str) -> Self {
            Self::new(vec![json.to_string()])
        }
    }

    impl LlmBackend for ProgressiveMockLlm {
        fn send(&self, _request: &LlmRequest) -> Result<LlmResponse, LlmError> {
            let idx = self
                .call_count
                .fetch_add(1, std::sync::atomic::Ordering::SeqCst);
            let empty = String::new();
            let json = if idx < self.responses.len() {
                &self.responses[idx]
            } else {
                self.responses.last().unwrap_or(&empty)
            };
            Ok(LlmResponse {
                content: json.clone(),
                used_tool_use: false,
                model_used: "mock".into(),
            })
        }
    }

    /// Mock verifier that always returns an error.
    struct ErrorVerifier;

    impl VerificationOracle for ErrorVerifier {
        fn verify_specs(&self, _: &str, _: &[SpecProposal]) -> VerifyOutcome {
            VerifyOutcome::Error {
                message: "solver timeout".into(),
            }
        }
    }

    fn overflow_failure() -> FailureAnalysis {
        FailureAnalysis {
            vc_kind: VcKind::ArithmeticOverflow {
                op: BinOp::Add,
                operand_tys: (
                    Ty::Int {
                        width: 64,
                        signed: false,
                    },
                    Ty::Int {
                        width: 64,
                        signed: false,
                    },
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
            mir_text: Some("bb0: { _3 = Add(_1, _2); _0 = Div(_3, const 2); }".into()),
            reconstructed_source: None,
            existing_specs: Vec::new(),
            source_context: extract_function(source, "get_midpoint"),
        }
    }

    // --- AlwaysPassVerifier ---

    #[test]
    fn test_always_pass_verifier() {
        let v = AlwaysPassVerifier;
        let outcome = v.verify_specs("test::f", &[]);
        assert!(matches!(outcome, VerifyOutcome::AllPassed));
    }

    // --- FailThenPassVerifier ---

    #[test]
    fn test_fail_then_pass_verifier() {
        let v = FailThenPassVerifier::new(2, "a = MAX");

        // First two calls fail
        assert!(matches!(
            v.verify_specs("f", &[]),
            VerifyOutcome::Failed { .. }
        ));
        assert!(matches!(
            v.verify_specs("f", &[]),
            VerifyOutcome::Failed { .. }
        ));

        // Third call passes
        assert!(matches!(
            v.verify_specs("f", &[]),
            VerifyOutcome::AllPassed
        ));
    }

    // --- SpecFeedbackLoop: immediate success ---

    #[test]
    fn test_feedback_loop_immediate_success() {
        let llm = ProgressiveMockLlm::single(
            r#"[{"kind": "precondition", "spec_body": "a <= usize::MAX - b", "confidence": 0.9, "rationale": "Overflow guard"}]"#,
        );
        let verifier = AlwaysPassVerifier;
        let config = FeedbackLoopConfig::default();

        let fl = SpecFeedbackLoop::new(&llm, &verifier, config);
        let result = fl.run(
            "get_midpoint",
            "test::get_midpoint",
            &midpoint_context(),
            &[overflow_failure()],
        );

        assert!(result.converged);
        assert_eq!(result.total_iterations, 1);
        assert_eq!(result.accepted_specs.len(), 1);
        assert_eq!(result.accepted_specs[0].spec_body, "a <= usize::MAX - b");
        assert!(!result.suggestion_text.is_empty());
        assert!(result.suggestion_text.contains("#[requires"));
    }

    // --- SpecFeedbackLoop: converges after refinement ---

    #[test]
    fn test_feedback_loop_converges_with_refinement() {
        // First attempt: too weak. Second attempt: correct.
        let llm = ProgressiveMockLlm::new(vec![
            r#"[{"kind": "precondition", "spec_body": "a > 0", "confidence": 0.7, "rationale": "Weak attempt"}]"#.into(),
            r#"[{"kind": "precondition", "spec_body": "a <= usize::MAX - b", "confidence": 0.95, "rationale": "Refined after counterexample"}]"#.into(),
        ]);
        // Fails first time (weak spec), passes second time (strong spec)
        let verifier = FailThenPassVerifier::new(1, "a = 18446744073709551615, b = 1");
        let config = FeedbackLoopConfig::default();

        let fl = SpecFeedbackLoop::new(&llm, &verifier, config);
        let result = fl.run(
            "get_midpoint",
            "test::get_midpoint",
            &midpoint_context(),
            &[overflow_failure()],
        );

        assert!(result.converged);
        assert_eq!(result.total_iterations, 2);
        assert_eq!(result.iterations.len(), 2);

        // First iteration failed
        assert!(matches!(
            result.iterations[0].outcome,
            IterationOutcome::Failed { .. }
        ));

        // Second iteration passed
        assert!(matches!(
            result.iterations[1].outcome,
            IterationOutcome::Passed
        ));

        assert_eq!(result.accepted_specs[0].spec_body, "a <= usize::MAX - b");
    }

    // --- SpecFeedbackLoop: exhausts iterations ---

    #[test]
    fn test_feedback_loop_exhausts_iterations() {
        let llm = ProgressiveMockLlm::single(
            r#"[{"kind": "precondition", "spec_body": "a > 0", "confidence": 0.7, "rationale": "Always weak"}]"#,
        );
        // Always fails
        let verifier = FailThenPassVerifier::new(100, "counterexample: always fails");
        let config = FeedbackLoopConfig {
            max_iterations: 3,
            ..Default::default()
        };

        let fl = SpecFeedbackLoop::new(&llm, &verifier, config);
        let result = fl.run(
            "get_midpoint",
            "test::get_midpoint",
            &midpoint_context(),
            &[overflow_failure()],
        );

        assert!(!result.converged);
        assert_eq!(result.total_iterations, 3);
        assert!(result.accepted_specs.is_empty());
        assert!(result.suggestion_text.is_empty());
    }

    // --- SpecFeedbackLoop: no specs inferred ---

    #[test]
    fn test_feedback_loop_no_specs() {
        let llm = ProgressiveMockLlm::single("[]");
        let verifier = AlwaysPassVerifier;
        let config = FeedbackLoopConfig::default();

        let fl = SpecFeedbackLoop::new(&llm, &verifier, config);
        let result = fl.run(
            "get_midpoint",
            "test::get_midpoint",
            &midpoint_context(),
            &[overflow_failure()],
        );

        assert!(!result.converged);
        assert!(result.accepted_specs.is_empty());
        // Should have at least one iteration with NoSpecs
        assert!(result
            .iterations
            .iter()
            .any(|i| matches!(i.outcome, IterationOutcome::NoSpecs)));
    }

    // --- SpecFeedbackLoop: error breaks loop ---

    #[test]
    fn test_feedback_loop_error_breaks() {
        let llm = ProgressiveMockLlm::single(
            r#"[{"kind": "precondition", "spec_body": "a > 0", "confidence": 0.7, "rationale": "test"}]"#,
        );
        let verifier = ErrorVerifier;
        let config = FeedbackLoopConfig {
            max_iterations: 5,
            ..Default::default()
        };

        let fl = SpecFeedbackLoop::new(&llm, &verifier, config);
        let result = fl.run(
            "get_midpoint",
            "test::get_midpoint",
            &midpoint_context(),
            &[overflow_failure()],
        );

        assert!(!result.converged);
        assert_eq!(result.total_iterations, 1);
        assert!(matches!(
            result.iterations[0].outcome,
            IterationOutcome::Error { .. }
        ));
    }

    // --- IterationRecord ---

    #[test]
    fn test_iteration_records_capture_history() {
        let llm = ProgressiveMockLlm::new(vec![
            r#"[{"kind": "precondition", "spec_body": "a > 0", "confidence": 0.7, "rationale": "r1"}]"#.into(),
            r#"[{"kind": "precondition", "spec_body": "a > 0 && b > 0", "confidence": 0.8, "rationale": "r2"}]"#.into(),
            r#"[{"kind": "precondition", "spec_body": "a <= usize::MAX - b", "confidence": 0.95, "rationale": "r3"}]"#.into(),
        ]);
        let verifier = FailThenPassVerifier::new(2, "cex");
        let config = FeedbackLoopConfig::default();

        let fl = SpecFeedbackLoop::new(&llm, &verifier, config);
        let result = fl.run(
            "get_midpoint",
            "test::get_midpoint",
            &midpoint_context(),
            &[overflow_failure()],
        );

        assert!(result.converged);
        assert_eq!(result.iterations.len(), 3);
        assert_eq!(result.iterations[0].iteration, 1);
        assert_eq!(result.iterations[1].iteration, 2);
        assert_eq!(result.iterations[2].iteration, 3);

        // Each iteration should have inferred specs
        for iter in &result.iterations {
            assert!(
                !iter.inferred_specs.is_empty(),
                "iteration {} should have inferred specs",
                iter.iteration
            );
        }
    }

    // --- SpecFeedbackResult ---

    #[test]
    fn test_result_suggestion_text_on_success() {
        let llm = ProgressiveMockLlm::single(
            r#"[
                {"kind": "precondition", "spec_body": "a <= usize::MAX - b", "confidence": 0.9, "rationale": "Overflow guard"},
                {"kind": "postcondition", "spec_body": "result == (a + b) / 2", "confidence": 0.85, "rationale": "Midpoint identity"}
            ]"#,
        );
        let verifier = AlwaysPassVerifier;
        let config = FeedbackLoopConfig::default();

        let fl = SpecFeedbackLoop::new(&llm, &verifier, config);
        let result = fl.run(
            "get_midpoint",
            "test::get_midpoint",
            &midpoint_context(),
            &[overflow_failure()],
        );

        assert!(result.converged);
        assert!(result.suggestion_text.contains("#[requires"));
        assert!(result.suggestion_text.contains("#[ensures"));
        assert!(result.suggestion_text.contains("Suggested specs for"));
    }

    // --- Config tests ---

    #[test]
    fn test_default_config() {
        let config = FeedbackLoopConfig::default();
        assert_eq!(config.max_iterations, 5);
        assert!(config.stop_on_first_success);
    }

    #[test]
    fn test_custom_max_iterations() {
        let llm = ProgressiveMockLlm::single(
            r#"[{"kind": "precondition", "spec_body": "a > 0", "confidence": 0.7, "rationale": "test"}]"#,
        );
        let verifier = FailThenPassVerifier::new(100, "cex");
        let config = FeedbackLoopConfig {
            max_iterations: 2,
            ..Default::default()
        };

        let fl = SpecFeedbackLoop::new(&llm, &verifier, config);
        let result = fl.run(
            "f",
            "test::f",
            &midpoint_context(),
            &[overflow_failure()],
        );

        assert!(!result.converged);
        assert!(result.total_iterations <= 2);
    }
}
