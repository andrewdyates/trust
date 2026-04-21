// trust-decompile/beautify.rs: LLM beautification with z4 equivalence-proof loop
//
// Phase VIII of reverse compilation: LLM proposes idiomatic Rust rewrites,
// z4 proves behavioral equivalence. SAT counterexamples are fed back to the
// LLM for correction (up to max_iterations attempts).
//
// Architecture:
//   decompiled_rust -> LLM rewrite -> z4 equiv check
//                         ^                |
//                         |  SAT counter   |
//                         +--- example ----+
//                         (up to N rounds)
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::error::DecompileError;
use crate::types::DecompiledFunction;

// ---------------------------------------------------------------------------
// Configuration
// ---------------------------------------------------------------------------

/// Configuration for the LLM beautification loop.
#[derive(Debug, Clone)]
pub(crate) struct BeautifyConfig {
    /// Maximum number of LLM rewrite + equivalence-check rounds before giving up.
    /// Default: 5 (matches the architecture spec).
    pub(crate) max_iterations: u32,
    /// Whether to prefer concise single-expression bodies over multi-statement.
    pub(crate) prefer_concise: bool,
    /// Whether to convert raw pointer operations to safe Rust idioms.
    pub(crate) prefer_safe_idioms: bool,
    /// Whether to add documentation comments to the beautified output.
    pub(crate) add_doc_comments: bool,
}

impl Default for BeautifyConfig {
    fn default() -> Self {
        Self {
            max_iterations: 5,
            prefer_concise: true,
            prefer_safe_idioms: true,
            add_doc_comments: false,
        }
    }
}

// ---------------------------------------------------------------------------
// Equivalence checking
// ---------------------------------------------------------------------------

/// Status of an equivalence check between original and rewritten code.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum EquivalenceStatus {
    /// z4 proved the rewrite is semantically equivalent (UNSAT on `original != rewrite`).
    Equivalent,
    /// z4 found a divergence (SAT). The `counterexample` field contains concrete
    /// inputs that produce different outputs.
    Divergent {
        /// Human-readable description of the divergence (concrete input/output).
        counterexample: String,
    },
    /// The solver could not determine equivalence (timeout, unknown, or error).
    Unknown {
        /// Reason the check was inconclusive.
        reason: String,
    },
}

/// Result of an equivalence check.
#[derive(Debug, Clone)]
pub(crate) struct EquivalenceResult {
    /// Whether the two code snippets are semantically equivalent.
    pub(crate) status: EquivalenceStatus,
    /// Wall-clock time of the equivalence check in milliseconds.
    pub(crate) time_ms: u64,
}

/// Trait for checking semantic equivalence between two Rust code snippets.
///
/// Implementations encode both snippets as SMT formulas and check whether
/// `original != rewrite` is satisfiable. If UNSAT, the rewrite preserves
/// semantics. If SAT, the model is a counterexample.
///
/// The default implementation is a mock; real z4 integration is deferred
/// to a future issue (see #440).
pub(crate) trait EquivalenceChecker: std::fmt::Debug {
    /// Check whether `original` and `rewritten` are semantically equivalent.
    ///
    /// Both arguments are complete Rust function source strings.
    fn check_equivalence(
        &self,
        original: &str,
        rewritten: &str,
    ) -> Result<EquivalenceResult, DecompileError>;
}

// ---------------------------------------------------------------------------
// LLM rewriting
// ---------------------------------------------------------------------------

/// A suggestion from the LLM: the rewritten source plus an optional explanation.
#[derive(Debug, Clone)]
pub(crate) struct LlmSuggestion {
    /// The rewritten Rust source code.
    pub(crate) source: String,
    /// Optional explanation of what changed and why.
    pub(crate) explanation: Option<String>,
}

/// Trait for LLM-based code rewriting.
///
/// Implementations call an LLM to rewrite decompiled Rust into idiomatic form.
/// The `feedback` parameter carries counterexample information from prior
/// failed equivalence checks, enabling iterative correction.
///
/// The default implementation is a mock; real LLM integration is deferred
/// to a future issue (see #440).
pub(crate) trait LlmRewriter: std::fmt::Debug {
    /// Rewrite `source` into more idiomatic Rust.
    ///
    /// * `source` -- the current (possibly raw/ugly) Rust source.
    /// * `feedback` -- if `Some`, a counterexample string from a prior failed
    ///   equivalence check. The LLM should use this to correct its rewrite.
    fn rewrite(
        &self,
        source: &str,
        feedback: Option<&str>,
    ) -> Result<LlmSuggestion, DecompileError>;
}

// ---------------------------------------------------------------------------
// Beautification result
// ---------------------------------------------------------------------------

/// Outcome of a single iteration in the beautification loop.
#[derive(Debug, Clone)]
pub(crate) struct IterationOutcome {
    /// The LLM-suggested rewrite for this iteration.
    pub(crate) suggestion: LlmSuggestion,
    /// The equivalence check result for this iteration.
    pub(crate) equivalence: EquivalenceResult,
}

/// Result of the beautification loop.
#[derive(Debug, Clone)]
pub(crate) struct BeautifyResult {
    /// The original decompiled source code (before beautification).
    pub(crate) original_source: String,
    /// The beautified source code. If no equivalent rewrite was found,
    /// this is the same as `original_source`.
    pub(crate) beautified_source: String,
    /// Whether the beautified source was proven equivalent to the original.
    pub(crate) equivalence_proved: bool,
    /// Number of LLM rewrite iterations performed.
    pub(crate) iterations_used: u32,
    /// Per-iteration outcomes (for diagnostics and debugging).
    pub(crate) iteration_history: Vec<IterationOutcome>,
    /// Confidence boost from beautification (0.0 if no improvement accepted).
    pub(crate) confidence_boost: f64,
}

// ---------------------------------------------------------------------------
// Core loop
// ---------------------------------------------------------------------------

/// Run the beautification loop on a decompiled function.
///
/// The loop:
/// 1. Asks the LLM to rewrite the decompiled source.
/// 2. Checks equivalence between the original and the rewrite via z4.
/// 3. If equivalent: accept the rewrite and return.
/// 4. If divergent: feed the counterexample back to the LLM and retry.
/// 5. If unknown: treat as failure and retry without feedback.
/// 6. Repeat up to `config.max_iterations` times.
///
/// If no equivalent rewrite is found within the iteration budget, the
/// original source is returned unchanged.
pub(crate) fn beautify_function(
    func: &DecompiledFunction,
    rewriter: &dyn LlmRewriter,
    checker: &dyn EquivalenceChecker,
    config: &BeautifyConfig,
) -> Result<BeautifyResult, DecompileError> {
    let original = &func.source;
    let mut feedback: Option<String> = None;
    let mut history: Vec<IterationOutcome> = Vec::new();

    for _iter in 0..config.max_iterations {
        // Step 1: Ask LLM for a rewrite
        let suggestion = rewriter.rewrite(original, feedback.as_deref())?;

        // Step 2: Check equivalence
        let equivalence = checker.check_equivalence(original, &suggestion.source)?;

        let outcome =
            IterationOutcome { suggestion: suggestion.clone(), equivalence: equivalence.clone() };
        history.push(outcome);

        match &equivalence.status {
            EquivalenceStatus::Equivalent => {
                // Rewrite is proven equivalent -- accept it.
                let iterations_used = history.len() as u32;
                return Ok(BeautifyResult {
                    original_source: original.clone(),
                    beautified_source: suggestion.source,
                    equivalence_proved: true,
                    iterations_used,
                    iteration_history: history,
                    confidence_boost: 0.2,
                });
            }
            EquivalenceStatus::Divergent { counterexample } => {
                // Feed the counterexample back for the next iteration.
                feedback = Some(counterexample.clone());
            }
            EquivalenceStatus::Unknown { .. } => {
                // No useful feedback -- retry without context.
                feedback = None;
            }
        }
    }

    // Exhausted iteration budget without finding an equivalent rewrite.
    Ok(BeautifyResult {
        original_source: original.clone(),
        beautified_source: original.clone(),
        equivalence_proved: false,
        iterations_used: history.len() as u32,
        iteration_history: history,
        confidence_boost: 0.0,
    })
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // -- Mock LLM that always returns a fixed rewrite -----------------------

    /// Mock LLM rewriter that returns a fixed suggestion on every call.
    #[derive(Debug)]
    struct FixedRewriter {
        suggestion: String,
    }

    impl FixedRewriter {
        fn new(suggestion: impl Into<String>) -> Self {
            Self { suggestion: suggestion.into() }
        }
    }

    impl LlmRewriter for FixedRewriter {
        fn rewrite(
            &self,
            _source: &str,
            _feedback: Option<&str>,
        ) -> Result<LlmSuggestion, DecompileError> {
            Ok(LlmSuggestion {
                source: self.suggestion.clone(),
                explanation: Some("fixed mock rewrite".into()),
            })
        }
    }

    // -- Mock LLM that corrects on the Nth attempt --------------------------

    /// Mock LLM rewriter that returns a bad rewrite until the Nth call,
    /// then returns a good rewrite.
    #[derive(Debug)]
    struct ConvergingRewriter {
        bad_suggestion: String,
        good_suggestion: String,
        converge_at: u32,
        call_count: std::cell::Cell<u32>,
    }

    impl ConvergingRewriter {
        fn new(bad: impl Into<String>, good: impl Into<String>, converge_at: u32) -> Self {
            Self {
                bad_suggestion: bad.into(),
                good_suggestion: good.into(),
                converge_at,
                call_count: std::cell::Cell::new(0),
            }
        }
    }

    impl LlmRewriter for ConvergingRewriter {
        fn rewrite(
            &self,
            _source: &str,
            _feedback: Option<&str>,
        ) -> Result<LlmSuggestion, DecompileError> {
            let count = self.call_count.get() + 1;
            self.call_count.set(count);
            if count >= self.converge_at {
                Ok(LlmSuggestion {
                    source: self.good_suggestion.clone(),
                    explanation: Some(format!("converged on attempt {count}")),
                })
            } else {
                Ok(LlmSuggestion {
                    source: self.bad_suggestion.clone(),
                    explanation: Some(format!("bad attempt {count}")),
                })
            }
        }
    }

    // -- Mock equivalence checker: always equivalent ------------------------

    #[derive(Debug)]
    struct AlwaysEquivalent;

    impl EquivalenceChecker for AlwaysEquivalent {
        fn check_equivalence(
            &self,
            _original: &str,
            _rewritten: &str,
        ) -> Result<EquivalenceResult, DecompileError> {
            Ok(EquivalenceResult { status: EquivalenceStatus::Equivalent, time_ms: 1 })
        }
    }

    // -- Mock equivalence checker: always divergent -------------------------

    #[derive(Debug)]
    struct AlwaysDivergent;

    impl EquivalenceChecker for AlwaysDivergent {
        fn check_equivalence(
            &self,
            _original: &str,
            _rewritten: &str,
        ) -> Result<EquivalenceResult, DecompileError> {
            Ok(EquivalenceResult {
                status: EquivalenceStatus::Divergent {
                    counterexample: "x=42: original returns 21, rewrite returns 20".into(),
                },
                time_ms: 5,
            })
        }
    }

    // -- Mock equivalence checker: equivalent only for specific source ------

    /// Mock checker that considers the rewrite equivalent only if it matches
    /// the `expected_good` string exactly.
    #[derive(Debug)]
    struct SelectiveChecker {
        expected_good: String,
    }

    impl SelectiveChecker {
        fn new(expected_good: impl Into<String>) -> Self {
            Self { expected_good: expected_good.into() }
        }
    }

    impl EquivalenceChecker for SelectiveChecker {
        fn check_equivalence(
            &self,
            _original: &str,
            rewritten: &str,
        ) -> Result<EquivalenceResult, DecompileError> {
            if rewritten == self.expected_good {
                Ok(EquivalenceResult { status: EquivalenceStatus::Equivalent, time_ms: 3 })
            } else {
                Ok(EquivalenceResult {
                    status: EquivalenceStatus::Divergent {
                        counterexample: format!(
                            "rewrite '{}' differs from expected '{}'",
                            rewritten, self.expected_good
                        ),
                    },
                    time_ms: 4,
                })
            }
        }
    }

    // -- Helper to build a minimal DecompiledFunction -----------------------

    fn test_func(source: &str) -> DecompiledFunction {
        DecompiledFunction {
            name: "test_fn".into(),
            params: vec![("a".into(), "u64".into()), ("b".into(), "u64".into())],
            source: source.into(),
            confidence: 0.3,
        }
    }

    // -- Tests --------------------------------------------------------------

    #[test]
    fn test_beautify_accepts_equivalent_rewrite_on_first_try() {
        let func = test_func("fn test_fn(a: u64, b: u64) -> u64 { (a + b) / 2 }");
        let rewriter = FixedRewriter::new("fn test_fn(a: u64, b: u64) -> u64 { a.midpoint(b) }");
        let checker = AlwaysEquivalent;
        let config = BeautifyConfig::default();

        let result = beautify_function(&func, &rewriter, &checker, &config)
            .expect("beautify should succeed");

        assert!(result.equivalence_proved);
        assert_eq!(result.iterations_used, 1);
        assert_eq!(result.beautified_source, "fn test_fn(a: u64, b: u64) -> u64 { a.midpoint(b) }");
        assert!(result.confidence_boost > 0.0);
        assert_eq!(result.iteration_history.len(), 1);
    }

    #[test]
    fn test_beautify_exhausts_budget_when_never_equivalent() {
        let func = test_func("fn test_fn(a: u64, b: u64) -> u64 { (a + b) / 2 }");
        let rewriter = FixedRewriter::new("fn test_fn(a: u64, b: u64) -> u64 { a - b }");
        let checker = AlwaysDivergent;
        let config = BeautifyConfig { max_iterations: 3, ..Default::default() };

        let result = beautify_function(&func, &rewriter, &checker, &config)
            .expect("beautify should succeed");

        assert!(!result.equivalence_proved);
        assert_eq!(result.iterations_used, 3);
        // Original source is returned unchanged.
        assert_eq!(result.beautified_source, result.original_source);
        assert_eq!(result.confidence_boost, 0.0);
        assert_eq!(result.iteration_history.len(), 3);
    }

    #[test]
    fn test_beautify_converges_after_feedback() {
        let good = "fn test_fn(a: u64, b: u64) -> u64 { a.midpoint(b) }";
        let bad = "fn test_fn(a: u64, b: u64) -> u64 { a - b }";

        let func = test_func("fn test_fn(a: u64, b: u64) -> u64 { (a + b) / 2 }");
        let rewriter = ConvergingRewriter::new(bad, good, 3);
        let checker = SelectiveChecker::new(good);
        let config = BeautifyConfig { max_iterations: 5, ..Default::default() };

        let result = beautify_function(&func, &rewriter, &checker, &config)
            .expect("beautify should succeed");

        assert!(result.equivalence_proved);
        assert_eq!(result.iterations_used, 3);
        assert_eq!(result.beautified_source, good);
        assert_eq!(result.iteration_history.len(), 3);

        // First two iterations should have been divergent.
        assert_eq!(
            result.iteration_history[0].equivalence.status,
            EquivalenceStatus::Divergent {
                counterexample: format!("rewrite '{bad}' differs from expected '{good}'"),
            }
        );
        assert_eq!(
            result.iteration_history[1].equivalence.status,
            EquivalenceStatus::Divergent {
                counterexample: format!("rewrite '{bad}' differs from expected '{good}'"),
            }
        );
        // Third iteration converges.
        assert_eq!(result.iteration_history[2].equivalence.status, EquivalenceStatus::Equivalent,);
    }

    #[test]
    fn test_beautify_zero_iterations_returns_original() {
        let func = test_func("fn test_fn(a: u64, b: u64) -> u64 { (a + b) / 2 }");
        let rewriter = FixedRewriter::new("anything");
        let checker = AlwaysEquivalent;
        let config = BeautifyConfig { max_iterations: 0, ..Default::default() };

        let result = beautify_function(&func, &rewriter, &checker, &config)
            .expect("beautify should succeed");

        assert!(!result.equivalence_proved);
        assert_eq!(result.iterations_used, 0);
        assert_eq!(result.beautified_source, func.source);
        assert!(result.iteration_history.is_empty());
    }

    #[test]
    fn test_beautify_config_defaults() {
        let config = BeautifyConfig::default();
        assert_eq!(config.max_iterations, 5);
        assert!(config.prefer_concise);
        assert!(config.prefer_safe_idioms);
        assert!(!config.add_doc_comments);
    }

    #[test]
    fn test_equivalence_status_variants() {
        let eq = EquivalenceStatus::Equivalent;
        assert_eq!(eq, EquivalenceStatus::Equivalent);

        let div = EquivalenceStatus::Divergent { counterexample: "x=1: 3 vs 4".into() };
        assert!(matches!(div, EquivalenceStatus::Divergent { .. }));

        let unk = EquivalenceStatus::Unknown { reason: "timeout".into() };
        assert!(matches!(unk, EquivalenceStatus::Unknown { .. }));
    }

    #[test]
    fn test_beautify_with_unknown_checker() {
        /// Mock checker that always returns Unknown.
        #[derive(Debug)]
        struct AlwaysUnknown;

        impl EquivalenceChecker for AlwaysUnknown {
            fn check_equivalence(
                &self,
                _original: &str,
                _rewritten: &str,
            ) -> Result<EquivalenceResult, DecompileError> {
                Ok(EquivalenceResult {
                    status: EquivalenceStatus::Unknown { reason: "solver timeout".into() },
                    time_ms: 100,
                })
            }
        }

        let func = test_func("fn test_fn(a: u64, b: u64) -> u64 { (a + b) / 2 }");
        let rewriter = FixedRewriter::new("fn test_fn(a: u64, b: u64) -> u64 { a.midpoint(b) }");
        let checker = AlwaysUnknown;
        let config = BeautifyConfig { max_iterations: 2, ..Default::default() };

        let result = beautify_function(&func, &rewriter, &checker, &config)
            .expect("beautify should succeed");

        assert!(!result.equivalence_proved);
        assert_eq!(result.iterations_used, 2);
        assert_eq!(result.beautified_source, func.source);
    }

    #[test]
    fn test_beautify_result_preserves_original() {
        let original = "fn original(x: i32) -> i32 { x + 1 }";
        let func = test_func(original);
        let rewriter = FixedRewriter::new("fn original(x: i32) -> i32 { x.wrapping_add(1) }");
        let checker = AlwaysEquivalent;
        let config = BeautifyConfig::default();

        let result = beautify_function(&func, &rewriter, &checker, &config)
            .expect("beautify should succeed");

        assert_eq!(result.original_source, original);
        assert_ne!(result.beautified_source, original);
    }

    #[test]
    fn test_iteration_history_captures_explanations() {
        let func = test_func("fn f() {}");
        let rewriter = FixedRewriter::new("fn f() { /* beautified */ }");
        let checker = AlwaysEquivalent;
        let config = BeautifyConfig { max_iterations: 1, ..Default::default() };

        let result = beautify_function(&func, &rewriter, &checker, &config)
            .expect("beautify should succeed");

        assert_eq!(result.iteration_history.len(), 1);
        let iter0 = &result.iteration_history[0];
        assert_eq!(iter0.suggestion.explanation.as_deref(), Some("fixed mock rewrite"));
    }
}
