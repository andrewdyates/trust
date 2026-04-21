// trust-router/fallback.rs: Fallback and retry strategies for solver dispatch
//
// tRust: When the primary solver fails (timeout, OOM, unsupported theory),
// this module provides fallback chains that try alternative solvers with
// configurable retry policies and progressive formula simplification.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::sync::Arc;
use std::time::Instant;

use thiserror::Error;
use trust_types::{Formula, VerificationCondition, VerificationResult};

use crate::VerificationBackend;

/// tRust: Classified solver error for retry decisions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum SolverError {
    /// Solver exceeded its time budget.
    Timeout,
    /// Solver ran out of memory.
    OutOfMemory,
    /// Solver does not support the theory or feature used.
    Unsupported,
    /// Internal solver crash or unexpected error.
    InternalError,
    /// Solver returned Unknown with no actionable reason.
    Unknown,
}

impl SolverError {
    /// Classify a `VerificationResult` into a `SolverError`, if applicable.
    ///
    /// Returns `None` for `Proved` and `Failed` (which are not errors).
    #[must_use]
    pub fn from_result(result: &VerificationResult) -> Option<Self> {
        match result {
            VerificationResult::Proved { .. } | VerificationResult::Failed { .. } => None,
            VerificationResult::Timeout { .. } => Some(SolverError::Timeout),
            VerificationResult::Unknown { reason, .. } => {
                let reason_lower = reason.to_lowercase();
                if reason_lower.contains("memory") || reason_lower.contains("oom") {
                    Some(SolverError::OutOfMemory)
                } else if reason_lower.contains("unsupported")
                    || reason_lower.contains("not implemented")
                {
                    Some(SolverError::Unsupported)
                } else if reason_lower.contains("internal") || reason_lower.contains("crash") {
                    Some(SolverError::InternalError)
                } else {
                    Some(SolverError::Unknown)
                }
            }
            _ => None,
        }
    }
}

/// tRust: Fallback execution policy.
#[derive(Debug, Clone, Copy, PartialEq)]
#[non_exhaustive]
#[derive(Default)]
pub enum FallbackPolicy {
    /// Try solvers one at a time in order. Stop on first success.
    #[default]
    Sequential,
    /// Race all solvers in parallel. First definitive result wins.
    ParallelRace,
    /// Sequential with increasing timeouts per attempt.
    AdaptiveTimeout {
        /// Base timeout in ms for the first attempt.
        base_timeout_ms: u64,
        /// Multiplier applied to timeout on each subsequent attempt.
        timeout_multiplier: f64,
    },
}

/// tRust: Backoff strategy for retries.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
#[derive(Default)]
pub enum BackoffStrategy {
    /// No delay between retries.
    #[default]
    None,
    /// Fixed delay (ms) between retries.
    Fixed(u64),
    /// Exponential backoff: delay = base_ms * 2^attempt.
    Exponential { base_ms: u64 },
}

/// tRust: Retry policy controlling how many times and how to retry.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RetryPolicy {
    /// Maximum number of retries (0 = no retries, just the initial attempt).
    pub max_retries: u32,
    /// Backoff strategy between retries.
    pub backoff: BackoffStrategy,
    /// Whether to simplify the formula on retry.
    pub simplify_on_retry: bool,
}

impl Default for RetryPolicy {
    fn default() -> Self {
        Self { max_retries: 2, backoff: BackoffStrategy::None, simplify_on_retry: true }
    }
}

/// tRust: An ordered chain of solver backends to try.
#[derive(Clone)]
pub struct FallbackChain {
    /// Ordered list of backends (first = preferred).
    backends: Vec<Arc<dyn VerificationBackend>>,
    /// Execution policy.
    policy: FallbackPolicy,
    /// Retry policy per backend.
    retry_policy: RetryPolicy,
}

impl FallbackChain {
    /// Create a new fallback chain.
    #[must_use]
    pub fn new(
        backends: Vec<Arc<dyn VerificationBackend>>,
        policy: FallbackPolicy,
        retry_policy: RetryPolicy,
    ) -> Self {
        Self { backends, policy, retry_policy }
    }

    /// Create a simple sequential chain with default retry policy.
    #[must_use]
    pub fn sequential(backends: Vec<Arc<dyn VerificationBackend>>) -> Self {
        Self::new(backends, FallbackPolicy::Sequential, RetryPolicy::default())
    }

    /// Number of backends in the chain.
    #[must_use]
    pub fn len(&self) -> usize {
        self.backends.len()
    }

    /// Whether the chain is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.backends.is_empty()
    }

    /// Access the policy.
    #[must_use]
    pub fn policy(&self) -> FallbackPolicy {
        self.policy
    }
}

/// tRust: Result of a fallback chain execution.
#[derive(Debug, Clone)]
pub struct FallbackResult {
    /// The verification result from the successful solver.
    pub result: VerificationResult,
    /// Which solver produced the result.
    pub solver_used: String,
    /// Number of solver attempts made before success.
    pub attempts: u32,
    /// Total wall-clock time across all attempts (ms).
    pub total_time_ms: u64,
    /// Errors encountered during fallback (solver_name, error).
    pub errors: Vec<(String, SolverError)>,
}

/// tRust: Error from fallback chain execution.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum FallbackError {
    /// All solvers in the chain failed or were exhausted.
    #[error("all {attempted} solvers in fallback chain failed")]
    AllSolversFailed {
        /// Number of solvers attempted.
        attempted: u32,
        /// Errors from each solver.
        errors: Vec<(String, SolverError)>,
        /// Total time spent across all attempts.
        total_time_ms: u64,
    },
    /// The fallback chain was empty.
    #[error("fallback chain is empty — no solvers to try")]
    EmptyChain,
}

// ---------------------------------------------------------------------------
// Execution
// ---------------------------------------------------------------------------

/// tRust: Execute a VC through a fallback chain.
///
/// Tries each backend in order according to the chain's policy. Returns the
/// first definitive result (Proved or Failed), or an error if all solvers fail.
pub fn execute_with_fallback(
    vc: &VerificationCondition,
    chain: &FallbackChain,
) -> Result<FallbackResult, FallbackError> {
    if chain.is_empty() {
        return Err(FallbackError::EmptyChain);
    }

    match chain.policy {
        FallbackPolicy::Sequential => execute_sequential(vc, chain),
        FallbackPolicy::ParallelRace => execute_parallel_race(vc, chain),
        FallbackPolicy::AdaptiveTimeout { base_timeout_ms, timeout_multiplier } => {
            execute_adaptive(vc, chain, base_timeout_ms, timeout_multiplier)
        }
    }
}

/// Sequential fallback: try each backend in order.
fn execute_sequential(
    vc: &VerificationCondition,
    chain: &FallbackChain,
) -> Result<FallbackResult, FallbackError> {
    let start = Instant::now();
    let mut errors = Vec::new();
    let mut attempts: u32 = 0;

    for backend in &chain.backends {
        if !backend.can_handle(vc) {
            continue;
        }

        // Try with retries.
        for retry in 0..=chain.retry_policy.max_retries {
            attempts += 1;
            let query = if retry > 0 && chain.retry_policy.simplify_on_retry {
                let simplified = simplify_for_retry(&vc.formula, retry);
                VerificationCondition {
                    formula: simplified,
                    kind: vc.kind.clone(),
                    function: vc.function.clone(),
                    location: vc.location.clone(),
                    contract_metadata: vc.contract_metadata,
                }
            } else {
                vc.clone()
            };

            let result = backend.verify(&query);
            let was_simplified = retry > 0 && chain.retry_policy.simplify_on_retry;

            if is_definitive(&result) {
                // #781: Over-approximation via simplify_on_retry preserves
                // UNSAT (Proved) but NOT SAT (Failed): a counterexample on
                // a simplified formula may be spurious because Bool(true)
                // substitutions widen the formula's satisfying set.
                // Only accept Proved from simplified formulas; downgrade
                // Failed to Unknown.
                if was_simplified && result.is_failed() {
                    // Spurious counterexample from over-approximated formula.
                    // Treat as Unknown — do not report as definitive failure.
                    let downgraded = VerificationResult::Unknown {
                        solver: backend.name().to_string(),
                        time_ms: result.time_ms(),
                        reason: "Failed on simplified formula (over-approximation may produce spurious CEX)".to_string(),
                    };
                    // Continue trying other backends or retries.
                    errors.push((backend.name().to_string(), SolverError::Unknown));
                    // If this was the last retry, fall through to next backend
                    // with the downgraded result recorded.
                    if retry == chain.retry_policy.max_retries {
                        break;
                    }
                    let _ = downgraded;
                    continue;
                }
                return Ok(FallbackResult {
                    result,
                    solver_used: backend.name().to_string(),
                    attempts,
                    total_time_ms: start.elapsed().as_millis() as u64,
                    errors,
                });
            }

            // Classify the error.
            if let Some(err) = SolverError::from_result(&result) {
                if !should_retry(err, retry, chain.retry_policy.max_retries) {
                    errors.push((backend.name().to_string(), err));
                    break; // Move to next backend.
                }
                errors.push((backend.name().to_string(), err));
                // Apply backoff.
                apply_backoff(chain.retry_policy.backoff, retry);
            }
        }
    }

    Err(FallbackError::AllSolversFailed {
        attempted: attempts,
        errors,
        total_time_ms: start.elapsed().as_millis() as u64,
    })
}

/// Parallel race: try all backends simultaneously, first result wins.
///
/// Uses std::thread for simplicity. For a single backend, falls back to
/// sequential to avoid thread overhead.
fn execute_parallel_race(
    vc: &VerificationCondition,
    chain: &FallbackChain,
) -> Result<FallbackResult, FallbackError> {
    let eligible: Vec<_> = chain.backends.iter().filter(|b| b.can_handle(vc)).cloned().collect();

    if eligible.is_empty() {
        return Err(FallbackError::AllSolversFailed {
            attempted: 0,
            errors: Vec::new(),
            total_time_ms: 0,
        });
    }

    if eligible.len() == 1 {
        // Fall back to sequential for a single backend.
        let single_chain =
            FallbackChain::new(eligible, FallbackPolicy::Sequential, chain.retry_policy);
        return execute_sequential(vc, &single_chain);
    }

    let start = Instant::now();
    let vc_clone = vc.clone();

    // Race using channels.
    let (tx, rx) = std::sync::mpsc::channel();

    for backend in &eligible {
        let backend = Arc::clone(backend);
        let vc_inner = vc_clone.clone();
        let tx = tx.clone();
        std::thread::spawn(move || {
            let result = backend.verify(&vc_inner);
            let name = backend.name().to_string();
            // Ignore send errors (receiver dropped = another thread won).
            let _ = tx.send((name, result));
        });
    }
    // Drop our sender so the channel closes when all threads finish.
    drop(tx);

    let mut errors = Vec::new();
    let mut attempts: u32 = 0;

    for (solver_name, result) in rx {
        attempts += 1;
        if is_definitive(&result) {
            return Ok(FallbackResult {
                result,
                solver_used: solver_name,
                attempts,
                total_time_ms: start.elapsed().as_millis() as u64,
                errors,
            });
        }
        if let Some(err) = SolverError::from_result(&result) {
            errors.push((solver_name, err));
        }
    }

    Err(FallbackError::AllSolversFailed {
        attempted: attempts,
        errors,
        total_time_ms: start.elapsed().as_millis() as u64,
    })
}

/// Adaptive timeout: sequential with increasing timeouts.
fn execute_adaptive(
    vc: &VerificationCondition,
    chain: &FallbackChain,
    base_timeout_ms: u64,
    timeout_multiplier: f64,
) -> Result<FallbackResult, FallbackError> {
    let start = Instant::now();
    let mut errors = Vec::new();
    let mut attempts: u32 = 0;

    for (idx, backend) in chain.backends.iter().enumerate() {
        if !backend.can_handle(vc) {
            continue;
        }

        let _timeout_ms = (base_timeout_ms as f64 * timeout_multiplier.powi(idx as i32)) as u64;
        // Note: actual timeout enforcement would require the backend to
        // respect a timeout parameter. For now we just run the backend
        // and record the result -- the timeout module handles enforcement.
        attempts += 1;
        let result = backend.verify(vc);

        if is_definitive(&result) {
            return Ok(FallbackResult {
                result,
                solver_used: backend.name().to_string(),
                attempts,
                total_time_ms: start.elapsed().as_millis() as u64,
                errors,
            });
        }

        if let Some(err) = SolverError::from_result(&result) {
            errors.push((backend.name().to_string(), err));
        }
    }

    Err(FallbackError::AllSolversFailed {
        attempted: attempts,
        errors,
        total_time_ms: start.elapsed().as_millis() as u64,
    })
}

// ---------------------------------------------------------------------------
// Retry logic
// ---------------------------------------------------------------------------

/// tRust: Decide whether a solver error is worth retrying.
///
/// - Timeout: retry (solver might succeed with simplified formula).
/// - OutOfMemory: retry once (simplification may reduce memory).
/// - Unsupported: never retry (same solver can't learn new theories).
/// - InternalError: retry once (transient errors possible).
/// - Unknown: retry (solver might succeed on retry or with simplification).
#[must_use]
pub fn should_retry(error: SolverError, attempt: u32, max_retries: u32) -> bool {
    if attempt >= max_retries {
        return false;
    }
    match error {
        SolverError::Timeout => true,
        SolverError::OutOfMemory => attempt < 1,
        SolverError::Unsupported => false,
        SolverError::InternalError => attempt < 1,
        SolverError::Unknown => true,
    }
}

/// Apply backoff delay between retries.
fn apply_backoff(strategy: BackoffStrategy, attempt: u32) {
    let delay_ms = match strategy {
        BackoffStrategy::None => 0,
        BackoffStrategy::Fixed(ms) => ms,
        BackoffStrategy::Exponential { base_ms } => base_ms * 2u64.pow(attempt),
    };
    if delay_ms > 0 {
        std::thread::sleep(std::time::Duration::from_millis(delay_ms));
    }
}

// ---------------------------------------------------------------------------
// Formula simplification
// ---------------------------------------------------------------------------

/// tRust: Progressively simplify a formula for retry attempts.
///
/// Each attempt level applies more aggressive simplification:
/// - Attempt 1: Flatten nested And/Or, remove double negation.
/// - Attempt 2+: Replace deep subformulas with `Bool(true)` (over-approximate).
///
/// The simplification is sound for safety properties: we over-approximate,
/// meaning if the simplified formula is proved safe, the original is safe too.
/// However, a counterexample on a simplified formula may be spurious.
#[must_use]
pub fn simplify_for_retry(formula: &Formula, attempt: u32) -> Formula {
    match attempt {
        0 => formula.clone(),
        1 => simplify_flatten(formula),
        _ => simplify_truncate(formula, 10), // Truncate at depth 10.
    }
}

/// Flatten nested And/Or and remove double negation.
fn simplify_flatten(formula: &Formula) -> Formula {
    match formula {
        Formula::Not(inner) => {
            if let Formula::Not(double_inner) = inner.as_ref() {
                simplify_flatten(double_inner)
            } else {
                Formula::Not(Box::new(simplify_flatten(inner)))
            }
        }
        Formula::And(children) => {
            let mut flat = Vec::new();
            for child in children {
                let simplified = simplify_flatten(child);
                // Flatten nested Ands.
                if let Formula::And(inner_children) = simplified {
                    flat.extend(inner_children);
                } else {
                    flat.push(simplified);
                }
            }
            if flat.len() == 1 {
                // SAFETY: len == 1 guarantees .next() returns Some.
                flat.into_iter()
                    .next()
                    .unwrap_or_else(|| unreachable!("empty iter despite len == 1"))
            } else {
                Formula::And(flat)
            }
        }
        Formula::Or(children) => {
            let mut flat = Vec::new();
            for child in children {
                let simplified = simplify_flatten(child);
                if let Formula::Or(inner_children) = simplified {
                    flat.extend(inner_children);
                } else {
                    flat.push(simplified);
                }
            }
            if flat.len() == 1 {
                // SAFETY: len == 1 guarantees .next() returns Some.
                flat.into_iter()
                    .next()
                    .unwrap_or_else(|| unreachable!("empty iter despite len == 1"))
            } else {
                Formula::Or(flat)
            }
        }
        Formula::Implies(a, b) => {
            Formula::Implies(Box::new(simplify_flatten(a)), Box::new(simplify_flatten(b)))
        }
        Formula::Forall(bindings, body) => {
            Formula::Forall(bindings.clone(), Box::new(simplify_flatten(body)))
        }
        Formula::Exists(bindings, body) => {
            Formula::Exists(bindings.clone(), Box::new(simplify_flatten(body)))
        }
        // For all other nodes, return as-is (leaf or non-boolean structure).
        other => other.clone(),
    }
}

/// Truncate formula at a given depth, replacing deeper nodes with
/// polarity-aware booleans that weaken the formula.
fn simplify_truncate(formula: &Formula, max_depth: usize) -> Formula {
    truncate_at_depth(formula, 0, max_depth, true)
}

// tRust #804 P1-10: Track polarity so truncation always over-approximates.
// positive=true means we're in positive polarity (replace with Bool(true) to weaken).
// positive=false means we're in negative polarity (replace with Bool(false) to weaken).
fn truncate_at_depth(formula: &Formula, depth: usize, max_depth: usize, positive: bool) -> Formula {
    if depth >= max_depth {
        // tRust #804 P1-10: Use polarity-aware truncation.
        // Positive polarity: Bool(true) weakens (sound over-approximation).
        // Negative polarity: Bool(false) weakens (sound over-approximation).
        return Formula::Bool(positive);
    }
    match formula {
        Formula::Not(inner) => {
            Formula::Not(Box::new(truncate_at_depth(inner, depth + 1, max_depth, !positive)))
        }
        Formula::And(children) => Formula::And(
            children.iter().map(|c| truncate_at_depth(c, depth + 1, max_depth, positive)).collect(),
        ),
        Formula::Or(children) => Formula::Or(
            children.iter().map(|c| truncate_at_depth(c, depth + 1, max_depth, positive)).collect(),
        ),
        Formula::Implies(a, b) => Formula::Implies(
            Box::new(truncate_at_depth(a, depth + 1, max_depth, !positive)),
            Box::new(truncate_at_depth(b, depth + 1, max_depth, positive)),
        ),
        Formula::Eq(a, b) => Formula::Eq(
            Box::new(truncate_at_depth(a, depth + 1, max_depth, positive)),
            Box::new(truncate_at_depth(b, depth + 1, max_depth, positive)),
        ),
        Formula::Forall(bindings, body) => Formula::Forall(
            bindings.clone(),
            Box::new(truncate_at_depth(body, depth + 1, max_depth, positive)),
        ),
        Formula::Exists(bindings, body) => Formula::Exists(
            bindings.clone(),
            Box::new(truncate_at_depth(body, depth + 1, max_depth, positive)),
        ),
        // Leaves and other nodes: return as-is.
        other => other.clone(),
    }
}

/// Check if a result is definitive (Proved or Failed).
fn is_definitive(result: &VerificationResult) -> bool {
    result.is_proved() || result.is_failed()
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_types::{Formula, ProofStrength, Sort, SourceSpan, VcKind};

    // -----------------------------------------------------------------------
    // Test helpers
    // -----------------------------------------------------------------------

    fn make_vc(formula: Formula) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "test".to_string(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
        }
    }

    /// Backend that always proves.
    struct AlwaysProves;
    impl VerificationBackend for AlwaysProves {
        fn name(&self) -> &str {
            "always-proves"
        }
        fn can_handle(&self, _vc: &VerificationCondition) -> bool {
            true
        }
        fn verify(&self, _vc: &VerificationCondition) -> VerificationResult {
            VerificationResult::Proved {
                solver: "always-proves".to_string(),
                time_ms: 1,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: None,
                solver_warnings: None,
            }
        }
    }

    /// Backend that always times out.
    struct AlwaysTimesOut;
    impl VerificationBackend for AlwaysTimesOut {
        fn name(&self) -> &str {
            "always-timeout"
        }
        fn can_handle(&self, _vc: &VerificationCondition) -> bool {
            true
        }
        fn verify(&self, _vc: &VerificationCondition) -> VerificationResult {
            VerificationResult::Timeout { solver: "always-timeout".to_string(), timeout_ms: 5000 }
        }
    }

    /// Backend that returns Unknown with a reason.
    struct AlwaysUnknown {
        reason: String,
    }
    impl VerificationBackend for AlwaysUnknown {
        fn name(&self) -> &str {
            "always-unknown"
        }
        fn can_handle(&self, _vc: &VerificationCondition) -> bool {
            true
        }
        fn verify(&self, _vc: &VerificationCondition) -> VerificationResult {
            VerificationResult::Unknown {
                solver: "always-unknown".to_string(),
                time_ms: 100,
                reason: self.reason.clone(),
            }
        }
    }

    /// Backend that cannot handle any VC.
    struct CannotHandle;
    impl VerificationBackend for CannotHandle {
        fn name(&self) -> &str {
            "cannot-handle"
        }
        fn can_handle(&self, _vc: &VerificationCondition) -> bool {
            false
        }
        fn verify(&self, _vc: &VerificationCondition) -> VerificationResult {
            unreachable!("should not be called")
        }
    }

    // -----------------------------------------------------------------------
    // SolverError tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_solver_error_from_result_proved() {
        let result = VerificationResult::Proved {
            solver: "z4".into(),
            time_ms: 10,
            strength: ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: None,
        };
        assert!(SolverError::from_result(&result).is_none());
    }

    #[test]
    fn test_solver_error_from_result_failed() {
        let result =
            VerificationResult::Failed { solver: "z4".into(), time_ms: 10, counterexample: None };
        assert!(SolverError::from_result(&result).is_none());
    }

    #[test]
    fn test_solver_error_from_result_timeout() {
        let result = VerificationResult::Timeout { solver: "z4".into(), timeout_ms: 5000 };
        assert_eq!(SolverError::from_result(&result), Some(SolverError::Timeout));
    }

    #[test]
    fn test_solver_error_from_result_oom() {
        let result = VerificationResult::Unknown {
            solver: "z4".into(),
            time_ms: 100,
            reason: "out of memory".into(),
        };
        assert_eq!(SolverError::from_result(&result), Some(SolverError::OutOfMemory));
    }

    #[test]
    fn test_solver_error_from_result_unsupported() {
        let result = VerificationResult::Unknown {
            solver: "z4".into(),
            time_ms: 0,
            reason: "unsupported theory: AUFLIRA".into(),
        };
        assert_eq!(SolverError::from_result(&result), Some(SolverError::Unsupported));
    }

    #[test]
    fn test_solver_error_from_result_internal() {
        let result = VerificationResult::Unknown {
            solver: "z4".into(),
            time_ms: 0,
            reason: "internal error in sat core".into(),
        };
        assert_eq!(SolverError::from_result(&result), Some(SolverError::InternalError));
    }

    #[test]
    fn test_solver_error_from_result_generic_unknown() {
        let result = VerificationResult::Unknown {
            solver: "z4".into(),
            time_ms: 0,
            reason: "incomplete".into(),
        };
        assert_eq!(SolverError::from_result(&result), Some(SolverError::Unknown));
    }

    // -----------------------------------------------------------------------
    // should_retry tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_should_retry_timeout() {
        assert!(should_retry(SolverError::Timeout, 0, 3));
        assert!(should_retry(SolverError::Timeout, 1, 3));
        assert!(!should_retry(SolverError::Timeout, 3, 3));
    }

    #[test]
    fn test_should_retry_oom_only_once() {
        assert!(should_retry(SolverError::OutOfMemory, 0, 3));
        assert!(!should_retry(SolverError::OutOfMemory, 1, 3));
    }

    #[test]
    fn test_should_retry_unsupported_never() {
        assert!(!should_retry(SolverError::Unsupported, 0, 3));
    }

    #[test]
    fn test_should_retry_internal_once() {
        assert!(should_retry(SolverError::InternalError, 0, 3));
        assert!(!should_retry(SolverError::InternalError, 1, 3));
    }

    #[test]
    fn test_should_retry_unknown() {
        assert!(should_retry(SolverError::Unknown, 0, 3));
        assert!(should_retry(SolverError::Unknown, 1, 3));
    }

    // -----------------------------------------------------------------------
    // Simplification tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_simplify_attempt_zero_identity() {
        let f = Formula::Bool(true);
        let result = simplify_for_retry(&f, 0);
        assert_eq!(result, Formula::Bool(true));
    }

    #[test]
    fn test_simplify_flatten_double_negation() {
        let f = Formula::Not(Box::new(Formula::Not(Box::new(Formula::Bool(true)))));
        let result = simplify_for_retry(&f, 1);
        assert_eq!(result, Formula::Bool(true));
    }

    #[test]
    fn test_simplify_flatten_nested_and() {
        let f = Formula::And(vec![
            Formula::And(vec![Formula::Bool(true), Formula::Bool(false)]),
            Formula::Bool(true),
        ]);
        let result = simplify_for_retry(&f, 1);
        match result {
            Formula::And(children) => assert_eq!(children.len(), 3),
            _ => panic!("expected flattened And"),
        }
    }

    #[test]
    fn test_simplify_flatten_nested_or() {
        let f = Formula::Or(vec![
            Formula::Or(vec![Formula::Bool(true), Formula::Bool(false)]),
            Formula::Bool(true),
        ]);
        let result = simplify_for_retry(&f, 1);
        match result {
            Formula::Or(children) => assert_eq!(children.len(), 3),
            _ => panic!("expected flattened Or"),
        }
    }

    #[test]
    fn test_simplify_truncate_deep_formula() {
        // Build a formula of depth > 10.
        let mut f = Formula::Bool(true);
        for _ in 0..15 {
            f = Formula::Not(Box::new(f));
        }
        let result = simplify_for_retry(&f, 2);
        // The result should be truncated -- depth <= 10 means inner nodes
        // past depth 10 become Bool(true).
        fn max_depth(f: &Formula) -> usize {
            match f {
                Formula::Not(inner) => 1 + max_depth(inner),
                _ => 0,
            }
        }
        assert!(max_depth(&result) <= 10);
    }

    #[test]
    fn test_simplify_flatten_single_child_and() {
        let f = Formula::And(vec![Formula::And(vec![Formula::Bool(true)])]);
        let result = simplify_for_retry(&f, 1);
        assert_eq!(result, Formula::Bool(true));
    }

    // -----------------------------------------------------------------------
    // Fallback chain execution tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_execute_empty_chain() {
        let chain = FallbackChain::sequential(vec![]);
        let vc = make_vc(Formula::Bool(true));
        let result = execute_with_fallback(&vc, &chain);
        assert!(matches!(result, Err(FallbackError::EmptyChain)));
    }

    #[test]
    fn test_execute_sequential_first_succeeds() {
        let chain =
            FallbackChain::sequential(vec![Arc::new(AlwaysProves), Arc::new(AlwaysTimesOut)]);
        let vc = make_vc(Formula::Bool(true));
        let result = execute_with_fallback(&vc, &chain).unwrap();
        assert_eq!(result.solver_used, "always-proves");
        assert_eq!(result.attempts, 1);
        assert!(result.result.is_proved());
    }

    #[test]
    fn test_execute_sequential_fallback_to_second() {
        let chain = FallbackChain::new(
            vec![
                Arc::new(AlwaysUnknown { reason: "unsupported feature".into() }),
                Arc::new(AlwaysProves),
            ],
            FallbackPolicy::Sequential,
            RetryPolicy { max_retries: 0, ..Default::default() },
        );
        let vc = make_vc(Formula::Bool(true));
        let result = execute_with_fallback(&vc, &chain).unwrap();
        assert_eq!(result.solver_used, "always-proves");
        assert!(result.errors.iter().any(|(name, _)| name == "always-unknown"));
    }

    #[test]
    fn test_execute_sequential_all_fail() {
        let chain = FallbackChain::new(
            vec![Arc::new(AlwaysTimesOut), Arc::new(AlwaysUnknown { reason: "incomplete".into() })],
            FallbackPolicy::Sequential,
            RetryPolicy { max_retries: 0, ..Default::default() },
        );
        let vc = make_vc(Formula::Bool(true));
        let result = execute_with_fallback(&vc, &chain);
        assert!(matches!(result, Err(FallbackError::AllSolversFailed { .. })));
    }

    #[test]
    fn test_execute_sequential_skip_cannot_handle() {
        let chain = FallbackChain::sequential(vec![Arc::new(CannotHandle), Arc::new(AlwaysProves)]);
        let vc = make_vc(Formula::Bool(true));
        let result = execute_with_fallback(&vc, &chain).unwrap();
        assert_eq!(result.solver_used, "always-proves");
    }

    #[test]
    fn test_execute_parallel_race_first_definitive_wins() {
        let chain = FallbackChain::new(
            vec![Arc::new(AlwaysProves), Arc::new(AlwaysTimesOut)],
            FallbackPolicy::ParallelRace,
            RetryPolicy::default(),
        );
        let vc = make_vc(Formula::Bool(true));
        let result = execute_with_fallback(&vc, &chain).unwrap();
        assert_eq!(result.solver_used, "always-proves");
        assert!(result.result.is_proved());
    }

    #[test]
    fn test_execute_adaptive_timeout() {
        let chain = FallbackChain::new(
            vec![Arc::new(AlwaysTimesOut), Arc::new(AlwaysProves)],
            FallbackPolicy::AdaptiveTimeout { base_timeout_ms: 100, timeout_multiplier: 2.0 },
            RetryPolicy { max_retries: 0, ..Default::default() },
        );
        let vc = make_vc(Formula::Bool(true));
        let result = execute_with_fallback(&vc, &chain).unwrap();
        assert_eq!(result.solver_used, "always-proves");
    }

    #[test]
    fn test_fallback_result_records_errors() {
        let chain = FallbackChain::new(
            vec![
                Arc::new(AlwaysTimesOut),
                Arc::new(AlwaysUnknown { reason: "memory limit exceeded (OOM)".into() }),
                Arc::new(AlwaysProves),
            ],
            FallbackPolicy::Sequential,
            RetryPolicy { max_retries: 0, ..Default::default() },
        );
        let vc = make_vc(Formula::Bool(true));
        let result = execute_with_fallback(&vc, &chain).unwrap();
        assert_eq!(result.solver_used, "always-proves");
        assert!(result.errors.len() >= 2);
    }

    #[test]
    fn test_fallback_chain_len_and_is_empty() {
        let empty = FallbackChain::sequential(vec![]);
        assert!(empty.is_empty());
        assert_eq!(empty.len(), 0);

        let one = FallbackChain::sequential(vec![Arc::new(AlwaysProves)]);
        assert!(!one.is_empty());
        assert_eq!(one.len(), 1);
    }

    #[test]
    fn test_fallback_policy_default() {
        let policy = FallbackPolicy::default();
        assert_eq!(policy, FallbackPolicy::Sequential);
    }

    #[test]
    fn test_fallback_chain_policy_accessor() {
        let chain = FallbackChain::new(
            vec![Arc::new(AlwaysProves)],
            FallbackPolicy::ParallelRace,
            RetryPolicy::default(),
        );
        assert_eq!(chain.policy(), FallbackPolicy::ParallelRace);
    }

    // -----------------------------------------------------------------------
    // #781: Simplified-formula Failed → Unknown downgrade
    // -----------------------------------------------------------------------

    /// Backend that always returns Failed (counterexample found).
    struct AlwaysFails;
    impl VerificationBackend for AlwaysFails {
        fn name(&self) -> &str {
            "always-fails"
        }
        fn can_handle(&self, _vc: &VerificationCondition) -> bool {
            true
        }
        fn verify(&self, _vc: &VerificationCondition) -> VerificationResult {
            VerificationResult::Failed {
                solver: "always-fails".to_string(),
                time_ms: 2,
                counterexample: None,
            }
        }
    }

    #[test]
    fn test_simplified_retry_failed_is_downgraded_to_unknown() {
        // A deeply nested formula that triggers simplification on retry.
        let terms: Vec<Formula> = (0..20).map(|_| Formula::Var("x".into(), Sort::Int)).collect();
        let deep = Formula::And(terms);
        let vc = make_vc(deep);

        let chain = FallbackChain::new(
            vec![Arc::new(AlwaysFails)],
            FallbackPolicy::Sequential,
            RetryPolicy { max_retries: 2, simplify_on_retry: true, backoff: BackoffStrategy::None },
        );

        let result = execute_with_fallback(&vc, &chain);
        // retry=0: original formula, Failed is definitive → returned immediately
        // (the formula is not simplified on the first attempt)
        assert!(result.is_ok(), "fallback chain should succeed");
        let fb = result.unwrap();
        assert!(fb.result.is_failed(), "first attempt on original formula should return Failed");
    }

    #[test]
    fn test_simplified_retry_failed_not_returned_as_definitive_on_retry() {
        // Backend: first call → timeout (forces retry), subsequent calls → Failed.
        // With simplify_on_retry, the Failed on simplified formulas should be
        // downgraded, so the overall result should NOT be Failed.
        use std::sync::atomic::{AtomicUsize, Ordering};

        struct TimeoutThenFails {
            call_count: AtomicUsize,
        }
        impl VerificationBackend for TimeoutThenFails {
            fn name(&self) -> &str {
                "timeout-then-fails"
            }
            fn can_handle(&self, _vc: &VerificationCondition) -> bool {
                true
            }
            fn verify(&self, _vc: &VerificationCondition) -> VerificationResult {
                let n = self.call_count.fetch_add(1, Ordering::SeqCst);
                if n == 0 {
                    // First attempt: timeout → triggers retry
                    VerificationResult::Timeout {
                        solver: "timeout-then-fails".to_string(),
                        timeout_ms: 5000,
                    }
                } else {
                    // Retries: fail (but on simplified formula)
                    VerificationResult::Failed {
                        solver: "timeout-then-fails".to_string(),
                        time_ms: 2,
                        counterexample: None,
                    }
                }
            }
        }

        let terms: Vec<Formula> = (0..20).map(|_| Formula::Var("x".into(), Sort::Int)).collect();
        let deep = Formula::And(terms);
        let vc = make_vc(deep);

        let chain = FallbackChain::new(
            vec![Arc::new(TimeoutThenFails { call_count: AtomicUsize::new(0) })],
            FallbackPolicy::Sequential,
            RetryPolicy { max_retries: 2, simplify_on_retry: true, backoff: BackoffStrategy::None },
        );

        let result = execute_with_fallback(&vc, &chain);
        // retry=0: Timeout → should_retry → retry=1: simplified+Failed → downgraded
        // → retry=2: simplified+Failed → downgraded, breaks out
        // All attempts exhausted with no definitive result → AllBackendsFailed
        assert!(
            result.is_err(),
            "simplified Failed should be downgraded, so no definitive result → error"
        );
    }
}
