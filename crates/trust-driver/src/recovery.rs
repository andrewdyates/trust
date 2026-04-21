// trust-driver/recovery.rs: Error recovery for the verification loop
//
// Classifies verification errors as transient/permanent/resource/configuration,
// tracks retry state with exponential backoff, and recommends recovery actions.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;
use std::time::Duration;

// ---------------------------------------------------------------------------
// Error classification
// ---------------------------------------------------------------------------

/// How an error should be classified for recovery purposes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub(crate) enum ErrorClass {
    /// Transient errors that may resolve on retry (solver timeout, network).
    Transient,
    /// Permanent errors that will not resolve on retry (parse error, unsupported).
    Permanent,
    /// Resource exhaustion (OOM, disk full, too many open files).
    Resource,
    /// Configuration errors (missing solver, bad config file).
    Configuration,
}

/// High-level recovery strategy for a function or VC.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum RecoveryStrategy {
    /// Retry up to N times with backoff.
    Retry(usize),
    /// Skip this function and continue with the rest.
    Skip,
    /// Fall back to a weaker proof level (e.g., L2 -> L1 -> L0).
    Fallback,
    /// Abort the entire verification loop.
    Abort,
}

/// Concrete action the loop should take after consulting the recovery manager.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum RecoveryAction {
    /// Retry after a delay.
    Retry { delay_ms: u64 },
    /// Skip this function and move on.
    SkipFunction,
    /// Reduce the proof level and retry.
    ReduceProofLevel,
    /// Abort the entire loop.
    AbortLoop,
}

// ---------------------------------------------------------------------------
// Error classifier
// ---------------------------------------------------------------------------

/// Classifies error messages into [`ErrorClass`] categories.
///
/// Uses pattern matching on error strings. In production, the verify phase
/// would return structured error types; this classifier bridges the gap
/// for unstructured error output.
pub(crate) struct ErrorClassifier;

impl ErrorClassifier {
    /// Classify an error message string.
    #[must_use]
    pub(crate) fn classify(error_msg: &str) -> ErrorClass {
        let lower = error_msg.to_lowercase();

        // Configuration errors
        if lower.contains("not found")
            || lower.contains("config")
            || lower.contains("missing solver")
            || lower.contains("no such file")
        {
            return ErrorClass::Configuration;
        }

        // Resource exhaustion
        if lower.contains("out of memory")
            || lower.contains("oom")
            || lower.contains("disk full")
            || lower.contains("too many open files")
            || lower.contains("resource exhausted")
        {
            return ErrorClass::Resource;
        }

        // Transient errors
        if lower.contains("timeout")
            || lower.contains("timed out")
            || lower.contains("connection")
            || lower.contains("temporary")
            || lower.contains("try again")
            || lower.contains("busy")
        {
            return ErrorClass::Transient;
        }

        // Default: permanent
        ErrorClass::Permanent
    }

    /// Classify a [`DriverError`](crate::DriverError).
    #[must_use]
    pub(crate) fn classify_driver_error(err: &crate::DriverError) -> ErrorClass {
        match err {
            crate::DriverError::RustcNotFound { .. } => ErrorClass::Configuration,
            crate::DriverError::SourceNotFound { .. } => ErrorClass::Configuration,
            crate::DriverError::CompilerSpawn { .. } => ErrorClass::Configuration,
            crate::DriverError::ConfigRead { .. } => ErrorClass::Configuration,
            crate::DriverError::ConfigParse { .. } => ErrorClass::Configuration,
            crate::DriverError::CompilationFailed { stderr, .. } => {
                Self::classify(stderr)
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Recovery manager
// ---------------------------------------------------------------------------

/// Per-function retry state.
#[derive(Debug, Clone)]
struct RetryState {
    attempts: usize,
    last_class: ErrorClass,
}

/// Manages error recovery across the verification loop.
///
/// Tracks per-function retry counts, applies exponential backoff, and
/// decides when to skip, fall back, or abort.
pub(crate) struct RecoveryManager {
    /// Maximum retries for transient errors.
    max_retries: usize,
    /// Base delay for exponential backoff (in milliseconds).
    base_delay_ms: u64,
    /// Maximum delay cap (in milliseconds).
    max_delay_ms: u64,
    /// Per-function retry tracking.
    state: FxHashMap<String, RetryState>,
    /// Total errors seen across all functions in this loop run.
    total_errors: usize,
    /// Threshold: abort the loop if total errors exceed this.
    abort_threshold: usize,
}

impl RecoveryManager {
    /// Create a new recovery manager with default settings.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            max_retries: 3,
            base_delay_ms: 100,
            max_delay_ms: 5000,
            state: FxHashMap::default(),
            total_errors: 0,
            abort_threshold: 50,
        }
    }

    /// Create a recovery manager with custom limits.
    #[must_use]
    pub(crate) fn with_limits(max_retries: usize, base_delay_ms: u64, abort_threshold: usize) -> Self {
        Self {
            max_retries,
            base_delay_ms,
            max_delay_ms: base_delay_ms.saturating_mul(64),
            state: FxHashMap::default(),
            total_errors: 0,
            abort_threshold,
        }
    }

    /// Record an error for a function and get the recommended recovery action.
    pub(crate) fn on_error(&mut self, function_name: &str, error_class: ErrorClass) -> RecoveryAction {
        self.total_errors += 1;

        // Global abort check.
        if self.total_errors >= self.abort_threshold {
            return RecoveryAction::AbortLoop;
        }

        match error_class {
            ErrorClass::Permanent => RecoveryAction::SkipFunction,
            ErrorClass::Configuration => RecoveryAction::AbortLoop,
            ErrorClass::Resource => RecoveryAction::ReduceProofLevel,
            ErrorClass::Transient => {
                let entry = self
                    .state
                    .entry(function_name.to_string())
                    .or_insert(RetryState {
                        attempts: 0,
                        last_class: error_class,
                    });
                entry.attempts += 1;
                entry.last_class = error_class;

                let attempts = entry.attempts;
                if attempts > self.max_retries {
                    RecoveryAction::SkipFunction
                } else {
                    let delay = self.backoff_delay(attempts);
                    RecoveryAction::Retry { delay_ms: delay }
                }
            }
        }
    }

    /// Get the recommended strategy for an error class.
    #[must_use]
    pub(crate) fn strategy_for(error_class: ErrorClass) -> RecoveryStrategy {
        match error_class {
            ErrorClass::Transient => RecoveryStrategy::Retry(3),
            ErrorClass::Permanent => RecoveryStrategy::Skip,
            ErrorClass::Resource => RecoveryStrategy::Fallback,
            ErrorClass::Configuration => RecoveryStrategy::Abort,
        }
    }

    /// Calculate exponential backoff delay for the given attempt number.
    fn backoff_delay(&self, attempt: usize) -> u64 {
        // 2^(attempt-1) * base_delay, capped at max_delay
        let exp = (attempt as u32).saturating_sub(1);
        let delay = self.base_delay_ms.saturating_mul(2u64.saturating_pow(exp));
        delay.min(self.max_delay_ms)
    }

    /// How many retries remain for a given function.
    #[must_use]
    pub(crate) fn retries_remaining(&self, function_name: &str) -> usize {
        match self.state.get(function_name) {
            Some(s) => self.max_retries.saturating_sub(s.attempts),
            None => self.max_retries,
        }
    }

    /// Total errors seen so far.
    #[must_use]
    pub(crate) fn total_errors(&self) -> usize {
        self.total_errors
    }

    /// Reset state for a new loop run.
    pub(crate) fn reset(&mut self) {
        self.state.clear();
        self.total_errors = 0;
    }

    /// Get the backoff duration for a retry action.
    #[must_use]
    pub(crate) fn retry_duration(action: &RecoveryAction) -> Option<Duration> {
        match action {
            RecoveryAction::Retry { delay_ms } => Some(Duration::from_millis(*delay_ms)),
            _ => None,
        }
    }
}

impl Default for RecoveryManager {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // -- ErrorClassifier tests --

    #[test]
    fn test_classify_timeout_as_transient() {
        assert_eq!(ErrorClassifier::classify("solver timeout after 5s"), ErrorClass::Transient);
    }

    #[test]
    fn test_classify_timed_out_as_transient() {
        assert_eq!(ErrorClassifier::classify("connection timed out"), ErrorClass::Transient);
    }

    #[test]
    fn test_classify_oom_as_resource() {
        assert_eq!(ErrorClassifier::classify("out of memory"), ErrorClass::Resource);
    }

    #[test]
    fn test_classify_disk_full_as_resource() {
        assert_eq!(ErrorClassifier::classify("disk full"), ErrorClass::Resource);
    }

    #[test]
    fn test_classify_not_found_as_configuration() {
        assert_eq!(ErrorClassifier::classify("solver not found"), ErrorClass::Configuration);
    }

    #[test]
    fn test_classify_config_error_as_configuration() {
        assert_eq!(ErrorClassifier::classify("bad config value"), ErrorClass::Configuration);
    }

    #[test]
    fn test_classify_unknown_as_permanent() {
        assert_eq!(ErrorClassifier::classify("unsupported feature"), ErrorClass::Permanent);
    }

    #[test]
    fn test_classify_case_insensitive() {
        assert_eq!(ErrorClassifier::classify("TIMEOUT exceeded"), ErrorClass::Transient);
        assert_eq!(ErrorClassifier::classify("OUT OF MEMORY"), ErrorClass::Resource);
    }

    #[test]
    fn test_classify_driver_error_rustc_not_found() {
        let err = crate::DriverError::RustcNotFound { path: "/bad".into() };
        assert_eq!(ErrorClassifier::classify_driver_error(&err), ErrorClass::Configuration);
    }

    #[test]
    fn test_classify_driver_error_compilation_timeout() {
        let err = crate::DriverError::CompilationFailed {
            exit_code: Some(1),
            stderr: "solver timeout after 30s".into(),
        };
        assert_eq!(ErrorClassifier::classify_driver_error(&err), ErrorClass::Transient);
    }

    #[test]
    fn test_classify_driver_error_compilation_permanent() {
        let err = crate::DriverError::CompilationFailed {
            exit_code: Some(1),
            stderr: "type mismatch in assertion".into(),
        };
        assert_eq!(ErrorClassifier::classify_driver_error(&err), ErrorClass::Permanent);
    }

    // -- RecoveryStrategy tests --

    #[test]
    fn test_strategy_for_transient() {
        assert_eq!(RecoveryManager::strategy_for(ErrorClass::Transient), RecoveryStrategy::Retry(3));
    }

    #[test]
    fn test_strategy_for_permanent() {
        assert_eq!(RecoveryManager::strategy_for(ErrorClass::Permanent), RecoveryStrategy::Skip);
    }

    #[test]
    fn test_strategy_for_resource() {
        assert_eq!(RecoveryManager::strategy_for(ErrorClass::Resource), RecoveryStrategy::Fallback);
    }

    #[test]
    fn test_strategy_for_configuration() {
        assert_eq!(RecoveryManager::strategy_for(ErrorClass::Configuration), RecoveryStrategy::Abort);
    }

    // -- RecoveryManager tests --

    #[test]
    fn test_recovery_manager_transient_retries_with_backoff() {
        let mut mgr = RecoveryManager::with_limits(3, 100, 50);

        // First transient error -> retry with base delay.
        let action = mgr.on_error("fn_a", ErrorClass::Transient);
        assert_eq!(action, RecoveryAction::Retry { delay_ms: 100 });

        // Second -> 200ms.
        let action = mgr.on_error("fn_a", ErrorClass::Transient);
        assert_eq!(action, RecoveryAction::Retry { delay_ms: 200 });

        // Third -> 400ms.
        let action = mgr.on_error("fn_a", ErrorClass::Transient);
        assert_eq!(action, RecoveryAction::Retry { delay_ms: 400 });

        // Fourth exceeds limit -> skip.
        let action = mgr.on_error("fn_a", ErrorClass::Transient);
        assert_eq!(action, RecoveryAction::SkipFunction);
    }

    #[test]
    fn test_recovery_manager_permanent_skips_immediately() {
        let mut mgr = RecoveryManager::new();
        let action = mgr.on_error("fn_b", ErrorClass::Permanent);
        assert_eq!(action, RecoveryAction::SkipFunction);
    }

    #[test]
    fn test_recovery_manager_configuration_aborts() {
        let mut mgr = RecoveryManager::new();
        let action = mgr.on_error("fn_c", ErrorClass::Configuration);
        assert_eq!(action, RecoveryAction::AbortLoop);
    }

    #[test]
    fn test_recovery_manager_resource_reduces_level() {
        let mut mgr = RecoveryManager::new();
        let action = mgr.on_error("fn_d", ErrorClass::Resource);
        assert_eq!(action, RecoveryAction::ReduceProofLevel);
    }

    #[test]
    fn test_recovery_manager_abort_threshold() {
        let mut mgr = RecoveryManager::with_limits(100, 100, 3);

        mgr.on_error("fn_1", ErrorClass::Transient);
        mgr.on_error("fn_2", ErrorClass::Transient);
        let action = mgr.on_error("fn_3", ErrorClass::Transient);
        assert_eq!(action, RecoveryAction::AbortLoop);
    }

    #[test]
    fn test_recovery_manager_per_function_tracking() {
        let mut mgr = RecoveryManager::with_limits(2, 100, 50);

        // fn_a: 1 attempt.
        mgr.on_error("fn_a", ErrorClass::Transient);
        assert_eq!(mgr.retries_remaining("fn_a"), 1);

        // fn_b: 0 attempts.
        assert_eq!(mgr.retries_remaining("fn_b"), 2);

        // fn_a: 2 attempts -> exhausted.
        mgr.on_error("fn_a", ErrorClass::Transient);
        assert_eq!(mgr.retries_remaining("fn_a"), 0);
    }

    #[test]
    fn test_recovery_manager_reset() {
        let mut mgr = RecoveryManager::new();
        mgr.on_error("fn_a", ErrorClass::Transient);
        mgr.on_error("fn_b", ErrorClass::Permanent);
        assert_eq!(mgr.total_errors(), 2);

        mgr.reset();
        assert_eq!(mgr.total_errors(), 0);
        assert_eq!(mgr.retries_remaining("fn_a"), 3);
    }

    #[test]
    fn test_recovery_manager_default() {
        let mgr = RecoveryManager::default();
        assert_eq!(mgr.total_errors(), 0);
        assert_eq!(mgr.retries_remaining("anything"), 3);
    }

    #[test]
    fn test_retry_duration() {
        let action = RecoveryAction::Retry { delay_ms: 250 };
        assert_eq!(
            RecoveryManager::retry_duration(&action),
            Some(Duration::from_millis(250))
        );

        let skip = RecoveryAction::SkipFunction;
        assert_eq!(RecoveryManager::retry_duration(&skip), None);
    }

    #[test]
    fn test_backoff_delay_caps_at_max() {
        let mgr = RecoveryManager::with_limits(10, 100, 50);
        // max_delay = 100 * 64 = 6400
        let delay = mgr.backoff_delay(20);
        assert!(delay <= 6400, "delay {delay} should be capped at max");
    }
}
