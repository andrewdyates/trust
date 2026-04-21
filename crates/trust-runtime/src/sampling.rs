// trust-runtime/sampling.rs: Configurable sampling for runtime checks
//
// In hot paths, running every runtime check on every invocation is too
// expensive. This module provides sampling wrappers that execute checks
// probabilistically, with adaptive rate increases on failure.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};

use crate::RuntimeCheck;

// ---------------------------------------------------------------------------
// SamplingConfig
// ---------------------------------------------------------------------------

/// Configuration for runtime check sampling.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub(crate) struct SamplingConfig {
    /// Base sampling rate in `[0.0, 1.0]`. 1.0 = always check, 0.0 = never.
    pub rate: f64,
    /// Seed for the deterministic PRNG (reproducible sampling).
    pub seed: u64,
    /// Whether to adaptively increase the rate on failures.
    pub adaptive: bool,
}

impl SamplingConfig {
    /// Create a config that always checks (rate = 1.0, no adaptation).
    #[must_use]
    pub(crate) fn always() -> Self {
        Self {
            rate: 1.0,
            seed: 0,
            adaptive: false,
        }
    }

    /// Create a config with the given rate and default seed.
    #[must_use]
    pub(crate) fn with_rate(rate: f64) -> Self {
        Self {
            rate: rate.clamp(0.0, 1.0),
            seed: 0,
            adaptive: false,
        }
    }

    /// Enable adaptive sampling.
    #[must_use]
    pub(crate) fn with_adaptive(mut self) -> Self {
        self.adaptive = true;
        self
    }

    /// Set the PRNG seed.
    #[must_use]
    pub(crate) fn with_seed(mut self, seed: u64) -> Self {
        self.seed = seed;
        self
    }
}

impl Default for SamplingConfig {
    fn default() -> Self {
        Self::always()
    }
}

// ---------------------------------------------------------------------------
// SampledCheck
// ---------------------------------------------------------------------------

/// A runtime check wrapped with sampling configuration.
///
/// On each invocation, the check is executed with probability `config.rate`.
/// If the check fails and `config.adaptive` is true, the rate is increased
/// toward 1.0 to catch more failures.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct SampledCheck {
    /// The underlying runtime check.
    pub check: RuntimeCheck,
    /// Sampling configuration.
    pub config: SamplingConfig,
    /// Current effective rate (may differ from config.rate if adaptive).
    pub effective_rate: f64,
    /// Total number of invocations.
    pub invocation_count: u64,
    /// Number of times the check was actually executed.
    pub execution_count: u64,
    /// Number of failures observed.
    pub failure_count: u64,
}

impl SampledCheck {
    /// Wrap a runtime check with sampling.
    #[must_use]
    pub(crate) fn new(check: RuntimeCheck, config: SamplingConfig) -> Self {
        let effective_rate = config.rate;
        Self {
            check,
            config,
            effective_rate,
            invocation_count: 0,
            execution_count: 0,
            failure_count: 0,
        }
    }

    /// Decide whether to execute the check on this invocation.
    ///
    /// Uses a simple deterministic hash of (seed, invocation_count) to decide.
    /// Returns true if the check should be executed.
    #[must_use]
    pub(crate) fn should_execute(&mut self) -> bool {
        self.invocation_count += 1;

        if self.effective_rate >= 1.0 {
            self.execution_count += 1;
            return true;
        }
        if self.effective_rate <= 0.0 {
            return false;
        }

        // Simple deterministic PRNG: hash seed with invocation count.
        let hash = deterministic_hash(self.config.seed, self.invocation_count);
        let threshold = (self.effective_rate * u64::MAX as f64) as u64;
        let execute = hash <= threshold;

        if execute {
            self.execution_count += 1;
        }
        execute
    }

    /// Record a check failure. If adaptive, increases the effective rate.
    pub(crate) fn record_failure(&mut self) {
        self.failure_count += 1;
        if self.config.adaptive {
            // Double the effective rate toward 1.0 on each failure.
            self.effective_rate = (self.effective_rate * 2.0).min(1.0);
        }
    }

    /// Record a check success. Does not change the rate.
    pub(crate) fn record_success(&mut self) {
        // Adaptive sampling only reacts to failures, not successes.
        // The rate stays elevated until reset.
    }

    /// Reset the effective rate to the base config rate.
    pub(crate) fn reset_rate(&mut self) {
        self.effective_rate = self.config.rate;
    }

    /// The ratio of executions to invocations (actual sampling ratio).
    #[must_use]
    pub(crate) fn actual_rate(&self) -> f64 {
        if self.invocation_count == 0 {
            0.0
        } else {
            self.execution_count as f64 / self.invocation_count as f64
        }
    }
}

// ---------------------------------------------------------------------------
// AdaptiveSampler
// ---------------------------------------------------------------------------

/// Manages a collection of sampled checks with adaptive rate adjustment.
///
/// Tracks global failure state and can boost all sampling rates when
/// failures are detected in any check.
pub(crate) struct AdaptiveSampler {
    /// The sampled checks being managed.
    pub checks: Vec<SampledCheck>,
    /// Global failure count across all checks.
    pub total_failures: u64,
    /// The boost factor applied when any check fails.
    boost_factor: f64,
}

impl AdaptiveSampler {
    /// Create a new adaptive sampler with the given checks.
    #[must_use]
    pub(crate) fn new(checks: Vec<SampledCheck>) -> Self {
        Self {
            checks,
            total_failures: 0,
            boost_factor: 2.0,
        }
    }

    /// Set the boost factor for adaptive rate increases (default 2.0).
    #[must_use]
    pub(crate) fn with_boost_factor(mut self, factor: f64) -> Self {
        self.boost_factor = factor.max(1.0);
        self
    }

    /// Record a failure for the check at the given index.
    ///
    /// Boosts the failed check's rate and optionally boosts nearby checks.
    pub(crate) fn record_failure(&mut self, check_index: usize) {
        self.total_failures += 1;
        if let Some(sc) = self.checks.get_mut(check_index) {
            sc.record_failure();
        }
        // Boost all checks in the same function as the failed check.
        if let Some(failed_fn) = self.checks.get(check_index).map(|sc| sc.check.function.clone()) {
            for sc in &mut self.checks {
                if sc.check.function == failed_fn {
                    sc.effective_rate = (sc.effective_rate * self.boost_factor).min(1.0);
                }
            }
        }
    }

    /// Reset all check rates to their base configuration.
    pub(crate) fn reset_all_rates(&mut self) {
        for sc in &mut self.checks {
            sc.reset_rate();
        }
    }

    /// Summary of sampling state.
    #[must_use]
    pub(crate) fn summary(&self) -> SamplingSummary {
        let total_invocations: u64 = self.checks.iter().map(|sc| sc.invocation_count).sum();
        let total_executions: u64 = self.checks.iter().map(|sc| sc.execution_count).sum();
        let checks_at_full_rate = self.checks.iter().filter(|sc| sc.effective_rate >= 1.0).count();

        SamplingSummary {
            total_checks: self.checks.len(),
            total_invocations,
            total_executions,
            total_failures: self.total_failures,
            checks_at_full_rate,
        }
    }
}

/// Summary statistics for the adaptive sampler.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct SamplingSummary {
    /// Total number of sampled checks.
    pub total_checks: usize,
    /// Total invocations across all checks.
    pub total_invocations: u64,
    /// Total actual executions across all checks.
    pub total_executions: u64,
    /// Total failures observed.
    pub total_failures: u64,
    /// Number of checks currently at rate 1.0.
    pub checks_at_full_rate: usize,
}

// ---------------------------------------------------------------------------
// Deterministic PRNG
// ---------------------------------------------------------------------------

/// Simple deterministic hash for sampling decisions.
/// Uses a variant of splitmix64 for speed and reproducibility.
fn deterministic_hash(seed: u64, counter: u64) -> u64 {
    let mut x = seed.wrapping_add(counter.wrapping_mul(0x9E37_79B9_7F4A_7C15));
    x = (x ^ (x >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    x = (x ^ (x >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    x ^ (x >> 31)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CheckKind, CheckStrategy, RuntimeCheck};
    use trust_types::SourceSpan;

    fn span() -> SourceSpan {
        SourceSpan {
            file: "src/lib.rs".to_string(),
            line_start: 10,
            col_start: 5,
            line_end: 10,
            col_end: 20,
        }
    }

    fn make_check(function: &str) -> RuntimeCheck {
        RuntimeCheck {
            kind: CheckKind::IndexOutOfBounds,
            location: span(),
            description: "test check".to_string(),
            strategy: CheckStrategy::BoundsCheck,
            function: function.to_string(),
        }
    }

    // -----------------------------------------------------------------------
    // SamplingConfig
    // -----------------------------------------------------------------------

    #[test]
    fn test_config_always() {
        let config = SamplingConfig::always();
        assert!((config.rate - 1.0).abs() < f64::EPSILON);
        assert!(!config.adaptive);
    }

    #[test]
    fn test_config_with_rate_clamps() {
        let config = SamplingConfig::with_rate(1.5);
        assert!((config.rate - 1.0).abs() < f64::EPSILON);

        let config = SamplingConfig::with_rate(-0.5);
        assert!(config.rate.abs() < f64::EPSILON);
    }

    #[test]
    fn test_config_builder() {
        let config = SamplingConfig::with_rate(0.5).with_adaptive().with_seed(42);
        assert!((config.rate - 0.5).abs() < f64::EPSILON);
        assert!(config.adaptive);
        assert_eq!(config.seed, 42);
    }

    #[test]
    fn test_config_default_is_always() {
        let config = SamplingConfig::default();
        assert!((config.rate - 1.0).abs() < f64::EPSILON);
    }

    // -----------------------------------------------------------------------
    // SampledCheck
    // -----------------------------------------------------------------------

    #[test]
    fn test_sampled_check_always_executes_at_rate_one() {
        let check = make_check("f");
        let mut sc = SampledCheck::new(check, SamplingConfig::always());

        for _ in 0..100 {
            assert!(sc.should_execute());
        }
        assert_eq!(sc.invocation_count, 100);
        assert_eq!(sc.execution_count, 100);
    }

    #[test]
    fn test_sampled_check_never_executes_at_rate_zero() {
        let check = make_check("f");
        let mut sc = SampledCheck::new(check, SamplingConfig::with_rate(0.0));

        for _ in 0..100 {
            assert!(!sc.should_execute());
        }
        assert_eq!(sc.invocation_count, 100);
        assert_eq!(sc.execution_count, 0);
    }

    #[test]
    fn test_sampled_check_partial_rate() {
        let check = make_check("f");
        let config = SamplingConfig::with_rate(0.5).with_seed(12345);
        let mut sc = SampledCheck::new(check, config);

        for _ in 0..1000 {
            let _ = sc.should_execute();
        }
        // With 50% rate over 1000 invocations, we expect roughly 500 executions.
        // Allow wide margin for hash distribution.
        assert!(sc.execution_count > 300, "too few executions: {}", sc.execution_count);
        assert!(sc.execution_count < 700, "too many executions: {}", sc.execution_count);
    }

    #[test]
    fn test_sampled_check_deterministic() {
        let config = SamplingConfig::with_rate(0.3).with_seed(42);

        let check1 = make_check("f");
        let mut sc1 = SampledCheck::new(check1, config.clone());

        let check2 = make_check("f");
        let mut sc2 = SampledCheck::new(check2, config);

        let results1: Vec<bool> = (0..100).map(|_| sc1.should_execute()).collect();
        let results2: Vec<bool> = (0..100).map(|_| sc2.should_execute()).collect();

        assert_eq!(results1, results2, "same seed should produce same decisions");
    }

    #[test]
    fn test_sampled_check_adaptive_increases_rate() {
        let check = make_check("f");
        let config = SamplingConfig::with_rate(0.1).with_adaptive();
        let mut sc = SampledCheck::new(check, config);

        assert!((sc.effective_rate - 0.1).abs() < f64::EPSILON);

        sc.record_failure();
        assert!((sc.effective_rate - 0.2).abs() < f64::EPSILON);

        sc.record_failure();
        assert!((sc.effective_rate - 0.4).abs() < f64::EPSILON);

        sc.record_failure();
        assert!((sc.effective_rate - 0.8).abs() < f64::EPSILON);

        sc.record_failure();
        assert!((sc.effective_rate - 1.0).abs() < f64::EPSILON);

        // Should cap at 1.0
        sc.record_failure();
        assert!((sc.effective_rate - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_sampled_check_non_adaptive_no_rate_change() {
        let check = make_check("f");
        let config = SamplingConfig::with_rate(0.5);
        let mut sc = SampledCheck::new(check, config);

        sc.record_failure();
        assert!((sc.effective_rate - 0.5).abs() < f64::EPSILON);
    }

    #[test]
    fn test_sampled_check_reset_rate() {
        let check = make_check("f");
        let config = SamplingConfig::with_rate(0.1).with_adaptive();
        let mut sc = SampledCheck::new(check, config);

        sc.record_failure();
        sc.record_failure();
        assert!((sc.effective_rate - 0.4).abs() < f64::EPSILON);

        sc.reset_rate();
        assert!((sc.effective_rate - 0.1).abs() < f64::EPSILON);
    }

    #[test]
    fn test_sampled_check_actual_rate() {
        let check = make_check("f");
        let mut sc = SampledCheck::new(check, SamplingConfig::always());

        assert!(sc.actual_rate().abs() < f64::EPSILON); // 0/0 = 0.0

        for _ in 0..10 {
            let _ = sc.should_execute();
        }
        assert!((sc.actual_rate() - 1.0).abs() < f64::EPSILON);
    }

    // -----------------------------------------------------------------------
    // AdaptiveSampler
    // -----------------------------------------------------------------------

    #[test]
    fn test_adaptive_sampler_record_failure_boosts_same_function() {
        let sc1 = SampledCheck::new(
            make_check("hot_fn"),
            SamplingConfig::with_rate(0.1).with_adaptive(),
        );
        let sc2 = SampledCheck::new(
            make_check("hot_fn"),
            SamplingConfig::with_rate(0.1).with_adaptive(),
        );
        let sc3 = SampledCheck::new(
            make_check("other_fn"),
            SamplingConfig::with_rate(0.1).with_adaptive(),
        );

        let mut sampler = AdaptiveSampler::new(vec![sc1, sc2, sc3]);
        sampler.record_failure(0); // Failure in hot_fn

        // Both hot_fn checks should be boosted
        assert!(sampler.checks[0].effective_rate > 0.1);
        assert!(sampler.checks[1].effective_rate > 0.1);
        // other_fn should stay the same
        assert!((sampler.checks[2].effective_rate - 0.1).abs() < f64::EPSILON);
        assert_eq!(sampler.total_failures, 1);
    }

    #[test]
    fn test_adaptive_sampler_reset_all() {
        let sc1 = SampledCheck::new(
            make_check("f"),
            SamplingConfig::with_rate(0.1).with_adaptive(),
        );
        let sc2 = SampledCheck::new(
            make_check("f"),
            SamplingConfig::with_rate(0.2).with_adaptive(),
        );

        let mut sampler = AdaptiveSampler::new(vec![sc1, sc2]);
        sampler.record_failure(0);
        sampler.record_failure(1);

        sampler.reset_all_rates();
        assert!((sampler.checks[0].effective_rate - 0.1).abs() < f64::EPSILON);
        assert!((sampler.checks[1].effective_rate - 0.2).abs() < f64::EPSILON);
    }

    #[test]
    fn test_adaptive_sampler_summary() {
        let mut sc1 = SampledCheck::new(make_check("f"), SamplingConfig::always());
        for _ in 0..10 {
            let _ = sc1.should_execute();
        }

        let mut sc2 = SampledCheck::new(make_check("g"), SamplingConfig::with_rate(0.0));
        for _ in 0..5 {
            let _ = sc2.should_execute();
        }

        let sampler = AdaptiveSampler::new(vec![sc1, sc2]);
        let summary = sampler.summary();

        assert_eq!(summary.total_checks, 2);
        assert_eq!(summary.total_invocations, 15);
        assert_eq!(summary.total_executions, 10);
        assert_eq!(summary.total_failures, 0);
        assert_eq!(summary.checks_at_full_rate, 1);
    }

    #[test]
    fn test_adaptive_sampler_custom_boost_factor() {
        let sc = SampledCheck::new(
            make_check("f"),
            SamplingConfig::with_rate(0.1).with_adaptive(),
        );

        let mut sampler = AdaptiveSampler::new(vec![sc]).with_boost_factor(3.0);
        sampler.record_failure(0);

        // With boost_factor=3.0, one failure should triple the rate: 0.1 * 3.0 = 0.3
        // The check's own record_failure doubles it (0.2), then the global boost
        // applies 3.0x to the already-doubled rate: 0.2 * 3.0 = 0.6
        assert!(sampler.checks[0].effective_rate > 0.1);
    }

    #[test]
    fn test_adaptive_sampler_out_of_bounds_failure() {
        let sc = SampledCheck::new(make_check("f"), SamplingConfig::always());
        let mut sampler = AdaptiveSampler::new(vec![sc]);

        // Should not panic on invalid index.
        sampler.record_failure(999);
        assert_eq!(sampler.total_failures, 1);
    }

    // -----------------------------------------------------------------------
    // Serialization
    // -----------------------------------------------------------------------

    #[test]
    fn test_sampling_config_serialization_roundtrip() {
        let config = SamplingConfig::with_rate(0.75).with_adaptive().with_seed(42);
        let json = serde_json::to_string(&config).expect("serialize");
        let roundtrip: SamplingConfig = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(roundtrip, config);
    }

    #[test]
    fn test_sampled_check_serialization_roundtrip() {
        let sc = SampledCheck::new(make_check("f"), SamplingConfig::with_rate(0.5));
        let json = serde_json::to_string(&sc).expect("serialize");
        let roundtrip: SampledCheck = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(roundtrip.config, sc.config);
        assert_eq!(roundtrip.effective_rate, sc.effective_rate);
    }

    #[test]
    fn test_summary_serialization_roundtrip() {
        let summary = SamplingSummary {
            total_checks: 10,
            total_invocations: 1000,
            total_executions: 500,
            total_failures: 3,
            checks_at_full_rate: 2,
        };
        let json = serde_json::to_string(&summary).expect("serialize");
        let roundtrip: SamplingSummary = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(roundtrip, summary);
    }
}
