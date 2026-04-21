// trust-convergence/src/acceleration.rs — Convergence acceleration methods
//
// Part of #269: Add convergence acceleration to trust-convergence
//
// Numerical acceleration techniques to speed up convergence of the
// prove-strengthen-backpropagate loop. No external dependencies — pure math on f64.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

/// Strategy for accelerating convergence of a scalar sequence.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum AccelerationStrategy {
    /// No acceleration — use raw values.
    None,
    /// Aitken's delta-squared method. Effective for linearly converging sequences.
    AitkenDeltaSquared,
    /// Richardson extrapolation. Cancels leading error terms of order `p`.
    Richardson,
    /// Adaptive relaxation with dynamic factor that decreases on oscillation.
    AdaptiveRelaxation,
}

/// Configuration for convergence acceleration.
#[derive(Debug, Clone)]
pub(crate) struct AccelerationConfig {
    /// Which acceleration strategy to apply.
    pub strategy: AccelerationStrategy,
    /// Relaxation factor for `AdaptiveRelaxation` (0.0, 1.0].
    pub relaxation_factor: f64,
    /// Maximum number of extrapolation steps for iterative methods.
    pub max_extrapolation_steps: usize,
    /// Threshold for oscillation detection (ratio of sign changes).
    pub oscillation_threshold: f64,
}

impl Default for AccelerationConfig {
    fn default() -> Self {
        Self {
            strategy: AccelerationStrategy::None,
            relaxation_factor: 0.8,
            max_extrapolation_steps: 5,
            oscillation_threshold: 0.6,
        }
    }
}

/// Result of applying an acceleration method to a sequence.
#[derive(Debug, Clone)]
pub(crate) struct AccelerationResult {
    /// The accelerated (extrapolated or relaxed) value.
    pub accelerated_value: f64,
    /// The most recent raw value from the input sequence.
    pub original_value: f64,
    /// Absolute improvement: `|accelerated - original|`.
    pub improvement: f64,
    /// Whether the accelerated value appears to have converged.
    pub converged: bool,
}

/// Aitken's delta-squared extrapolation.
///
/// Uses the last three values `[s_n, s_{n+1}, s_{n+2}]` to estimate the limit:
///   `s* = s_n - (s_{n+1} - s_n)^2 / (s_{n+2} - 2*s_{n+1} + s_n)`
///
/// Returns `None` if the denominator vanishes or fewer than 3 values are provided.
#[must_use]
pub(crate) fn aitken_extrapolate(values: &[f64]) -> Option<f64> {
    if values.len() < 3 {
        return None;
    }
    let n = values.len();
    let (s0, s1, s2) = (values[n - 3], values[n - 2], values[n - 1]);
    let denom = s2 - 2.0 * s1 + s0;
    if denom.abs() < f64::EPSILON {
        return None;
    }
    Some(s0 - (s1 - s0) * (s1 - s0) / denom)
}

/// Richardson extrapolation of order `p`.
///
/// Given the last two values `[a_h, a_{h/2}]`, computes:
///   `a* = (2^p * a_{h/2} - a_h) / (2^p - 1)`
///
/// Returns `None` if fewer than 2 values are provided or `order` is 0.
#[must_use]
pub(crate) fn richardson_extrapolate(values: &[f64], order: u32) -> Option<f64> {
    if values.len() < 2 || order == 0 {
        return None;
    }
    let n = values.len();
    let (a_coarse, a_fine) = (values[n - 2], values[n - 1]);
    let two_p = 2.0_f64.powi(order as i32);
    Some((two_p * a_fine - a_coarse) / (two_p - 1.0))
}

/// Adaptive relaxation: `factor * current + (1 - factor) * previous`.
///
/// `factor` is clamped to `[0.0, 1.0]`.
#[must_use]
pub(crate) fn adaptive_relax(current: f64, previous: f64, factor: f64) -> f64 {
    let f = factor.clamp(0.0, 1.0);
    f * current + (1.0 - f) * previous
}

/// Detect oscillation by counting sign changes in consecutive differences.
///
/// Returns `true` if the ratio of sign changes exceeds `threshold`.
/// Requires at least 3 values; returns `false` for shorter sequences.
#[must_use]
pub(crate) fn detect_oscillation(values: &[f64], threshold: f64) -> bool {
    if values.len() < 3 {
        return false;
    }
    let diffs: Vec<f64> = values.windows(2).map(|w| w[1] - w[0]).collect();
    if diffs.len() < 2 {
        return false;
    }
    let sign_changes = diffs
        .windows(2)
        .filter(|w| {
            let (a, b) = (w[0], w[1]);
            a.abs() >= f64::EPSILON && b.abs() >= f64::EPSILON && a.signum() != b.signum()
        })
        .count();
    let possible = diffs.len() - 1;
    if possible == 0 {
        return false;
    }
    (sign_changes as f64 / possible as f64) > threshold
}

/// Apply the configured acceleration strategy to a sequence of convergence
/// scores. Falls back to the last raw value if the method is inapplicable.
#[must_use]
pub(crate) fn accelerate(values: &[f64], config: &AccelerationConfig) -> AccelerationResult {
    if values.is_empty() {
        return AccelerationResult {
            accelerated_value: 0.0,
            original_value: 0.0,
            improvement: 0.0,
            converged: false,
        };
    }
    // SAFETY: We returned early above if values.is_empty().
    let original = *values.last()
        .unwrap_or_else(|| unreachable!("values empty after non-empty check"));
    let accelerated = match config.strategy {
        AccelerationStrategy::None => original,
        AccelerationStrategy::AitkenDeltaSquared => {
            aitken_extrapolate(values).unwrap_or(original)
        }
        AccelerationStrategy::Richardson => {
            // Default to first-order; callers needing higher order use
            // `richardson_extrapolate` directly.
            richardson_extrapolate(values, 1).unwrap_or(original)
        }
        AccelerationStrategy::AdaptiveRelaxation => {
            if values.len() < 2 {
                original
            } else {
                let mut factor = config.relaxation_factor;
                if detect_oscillation(values, config.oscillation_threshold) {
                    factor *= 0.5;
                }
                adaptive_relax(original, values[values.len() - 2], factor)
            }
        }
    };
    let improvement = (accelerated - original).abs();
    let magnitude = original.abs().max(accelerated.abs()).max(f64::EPSILON);
    AccelerationResult {
        accelerated_value: accelerated,
        original_value: original,
        improvement,
        converged: improvement / magnitude < 1e-12,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // -- Aitken --

    #[test]
    fn test_aitken_geometric_convergence() {
        // s_n = 1 - (1/2)^n => 0.5, 0.75, 0.875 => limit 1.0
        let result = aitken_extrapolate(&[0.5, 0.75, 0.875]).expect("extrapolate");
        assert!((result - 1.0).abs() < 1e-10, "got {result}");
    }

    #[test]
    fn test_aitken_already_converged() {
        assert!(aitken_extrapolate(&[1.0, 1.0, 1.0]).is_none());
    }

    #[test]
    fn test_aitken_too_few_values() {
        assert!(aitken_extrapolate(&[]).is_none());
        assert!(aitken_extrapolate(&[1.0]).is_none());
        assert!(aitken_extrapolate(&[1.0, 2.0]).is_none());
    }

    #[test]
    fn test_aitken_uses_last_three() {
        let result = aitken_extrapolate(&[0.0, 0.0, 0.5, 0.75, 0.875]).expect("extrapolate");
        assert!((result - 1.0).abs() < 1e-10, "got {result}");
    }

    // -- Richardson --

    #[test]
    fn test_richardson_first_order() {
        // (2*1.75 - 1.5) / (2-1) = 2.0
        let result = richardson_extrapolate(&[1.5, 1.75], 1).expect("extrapolate");
        assert!((result - 2.0).abs() < 1e-10, "got {result}");
    }

    #[test]
    fn test_richardson_second_order() {
        // (4*2.75 - 2.0) / 3 = 3.0
        let result = richardson_extrapolate(&[2.0, 2.75], 2).expect("extrapolate");
        assert!((result - 3.0).abs() < 1e-10, "got {result}");
    }

    #[test]
    fn test_richardson_too_few_values() {
        assert!(richardson_extrapolate(&[], 1).is_none());
        assert!(richardson_extrapolate(&[1.0], 1).is_none());
    }

    #[test]
    fn test_richardson_zero_order() {
        assert!(richardson_extrapolate(&[1.0, 2.0], 0).is_none());
    }

    // -- Adaptive relaxation --

    #[test]
    fn test_relax_full_factor() {
        assert!((adaptive_relax(5.0, 3.0, 1.0) - 5.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_relax_zero_factor() {
        assert!((adaptive_relax(5.0, 3.0, 0.0) - 3.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_relax_half_factor() {
        assert!((adaptive_relax(4.0, 2.0, 0.5) - 3.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_relax_clamping() {
        assert!((adaptive_relax(5.0, 3.0, 1.5) - 5.0).abs() < f64::EPSILON);
        assert!((adaptive_relax(5.0, 3.0, -0.5) - 3.0).abs() < f64::EPSILON);
    }

    // -- Oscillation detection --

    #[test]
    fn test_oscillation_alternating_sequence() {
        assert!(detect_oscillation(&[1.0, -1.0, 1.0, -1.0, 1.0], 0.6));
    }

    #[test]
    fn test_oscillation_monotone_sequence() {
        assert!(!detect_oscillation(&[1.0, 2.0, 3.0, 4.0, 5.0], 0.6));
    }

    #[test]
    fn test_oscillation_too_few_values() {
        assert!(!detect_oscillation(&[], 0.5));
        assert!(!detect_oscillation(&[1.0], 0.5));
        assert!(!detect_oscillation(&[1.0, 2.0], 0.5));
    }

    #[test]
    fn test_oscillation_partial() {
        // diffs: 1, -0.5, 1, -0.5 => 3/3 sign changes => ratio 1.0
        assert!(detect_oscillation(&[1.0, 2.0, 1.5, 2.5, 2.0], 0.6));
    }

    // -- Unified accelerate() --

    #[test]
    fn test_accelerate_none_strategy() {
        let config = AccelerationConfig { strategy: AccelerationStrategy::None, ..Default::default() };
        let r = accelerate(&[0.5, 0.75, 0.875], &config);
        assert!((r.accelerated_value - 0.875).abs() < f64::EPSILON);
        assert!((r.original_value - 0.875).abs() < f64::EPSILON);
        assert!(r.converged);
    }

    #[test]
    fn test_accelerate_aitken() {
        let config = AccelerationConfig {
            strategy: AccelerationStrategy::AitkenDeltaSquared, ..Default::default()
        };
        let r = accelerate(&[0.5, 0.75, 0.875], &config);
        assert!((r.accelerated_value - 1.0).abs() < 1e-10, "got {}", r.accelerated_value);
        assert!((r.original_value - 0.875).abs() < f64::EPSILON);
        assert!(r.improvement > 0.0);
    }

    #[test]
    fn test_accelerate_richardson() {
        let config = AccelerationConfig {
            strategy: AccelerationStrategy::Richardson, ..Default::default()
        };
        let r = accelerate(&[1.5, 1.75], &config);
        assert!((r.accelerated_value - 2.0).abs() < 1e-10, "got {}", r.accelerated_value);
    }

    #[test]
    fn test_accelerate_adaptive_no_oscillation() {
        let config = AccelerationConfig {
            strategy: AccelerationStrategy::AdaptiveRelaxation,
            relaxation_factor: 0.8,
            oscillation_threshold: 0.6,
            ..Default::default()
        };
        let r = accelerate(&[0.5, 0.6, 0.7, 0.8], &config);
        let expected = adaptive_relax(0.8, 0.7, 0.8);
        assert!((r.accelerated_value - expected).abs() < 1e-10, "got {}", r.accelerated_value);
    }

    #[test]
    fn test_accelerate_adaptive_with_oscillation() {
        let config = AccelerationConfig {
            strategy: AccelerationStrategy::AdaptiveRelaxation,
            relaxation_factor: 0.8,
            oscillation_threshold: 0.5,
            ..Default::default()
        };
        let r = accelerate(&[1.0, 2.0, 1.0, 2.0, 1.0], &config);
        // Factor halved to 0.4: 0.4*1.0 + 0.6*2.0 = 1.6
        let expected = adaptive_relax(1.0, 2.0, 0.4);
        assert!((r.accelerated_value - expected).abs() < 1e-10, "got {}", r.accelerated_value);
        assert!(!r.converged);
    }

    #[test]
    fn test_accelerate_empty_input() {
        let r = accelerate(&[], &AccelerationConfig::default());
        assert!(r.accelerated_value.abs() < f64::EPSILON);
        assert!(!r.converged);
    }

    #[test]
    fn test_accelerate_single_value_fallback() {
        let config = AccelerationConfig {
            strategy: AccelerationStrategy::AitkenDeltaSquared, ..Default::default()
        };
        let r = accelerate(&[0.5], &config);
        assert!((r.accelerated_value - 0.5).abs() < f64::EPSILON);
        assert!(r.converged);
    }

    #[test]
    fn test_default_config() {
        let c = AccelerationConfig::default();
        assert_eq!(c.strategy, AccelerationStrategy::None);
        assert!((c.relaxation_factor - 0.8).abs() < f64::EPSILON);
        assert_eq!(c.max_extrapolation_steps, 5);
        assert!((c.oscillation_threshold - 0.6).abs() < f64::EPSILON);
    }
}
