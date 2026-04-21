// trust-convergence/src/lyapunov.rs — Lyapunov convergence analysis
//
// Part of #320: Add Lyapunov convergence analysis to trust-convergence
//
// Provides Lyapunov function-based stability analysis for the verification
// loop. A Lyapunov function V(x) proves convergence if:
//   1. V(x) > 0 for all x != 0 (positive-definite)
//   2. V(x_{k+1}) < V(x_k) (strictly decreasing along trajectories)
//
// This module synthesizes candidate quadratic Lyapunov functions V(x) = x^T P x
// for the loop state and checks the two conditions numerically.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

/// A candidate Lyapunov function over loop state variables.
///
/// Represents V(x) = sum_i coefficients[i] * x_i^2  (diagonal quadratic form).
/// This is the simplest positive-definite form; sufficient for many convergence
/// proofs when the state is a vector of non-negative metrics.
#[derive(Debug, Clone)]
pub(crate) struct LyapunovFunction {
    /// Quadratic coefficients for each state dimension. Must all be > 0
    /// for the function to be positive-definite.
    pub coefficients: Vec<f64>,
    /// Human-readable names for each state dimension (optional).
    pub variable_names: Vec<String>,
}

impl LyapunovFunction {
    /// Create a Lyapunov function with the given positive coefficients.
    ///
    /// Returns `None` if `coefficients` is empty or any coefficient is <= 0.
    #[must_use]
    pub fn new(coefficients: Vec<f64>) -> Option<Self> {
        if coefficients.is_empty() || coefficients.iter().any(|&c| c <= 0.0) {
            return None;
        }
        let variable_names = (0..coefficients.len())
            .map(|i| format!("x{i}"))
            .collect();
        Self { coefficients, variable_names }.into()
    }

    /// Create a Lyapunov function with named variables.
    ///
    /// Returns `None` if dimensions mismatch, coefficients is empty,
    /// or any coefficient is <= 0.
    #[must_use]
    pub fn with_names(coefficients: Vec<f64>, names: Vec<String>) -> Option<Self> {
        if coefficients.is_empty()
            || coefficients.len() != names.len()
            || coefficients.iter().any(|&c| c <= 0.0)
        {
            return None;
        }
        Some(Self { coefficients, variable_names: names })
    }

    /// Number of state dimensions.
    #[must_use]
    pub fn dimension(&self) -> usize {
        self.coefficients.len()
    }

    /// Evaluate V(x) = sum_i coefficients[i] * x_i^2.
    ///
    /// Returns `None` if `state` length differs from `dimension()`.
    #[must_use]
    pub fn evaluate(&self, state: &[f64]) -> Option<f64> {
        if state.len() != self.coefficients.len() {
            return None;
        }
        Some(
            self.coefficients
                .iter()
                .zip(state.iter())
                .map(|(c, x)| c * x * x)
                .sum(),
        )
    }

    /// Check whether this function is positive-definite
    /// (all coefficients strictly positive).
    #[must_use]
    pub fn is_positive_definite(&self) -> bool {
        self.coefficients.iter().all(|&c| c > 0.0)
    }
}

/// Result of a Lyapunov stability check.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub(crate) enum StabilityResult {
    /// The system is stable: V decreases along all observed trajectories.
    Stable {
        /// Maximum observed decrease ratio V(x_{k+1})/V(x_k) (< 1.0 for stability).
        max_ratio: f64,
    },
    /// The system is unstable: V increased in at least one step.
    Unstable {
        /// The step index where the first increase was observed.
        first_increase_step: usize,
        /// The ratio V(x_{k+1})/V(x_k) at that step.
        ratio: f64,
    },
    /// Inconclusive: not enough data or degenerate case.
    Inconclusive {
        /// Why the check was inconclusive.
        reason: String,
    },
}

/// Check stability of a trajectory under a Lyapunov function.
///
/// Given a sequence of state vectors (one per loop iteration), evaluates V
/// at each point and verifies strict decrease.
///
/// # Arguments
/// - `lyapunov`: The candidate Lyapunov function.
/// - `trajectory`: Sequence of state vectors, each of length `lyapunov.dimension()`.
///
/// Returns `StabilityResult::Stable` with the worst-case ratio if V is strictly
/// decreasing, `Unstable` if any increase is detected, or `Inconclusive` for
/// degenerate inputs.
#[must_use]
pub(crate) fn check_stability(
    lyapunov: &LyapunovFunction,
    trajectory: &[Vec<f64>],
) -> StabilityResult {
    if trajectory.len() < 2 {
        return StabilityResult::Inconclusive {
            reason: "need at least 2 trajectory points".to_string(),
        };
    }
    if !lyapunov.is_positive_definite() {
        return StabilityResult::Inconclusive {
            reason: "Lyapunov function is not positive-definite".to_string(),
        };
    }

    let values: Vec<f64> = match trajectory
        .iter()
        .map(|s| lyapunov.evaluate(s))
        .collect::<Option<Vec<_>>>()
    {
        Some(v) => v,
        None => {
            return StabilityResult::Inconclusive {
                reason: "dimension mismatch in trajectory".to_string(),
            }
        }
    };

    // Check that the first value is positive (non-zero state).
    if values[0] < f64::EPSILON {
        return StabilityResult::Inconclusive {
            reason: "trajectory starts at or near the origin".to_string(),
        };
    }

    let mut max_ratio: f64 = 0.0;
    for (i, window) in values.windows(2).enumerate() {
        let (v_prev, v_curr) = (window[0], window[1]);
        if v_prev < f64::EPSILON {
            return StabilityResult::Inconclusive {
                reason: format!("V vanishes at step {i}"),
            };
        }
        let ratio = v_curr / v_prev;
        if ratio >= 1.0 {
            return StabilityResult::Unstable {
                first_increase_step: i,
                ratio,
            };
        }
        max_ratio = max_ratio.max(ratio);
    }

    StabilityResult::Stable { max_ratio }
}

/// Attempt to synthesize a diagonal quadratic Lyapunov function from trajectory data.
///
/// Strategy: use the inverse of the variance of each state dimension as the
/// coefficient. Dimensions with high variance get lower weight (they dominate
/// less), producing a balanced energy measure.
///
/// Returns `None` if the trajectory has < 2 points, dimension is 0, or
/// any dimension has zero variance (constant — cannot contribute to convergence).
#[must_use]
pub(crate) fn synthesize_lyapunov(trajectory: &[Vec<f64>]) -> Option<LyapunovFunction> {
    if trajectory.len() < 2 {
        return None;
    }
    let dim = trajectory[0].len();
    if dim == 0 {
        return None;
    }
    // Verify consistent dimensions.
    if trajectory.iter().any(|s| s.len() != dim) {
        return None;
    }

    let n = trajectory.len() as f64;
    let mut coefficients = Vec::with_capacity(dim);
    for d in 0..dim {
        let mean: f64 = trajectory.iter().map(|s| s[d]).sum::<f64>() / n;
        let variance: f64 =
            trajectory.iter().map(|s| (s[d] - mean) * (s[d] - mean)).sum::<f64>() / n;
        if variance < f64::EPSILON {
            return None; // Constant dimension — degenerate.
        }
        coefficients.push(1.0 / variance);
    }

    LyapunovFunction::new(coefficients)
}

/// Estimate the convergence rate from a Lyapunov function over a trajectory.
///
/// The convergence rate rho is estimated as the geometric mean of
/// V(x_{k+1})/V(x_k) over all steps. A value < 1 indicates convergence;
/// closer to 0 is faster.
///
/// Returns `None` if the trajectory is too short, dimension mismatches exist,
/// or any V value is non-positive.
#[must_use]
pub(crate) fn compute_convergence_rate(
    lyapunov: &LyapunovFunction,
    trajectory: &[Vec<f64>],
) -> Option<f64> {
    if trajectory.len() < 2 {
        return None;
    }

    let values: Vec<f64> = trajectory
        .iter()
        .map(|s| lyapunov.evaluate(s))
        .collect::<Option<Vec<_>>>()?;

    if values.iter().any(|&v| v < f64::EPSILON) {
        return None;
    }

    let n_steps = values.len() - 1;
    // rho = (V_last / V_first)^(1/n_steps)
    let ratio = values[values.len() - 1] / values[0];
    if ratio <= 0.0 {
        return None;
    }
    Some(ratio.powf(1.0 / n_steps as f64))
}

/// A certificate proving convergence via a Lyapunov argument.
///
/// Contains the Lyapunov function, the stability result, and the convergence
/// rate. Only produced when stability is confirmed.
#[derive(Debug, Clone)]
pub(crate) struct LyapunovCertificate {
    /// The Lyapunov function used for the proof.
    pub function: LyapunovFunction,
    /// The stability verdict.
    pub stability: StabilityResult,
    /// Estimated convergence rate (geometric mean ratio).
    pub convergence_rate: f64,
    /// Number of trajectory points used in the analysis.
    pub trajectory_length: usize,
}

impl LyapunovCertificate {
    /// Try to build a certificate from a trajectory.
    ///
    /// Synthesizes a Lyapunov function, checks stability, and computes
    /// the convergence rate. Returns `None` if synthesis fails or the
    /// system is not stable.
    #[must_use]
    pub fn try_from_trajectory(trajectory: &[Vec<f64>]) -> Option<Self> {
        let function = synthesize_lyapunov(trajectory)?;
        let stability = check_stability(&function, trajectory);
        match &stability {
            StabilityResult::Stable { .. } => {}
            _ => return None,
        }
        let convergence_rate = compute_convergence_rate(&function, trajectory)?;
        Some(Self {
            function,
            stability,
            convergence_rate,
            trajectory_length: trajectory.len(),
        })
    }

    /// Whether this certificate proves convergence (rate < 1.0).
    #[must_use]
    pub fn is_convergent(&self) -> bool {
        self.convergence_rate < 1.0
    }

    /// Estimated number of iterations to reach a given tolerance,
    /// assuming the current convergence rate holds.
    ///
    /// Returns `None` if not convergent or tolerance is non-positive.
    #[must_use]
    pub fn estimated_iterations_to(&self, tolerance: f64) -> Option<usize> {
        if !self.is_convergent() || tolerance <= 0.0 || tolerance >= 1.0 {
            return None;
        }
        // V_k = V_0 * rho^k < tolerance * V_0
        // => k > ln(tolerance) / ln(rho)
        let k = tolerance.ln() / self.convergence_rate.ln();
        Some(k.ceil() as usize)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // -- LyapunovFunction construction --

    #[test]
    fn test_lyapunov_function_new_valid() {
        let f = LyapunovFunction::new(vec![1.0, 2.0, 3.0]).expect("valid coefficients");
        assert_eq!(f.dimension(), 3);
        assert!(f.is_positive_definite());
        assert_eq!(f.variable_names, vec!["x0", "x1", "x2"]);
    }

    #[test]
    fn test_lyapunov_function_new_rejects_empty() {
        assert!(LyapunovFunction::new(vec![]).is_none());
    }

    #[test]
    fn test_lyapunov_function_new_rejects_non_positive() {
        assert!(LyapunovFunction::new(vec![1.0, 0.0, 2.0]).is_none());
        assert!(LyapunovFunction::new(vec![1.0, -1.0]).is_none());
    }

    #[test]
    fn test_lyapunov_function_with_names() {
        let f = LyapunovFunction::with_names(
            vec![1.0, 2.0],
            vec!["proved".to_string(), "failed".to_string()],
        )
        .expect("valid");
        assert_eq!(f.variable_names, vec!["proved", "failed"]);
    }

    #[test]
    fn test_lyapunov_function_with_names_rejects_mismatch() {
        assert!(LyapunovFunction::with_names(vec![1.0, 2.0], vec!["x".to_string()]).is_none());
    }

    // -- Evaluate --

    #[test]
    fn test_evaluate_simple() {
        let f = LyapunovFunction::new(vec![1.0, 2.0]).expect("valid");
        // V([3, 4]) = 1*9 + 2*16 = 41
        let v = f.evaluate(&[3.0, 4.0]).expect("dimension match");
        assert!((v - 41.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_evaluate_dimension_mismatch() {
        let f = LyapunovFunction::new(vec![1.0, 2.0]).expect("valid");
        assert!(f.evaluate(&[1.0]).is_none());
    }

    #[test]
    fn test_evaluate_at_origin() {
        let f = LyapunovFunction::new(vec![1.0, 2.0]).expect("valid");
        let v = f.evaluate(&[0.0, 0.0]).expect("ok");
        assert!(v.abs() < f64::EPSILON);
    }

    // -- check_stability --

    #[test]
    fn test_check_stability_converging_trajectory() {
        let f = LyapunovFunction::new(vec![1.0]).expect("valid");
        // Decreasing: 10, 5, 2.5, 1.25
        let traj = vec![vec![10.0_f64.sqrt()], vec![5.0_f64.sqrt()], vec![2.5_f64.sqrt()], vec![1.25_f64.sqrt()]];
        match check_stability(&f, &traj) {
            StabilityResult::Stable { max_ratio } => {
                assert!(max_ratio < 1.0, "ratio should be < 1, got {max_ratio}");
                assert!((max_ratio - 0.5).abs() < 1e-10);
            }
            other => panic!("expected Stable, got {other:?}"),
        }
    }

    #[test]
    fn test_check_stability_diverging_trajectory() {
        let f = LyapunovFunction::new(vec![1.0]).expect("valid");
        // Increasing: 1, 2, 4
        let traj = vec![vec![1.0], vec![2.0_f64.sqrt()], vec![2.0]];
        match check_stability(&f, &traj) {
            StabilityResult::Unstable { first_increase_step, .. } => {
                assert_eq!(first_increase_step, 0);
            }
            other => panic!("expected Unstable, got {other:?}"),
        }
    }

    #[test]
    fn test_check_stability_too_few_points() {
        let f = LyapunovFunction::new(vec![1.0]).expect("valid");
        match check_stability(&f, &[vec![1.0]]) {
            StabilityResult::Inconclusive { reason } => {
                assert!(reason.contains("at least 2"));
            }
            other => panic!("expected Inconclusive, got {other:?}"),
        }
    }

    // -- synthesize_lyapunov --

    #[test]
    fn test_synthesize_lyapunov_basic() {
        // A trajectory that converges toward the origin.
        let traj = vec![
            vec![10.0, 20.0],
            vec![5.0, 10.0],
            vec![2.5, 5.0],
            vec![1.25, 2.5],
        ];
        let f = synthesize_lyapunov(&traj).expect("synthesis should succeed");
        assert_eq!(f.dimension(), 2);
        assert!(f.is_positive_definite());
    }

    #[test]
    fn test_synthesize_lyapunov_rejects_constant_dim() {
        // Dimension 1 is constant => variance = 0 => None.
        let traj = vec![vec![10.0, 5.0], vec![5.0, 5.0], vec![2.5, 5.0]];
        assert!(synthesize_lyapunov(&traj).is_none());
    }

    #[test]
    fn test_synthesize_lyapunov_rejects_too_short() {
        assert!(synthesize_lyapunov(&[vec![1.0]]).is_none());
        assert!(synthesize_lyapunov(&[]).is_none());
    }

    // -- compute_convergence_rate --

    #[test]
    fn test_convergence_rate_halving() {
        let f = LyapunovFunction::new(vec![1.0]).expect("valid");
        // V values: 16, 8, 4, 2 => ratio per step = 0.5
        let traj = vec![vec![4.0], vec![8.0_f64.sqrt()], vec![2.0], vec![2.0_f64.sqrt()]];
        let rate = compute_convergence_rate(&f, &traj).expect("computable");
        assert!((rate - 0.5).abs() < 1e-10, "expected ~0.5, got {rate}");
    }

    #[test]
    fn test_convergence_rate_rejects_short() {
        let f = LyapunovFunction::new(vec![1.0]).expect("valid");
        assert!(compute_convergence_rate(&f, &[vec![1.0]]).is_none());
    }

    // -- LyapunovCertificate --

    #[test]
    fn test_certificate_from_converging_trajectory() {
        let traj = vec![
            vec![10.0, 20.0],
            vec![5.0, 10.0],
            vec![2.5, 5.0],
            vec![1.25, 2.5],
        ];
        let cert = LyapunovCertificate::try_from_trajectory(&traj)
            .expect("should produce certificate");
        assert!(cert.is_convergent());
        assert!(cert.convergence_rate < 1.0);
        assert_eq!(cert.trajectory_length, 4);
    }

    #[test]
    fn test_certificate_estimated_iterations() {
        let traj = vec![
            vec![10.0, 20.0],
            vec![5.0, 10.0],
            vec![2.5, 5.0],
            vec![1.25, 2.5],
        ];
        let cert = LyapunovCertificate::try_from_trajectory(&traj)
            .expect("certificate");
        let iters = cert.estimated_iterations_to(0.01).expect("convergent");
        // With rate ~0.25, ln(0.01)/ln(0.25) ~ 3.32 => ceil = 4
        assert!(iters > 0);
    }

    #[test]
    fn test_certificate_rejects_diverging() {
        let traj = vec![vec![1.0, 1.0], vec![2.0, 2.0], vec![4.0, 4.0]];
        assert!(LyapunovCertificate::try_from_trajectory(&traj).is_none());
    }

    #[test]
    fn test_certificate_estimated_iterations_invalid_tolerance() {
        let traj = vec![
            vec![10.0, 20.0],
            vec![5.0, 10.0],
            vec![2.5, 5.0],
        ];
        let cert = LyapunovCertificate::try_from_trajectory(&traj)
            .expect("certificate");
        assert!(cert.estimated_iterations_to(0.0).is_none());
        assert!(cert.estimated_iterations_to(1.0).is_none());
        assert!(cert.estimated_iterations_to(-0.5).is_none());
    }
}
