// trust-convergence/analysis.rs: Convergence pattern detection and rate analysis.
//
// Detects convergence patterns from iteration history: monotonic improvement,
// oscillation, plateau, and divergence. Computes convergence rate and predicts
// time-to-convergence.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};

use crate::metrics::ConvergenceMetrics;

// ---------------------------------------------------------------------------
// Convergence pattern classification
// ---------------------------------------------------------------------------

/// Detected convergence pattern across observed iterations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub(crate) enum ConvergencePattern {
    /// VCs proven is strictly non-decreasing across iterations.
    MonotonicImprovement,
    /// VCs proven alternates between increasing and decreasing.
    Oscillation,
    /// VCs proven has not changed for multiple consecutive iterations.
    Plateau,
    /// VCs proven is trending downward over recent iterations.
    Divergence,
    /// Not enough data to classify (fewer than 2 iterations).
    Insufficient,
}

/// Result of convergence pattern analysis.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub(crate) struct PatternAnalysis {
    /// The detected pattern.
    pub pattern: ConvergencePattern,
    /// Confidence in the classification (0.0..=1.0).
    pub confidence: f64,
    /// Number of iterations analyzed.
    pub iterations_analyzed: usize,
    /// Human-readable description.
    pub description: String,
}

/// Classify the convergence pattern from VCs-proven-per-iteration data.
#[must_use]
pub(crate) fn detect_pattern(vcs_proven: &[u32]) -> PatternAnalysis {
    if vcs_proven.len() < 2 {
        return PatternAnalysis {
            pattern: ConvergencePattern::Insufficient,
            confidence: 1.0,
            iterations_analyzed: vcs_proven.len(),
            description: "Not enough data to classify convergence pattern".to_string(),
        };
    }

    let deltas: Vec<i64> = vcs_proven
        .windows(2)
        .map(|w| w[1] as i64 - w[0] as i64)
        .collect();

    let positive_count = deltas.iter().filter(|&&d| d > 0).count();
    let negative_count = deltas.iter().filter(|&&d| d < 0).count();
    let zero_count = deltas.iter().filter(|&&d| d == 0).count();
    let total = deltas.len();

    // Detect plateau: all deltas are zero
    if zero_count == total {
        return PatternAnalysis {
            pattern: ConvergencePattern::Plateau,
            confidence: 1.0,
            iterations_analyzed: vcs_proven.len(),
            description: format!(
                "No change in VCs proven across {} iterations",
                vcs_proven.len()
            ),
        };
    }

    // Detect monotonic improvement: no decreases
    if negative_count == 0 {
        let confidence = if zero_count == 0 { 1.0 } else { 0.8 };
        return PatternAnalysis {
            pattern: ConvergencePattern::MonotonicImprovement,
            confidence,
            iterations_analyzed: vcs_proven.len(),
            description: format!(
                "VCs proven non-decreasing across {} iterations ({} increases, {} flat)",
                vcs_proven.len(),
                positive_count,
                zero_count
            ),
        };
    }

    // Detect divergence: mostly decreasing
    if negative_count as f64 / total as f64 > 0.6 {
        let confidence = negative_count as f64 / total as f64;
        return PatternAnalysis {
            pattern: ConvergencePattern::Divergence,
            confidence,
            iterations_analyzed: vcs_proven.len(),
            description: format!(
                "VCs proven trending down: {} of {} transitions are decreasing",
                negative_count, total
            ),
        };
    }

    // Detect oscillation: sign changes in deltas
    let sign_changes = deltas
        .windows(2)
        .filter(|w| (w[0] > 0 && w[1] < 0) || (w[0] < 0 && w[1] > 0))
        .count();

    if sign_changes > 0 && positive_count > 0 && negative_count > 0 {
        let max_possible_changes = if total > 1 { total - 1 } else { 1 };
        let confidence = sign_changes as f64 / max_possible_changes as f64;
        return PatternAnalysis {
            pattern: ConvergencePattern::Oscillation,
            confidence: confidence.min(1.0),
            iterations_analyzed: vcs_proven.len(),
            description: format!(
                "VCs proven oscillating: {} sign changes across {} transitions",
                sign_changes, total
            ),
        };
    }

    // Default: monotonic improvement with low confidence
    PatternAnalysis {
        pattern: ConvergencePattern::MonotonicImprovement,
        confidence: 0.5,
        iterations_analyzed: vcs_proven.len(),
        description: format!(
            "Mixed signals: {} increases, {} decreases, {} flat across {} transitions",
            positive_count, negative_count, zero_count, total
        ),
    }
}

// ---------------------------------------------------------------------------
// Convergence rate
// ---------------------------------------------------------------------------

/// Convergence rate metrics computed from iteration history.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub(crate) struct ConvergenceRate {
    /// Average VCs proven per iteration.
    pub avg_vcs_per_iteration: f64,
    /// VCs proven in the most recent iteration.
    pub latest_vcs_proven: u32,
    /// VCs proven in the first iteration.
    pub first_vcs_proven: u32,
    /// Overall rate: (latest - first) / iterations.
    pub overall_rate: f64,
    /// Windowed rate over the last N iterations (default 3).
    pub recent_rate: f64,
    /// Whether the rate is accelerating (recent > overall).
    pub is_accelerating: bool,
}

/// Compute convergence rate from VCs-proven-per-iteration data.
///
/// Returns `None` if there are fewer than 2 data points.
#[must_use]
pub(crate) fn compute_convergence_rate(vcs_proven: &[u32]) -> Option<ConvergenceRate> {
    if vcs_proven.len() < 2 {
        return None;
    }

    let first = vcs_proven[0];
    let latest = *vcs_proven.last()?;
    let total_iterations = vcs_proven.len() as f64;

    let avg = vcs_proven.iter().map(|&v| v as f64).sum::<f64>() / total_iterations;
    let overall_rate = (latest as f64 - first as f64) / (total_iterations - 1.0);

    // Windowed rate over last 3 iterations (or all if fewer)
    let window_size = 3.min(vcs_proven.len());
    let window = &vcs_proven[vcs_proven.len() - window_size..];
    let recent_rate = if window.len() >= 2 {
        let w_first = window[0];
        let w_last = *window.last().unwrap_or(&w_first);
        (w_last as f64 - w_first as f64) / (window.len() as f64 - 1.0)
    } else {
        0.0
    };

    Some(ConvergenceRate {
        avg_vcs_per_iteration: avg,
        latest_vcs_proven: latest,
        first_vcs_proven: first,
        overall_rate,
        recent_rate,
        is_accelerating: recent_rate > overall_rate,
    })
}

// ---------------------------------------------------------------------------
// Full convergence analysis
// ---------------------------------------------------------------------------

/// Complete convergence analysis result.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub(crate) struct ConvergenceAnalysis {
    /// Detected convergence pattern.
    pub pattern: PatternAnalysis,
    /// Convergence rate metrics (None if insufficient data).
    pub rate: Option<ConvergenceRate>,
    /// Proof success rate: total proved / total attempted across all iterations.
    pub proof_success_rate: f64,
    /// Estimated iterations to full convergence (None if cannot estimate).
    pub estimated_iterations_to_convergence: Option<u32>,
}

/// Run full convergence analysis on aggregated metrics.
#[must_use]
pub(crate) fn analyze_convergence(metrics: &ConvergenceMetrics) -> ConvergenceAnalysis {
    let vcs = &metrics.vcs_proven_per_iteration;
    let pattern = detect_pattern(vcs);
    let rate = compute_convergence_rate(vcs);

    // Compute overall proof success rate
    let total_proven: u64 = vcs.iter().map(|&v| v as u64).sum();
    // Use the max vc count as total per iteration (heuristic: the most VCs seen)
    let max_vcs_per_iter = vcs.iter().copied().max().unwrap_or(0) as u64;
    let proof_success_rate = if max_vcs_per_iter > 0 && !vcs.is_empty() {
        total_proven as f64 / (max_vcs_per_iter as f64 * vcs.len() as f64)
    } else {
        0.0
    };

    // Estimate iterations to convergence based on rate
    let estimated = rate.as_ref().and_then(|r| {
        if r.overall_rate <= 0.0 || r.latest_vcs_proven == 0 {
            return None;
        }
        // Heuristic: remaining = latest / rate
        let remaining = r.latest_vcs_proven as f64 / r.overall_rate;
        if remaining > 0.0 && remaining <= u32::MAX as f64 {
            Some(remaining.ceil() as u32)
        } else {
            None
        }
    });

    ConvergenceAnalysis {
        pattern,
        rate,
        proof_success_rate,
        estimated_iterations_to_convergence: estimated,
    }
}

// ---------------------------------------------------------------------------
// Sparkline data
// ---------------------------------------------------------------------------

/// Compact sparkline representation for dashboard display.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub(crate) struct Sparkline {
    /// Series label.
    pub label: String,
    /// Normalized values (0.0..=1.0) for rendering.
    pub values: Vec<f64>,
    /// Raw values before normalization.
    pub raw_values: Vec<f64>,
    /// Min of raw values.
    pub min: f64,
    /// Max of raw values.
    pub max: f64,
}

/// Build a sparkline from raw f64 values.
#[must_use]
pub(crate) fn build_sparkline(label: &str, raw_values: &[f64]) -> Sparkline {
    let min = raw_values
        .iter()
        .copied()
        .min_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal))
        .unwrap_or(0.0);
    let max = raw_values
        .iter()
        .copied()
        .max_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal))
        .unwrap_or(0.0);
    let range = max - min;

    let normalized = if range.abs() < f64::EPSILON {
        vec![0.5; raw_values.len()]
    } else {
        raw_values.iter().map(|&v| (v - min) / range).collect()
    };

    Sparkline {
        label: label.to_string(),
        values: normalized,
        raw_values: raw_values.to_vec(),
        min,
        max,
    }
}

/// Build sparklines for all key metrics series.
#[must_use]
pub(crate) fn build_metric_sparklines(metrics: &ConvergenceMetrics) -> Vec<Sparkline> {
    let mut sparklines = Vec::new();

    sparklines.push(build_sparkline(
        "VCs Proven",
        &metrics
            .vcs_proven_per_iteration
            .iter()
            .map(|&v| v as f64)
            .collect::<Vec<_>>(),
    ));

    sparklines.push(build_sparkline(
        "Iteration Time",
        &metrics
            .time_per_iteration
            .iter()
            .map(|&v| v as f64)
            .collect::<Vec<_>>(),
    ));

    sparklines.push(build_sparkline(
        "Cache Hit Rate",
        &metrics.cache_hit_rate_per_iteration,
    ));

    if !metrics.strengthening_proposals_per_iteration.is_empty() {
        sparklines.push(build_sparkline(
            "Strengthening Proposals",
            &metrics
                .strengthening_proposals_per_iteration
                .iter()
                .map(|&v| v as f64)
                .collect::<Vec<_>>(),
        ));
    }

    sparklines
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use trust_types::fx::FxHashMap;

    use super::*;

    fn make_metrics(vcs_proven: Vec<u32>) -> ConvergenceMetrics {
        let len = vcs_proven.len();
        ConvergenceMetrics {
            iterations: len as u32,
            time_per_iteration: vec![100; len],
            vcs_proven_per_iteration: vcs_proven,
            strengthening_proposals_per_iteration: vec![0; len],
            cache_hit_rate_per_iteration: vec![0.5; len],
            solver_time_totals: FxHashMap::default(),
            vc_kind_failure_totals: FxHashMap::default(),
            function_retry_totals: FxHashMap::default(),
        }
    }

    // -- Pattern detection --

    #[test]
    fn test_detect_pattern_insufficient_data() {
        let result = detect_pattern(&[5]);
        assert_eq!(result.pattern, ConvergencePattern::Insufficient);
        assert_eq!(result.iterations_analyzed, 1);
    }

    #[test]
    fn test_detect_pattern_empty() {
        let result = detect_pattern(&[]);
        assert_eq!(result.pattern, ConvergencePattern::Insufficient);
    }

    #[test]
    fn test_detect_pattern_monotonic_improvement() {
        let result = detect_pattern(&[2, 4, 6, 8]);
        assert_eq!(result.pattern, ConvergencePattern::MonotonicImprovement);
        assert!((result.confidence - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_detect_pattern_monotonic_with_flat_segments() {
        let result = detect_pattern(&[2, 4, 4, 6]);
        assert_eq!(result.pattern, ConvergencePattern::MonotonicImprovement);
        assert!(result.confidence > 0.5);
        assert!(result.confidence < 1.0);
    }

    #[test]
    fn test_detect_pattern_plateau() {
        let result = detect_pattern(&[5, 5, 5, 5]);
        assert_eq!(result.pattern, ConvergencePattern::Plateau);
        assert!((result.confidence - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_detect_pattern_divergence() {
        let result = detect_pattern(&[10, 8, 6, 4, 2]);
        assert_eq!(result.pattern, ConvergencePattern::Divergence);
        assert!(result.confidence > 0.6);
    }

    #[test]
    fn test_detect_pattern_oscillation() {
        let result = detect_pattern(&[5, 8, 4, 9, 3]);
        assert_eq!(result.pattern, ConvergencePattern::Oscillation);
        assert!(result.confidence > 0.0);
    }

    // -- Convergence rate --

    #[test]
    fn test_convergence_rate_insufficient() {
        assert!(compute_convergence_rate(&[5]).is_none());
        assert!(compute_convergence_rate(&[]).is_none());
    }

    #[test]
    fn test_convergence_rate_improving() {
        let rate = compute_convergence_rate(&[2, 4, 6]).expect("rate");
        assert_eq!(rate.first_vcs_proven, 2);
        assert_eq!(rate.latest_vcs_proven, 6);
        assert!((rate.overall_rate - 2.0).abs() < f64::EPSILON);
        assert!((rate.avg_vcs_per_iteration - 4.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_convergence_rate_flat() {
        let rate = compute_convergence_rate(&[5, 5, 5]).expect("rate");
        assert!((rate.overall_rate).abs() < f64::EPSILON);
        assert!(!rate.is_accelerating);
    }

    #[test]
    fn test_convergence_rate_accelerating() {
        // Overall rate is slow, but last 3 are fast
        let rate = compute_convergence_rate(&[1, 1, 1, 3, 5, 7]).expect("rate");
        // Overall: (7-1)/5 = 1.2
        // Recent (last 3): (7-3)/2 = 2.0
        assert!(rate.is_accelerating);
    }

    #[test]
    fn test_convergence_rate_decelerating() {
        let rate = compute_convergence_rate(&[1, 5, 9, 10, 10, 10]).expect("rate");
        // Overall rate positive, recent rate zero => not accelerating
        assert!(!rate.is_accelerating);
    }

    // -- Full analysis --

    #[test]
    fn test_analyze_convergence_improving() {
        let metrics = make_metrics(vec![2, 4, 6, 8]);
        let analysis = analyze_convergence(&metrics);
        assert_eq!(analysis.pattern.pattern, ConvergencePattern::MonotonicImprovement);
        assert!(analysis.rate.is_some());
        assert!(analysis.proof_success_rate > 0.0);
    }

    #[test]
    fn test_analyze_convergence_empty() {
        let metrics = make_metrics(vec![]);
        let analysis = analyze_convergence(&metrics);
        assert_eq!(analysis.pattern.pattern, ConvergencePattern::Insufficient);
        assert!(analysis.rate.is_none());
        assert!((analysis.proof_success_rate).abs() < f64::EPSILON);
    }

    #[test]
    fn test_analyze_convergence_plateau() {
        let metrics = make_metrics(vec![5, 5, 5]);
        let analysis = analyze_convergence(&metrics);
        assert_eq!(analysis.pattern.pattern, ConvergencePattern::Plateau);
    }

    // -- Sparkline --

    #[test]
    fn test_build_sparkline_basic() {
        let sparkline = build_sparkline("test", &[0.0, 5.0, 10.0]);
        assert_eq!(sparkline.label, "test");
        assert_eq!(sparkline.values.len(), 3);
        assert!((sparkline.values[0]).abs() < f64::EPSILON); // min => 0.0
        assert!((sparkline.values[1] - 0.5).abs() < f64::EPSILON); // mid => 0.5
        assert!((sparkline.values[2] - 1.0).abs() < f64::EPSILON); // max => 1.0
        assert!((sparkline.min).abs() < f64::EPSILON);
        assert!((sparkline.max - 10.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_build_sparkline_constant() {
        let sparkline = build_sparkline("flat", &[5.0, 5.0, 5.0]);
        // All same => normalized to 0.5
        for v in &sparkline.values {
            assert!((v - 0.5).abs() < f64::EPSILON);
        }
    }

    #[test]
    fn test_build_sparkline_empty() {
        let sparkline = build_sparkline("empty", &[]);
        assert!(sparkline.values.is_empty());
    }

    #[test]
    fn test_build_metric_sparklines() {
        let metrics = make_metrics(vec![2, 4, 6]);
        let sparklines = build_metric_sparklines(&metrics);
        // VCs Proven, Iteration Time, Cache Hit Rate = 3 (proposals are all 0)
        assert!(sparklines.len() >= 3);
        assert_eq!(sparklines[0].label, "VCs Proven");
        assert_eq!(sparklines[1].label, "Iteration Time");
        assert_eq!(sparklines[2].label, "Cache Hit Rate");
    }

    // -- Serialization --

    #[test]
    fn test_pattern_analysis_serialization() {
        let analysis = PatternAnalysis {
            pattern: ConvergencePattern::Oscillation,
            confidence: 0.75,
            iterations_analyzed: 5,
            description: "test".to_string(),
        };
        let json = serde_json::to_string(&analysis).expect("serialize");
        let deser: PatternAnalysis = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(analysis, deser);
    }

    #[test]
    fn test_convergence_rate_serialization() {
        let rate = ConvergenceRate {
            avg_vcs_per_iteration: 4.0,
            latest_vcs_proven: 6,
            first_vcs_proven: 2,
            overall_rate: 2.0,
            recent_rate: 2.0,
            is_accelerating: false,
        };
        let json = serde_json::to_string(&rate).expect("serialize");
        let deser: ConvergenceRate = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(rate, deser);
    }

    #[test]
    fn test_sparkline_serialization() {
        let sparkline = build_sparkline("test", &[1.0, 2.0, 3.0]);
        let json = serde_json::to_string(&sparkline).expect("serialize");
        let deser: Sparkline = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(sparkline, deser);
    }

    #[test]
    fn test_full_analysis_serialization() {
        let metrics = make_metrics(vec![2, 4, 6]);
        let analysis = analyze_convergence(&metrics);
        let json = serde_json::to_string(&analysis).expect("serialize");
        let deser: ConvergenceAnalysis = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(analysis, deser);
    }
}
