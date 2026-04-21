// trust-debug/trace_minimize.rs: Error trace minimization (#267)
//
// Reduces counterexample traces to minimal reproducing sequences using
// delta-debugging style reduction. Shorter traces are easier to understand.
//
// References:
//   Zeller, Hildebrandt. "Simplifying and Isolating Failure-Inducing Input" (TSE 2002).
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

// ---------------------------------------------------------------------------
// Trace types
// ---------------------------------------------------------------------------

/// A single step in an error trace.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct TraceStep {
    /// Step index in the original trace.
    pub index: usize,
    /// Description of the step.
    pub description: String,
    /// Whether this step is relevant to the error.
    pub relevant: bool,
    /// Relevance score (0.0 = irrelevant, 1.0 = critical).
    pub relevance_score: f64,
}

impl TraceStep {
    pub(crate) fn new(index: usize, description: impl Into<String>) -> Self {
        Self {
            index,
            description: description.into(),
            relevant: true,
            relevance_score: 0.5,
        }
    }

    pub(crate) fn with_score(mut self, score: f64) -> Self {
        self.relevance_score = score;
        self.relevant = score > 0.0;
        self
    }
}

/// An error trace to minimize.
#[derive(Debug, Clone)]
pub(crate) struct ErrorTrace {
    /// Steps in the trace.
    pub steps: Vec<TraceStep>,
    /// Description of the error at the end.
    pub error: String,
}

impl ErrorTrace {
    pub(crate) fn new(steps: Vec<TraceStep>, error: impl Into<String>) -> Self {
        Self { steps, error: error.into() }
    }

    /// Number of steps.
    #[must_use]
    pub(crate) fn len(&self) -> usize {
        self.steps.len()
    }

    #[must_use]
    pub(crate) fn is_empty(&self) -> bool {
        self.steps.is_empty()
    }
}

// ---------------------------------------------------------------------------
// Minimization result
// ---------------------------------------------------------------------------

/// Result of trace minimization.
#[derive(Debug, Clone)]
pub(crate) struct MinimizationResult {
    /// Minimal trace.
    pub minimal_trace: ErrorTrace,
    /// Steps that were removed.
    pub removed_steps: Vec<TraceStep>,
    /// Original length.
    pub original_length: usize,
    /// Minimized length.
    pub minimized_length: usize,
    /// Number of test iterations performed.
    pub iterations: usize,
}

impl MinimizationResult {
    /// Reduction ratio (0.0 = no reduction, 1.0 = maximally reduced).
    #[must_use]
    pub(crate) fn reduction_ratio(&self) -> f64 {
        if self.original_length == 0 { return 0.0; }
        1.0 - (self.minimized_length as f64 / self.original_length as f64)
    }
}

// ---------------------------------------------------------------------------
// Trace minimizer
// ---------------------------------------------------------------------------

/// Oracle that tests whether a reduced trace still exhibits the error.
pub(crate) trait ErrorOracle {
    /// Returns true if the given steps still reproduce the error.
    fn reproduces_error(&self, steps: &[TraceStep]) -> bool;
}

/// Always-true oracle for testing.
pub(crate) struct AlwaysReproduces;

impl ErrorOracle for AlwaysReproduces {
    fn reproduces_error(&self, steps: &[TraceStep]) -> bool {
        !steps.is_empty()
    }
}

/// Oracle that checks for a specific step.
pub(crate) struct RequiresStep {
    pub required_index: usize,
}

impl ErrorOracle for RequiresStep {
    fn reproduces_error(&self, steps: &[TraceStep]) -> bool {
        steps.iter().any(|s| s.index == self.required_index)
    }
}

/// Delta-debugging trace minimizer.
pub(crate) struct TraceMinimizer<'a> {
    oracle: &'a dyn ErrorOracle,
    max_iterations: usize,
}

impl<'a> TraceMinimizer<'a> {
    pub(crate) fn new(oracle: &'a dyn ErrorOracle) -> Self {
        Self { oracle, max_iterations: 100 }
    }

    pub(crate) fn with_max_iterations(mut self, max: usize) -> Self {
        self.max_iterations = max;
        self
    }

    /// Minimize a trace using delta debugging (ddmin algorithm).
    pub(crate) fn minimize(&self, trace: &ErrorTrace) -> MinimizationResult {
        let original_length = trace.len();
        let mut current = trace.steps.clone();
        let mut iterations = 0;
        let mut granularity = 2;

        while granularity <= current.len() && iterations < self.max_iterations {
            let chunk_size = current.len().div_ceil(granularity);
            let mut reduced = false;

            for i in 0..granularity {
                iterations += 1;
                if iterations >= self.max_iterations {
                    break;
                }

                let start = i * chunk_size;
                let end = (start + chunk_size).min(current.len());

                // Try removing this chunk
                let candidate: Vec<TraceStep> = current[..start].iter()
                    .chain(current[end..].iter())
                    .cloned()
                    .collect();

                if !candidate.is_empty() && self.oracle.reproduces_error(&candidate) {
                    current = candidate;
                    reduced = true;
                    granularity = 2.max(granularity - 1);
                    break;
                }
            }

            if !reduced {
                granularity += 1;
            }
        }

        // Try removing individual steps.
        let mut i = 0;
        while i < current.len() && iterations < self.max_iterations {
            iterations += 1;
            let mut candidate = current.clone();
            candidate.remove(i);

            if !candidate.is_empty() && self.oracle.reproduces_error(&candidate) {
                current = candidate;
                // Don't increment i — next element shifted into position
            } else {
                i += 1;
            }
        }

        let removed: Vec<TraceStep> = trace.steps.iter()
            .filter(|s| !current.iter().any(|c| c.index == s.index))
            .cloned()
            .collect();

        MinimizationResult {
            minimized_length: current.len(),
            minimal_trace: ErrorTrace::new(current, &trace.error),
            removed_steps: removed,
            original_length,
            iterations,
        }
    }
}

/// Score the relevance of trace steps.
pub(crate) fn score_relevance(trace: &ErrorTrace) -> Vec<f64> {
    let len = trace.len();
    if len == 0 { return vec![]; }

    // Simple heuristic: later steps are more relevant (closer to error).
    trace.steps.iter().enumerate().map(|(i, _)| {
        (i + 1) as f64 / len as f64
    }).collect()
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_trace(n: usize) -> ErrorTrace {
        let steps: Vec<TraceStep> = (0..n)
            .map(|i| TraceStep::new(i, format!("step {i}")))
            .collect();
        ErrorTrace::new(steps, "assertion failed")
    }

    #[test]
    fn test_trace_step_creation() {
        let s = TraceStep::new(0, "init");
        assert_eq!(s.index, 0);
        assert!(s.relevant);
    }

    #[test]
    fn test_trace_step_with_score() {
        let s = TraceStep::new(0, "init").with_score(0.0);
        assert!(!s.relevant);
        let s2 = TraceStep::new(1, "step").with_score(0.8);
        assert!(s2.relevant);
    }

    #[test]
    fn test_error_trace_basic() {
        let trace = sample_trace(5);
        assert_eq!(trace.len(), 5);
        assert!(!trace.is_empty());
    }

    #[test]
    fn test_minimize_with_always_reproduces() {
        let trace = sample_trace(10);
        let oracle = AlwaysReproduces;
        let minimizer = TraceMinimizer::new(&oracle);
        let result = minimizer.minimize(&trace);

        // Should reduce to 1 step since AlwaysReproduces accepts any non-empty trace.
        assert_eq!(result.minimized_length, 1);
        assert_eq!(result.original_length, 10);
        assert!(result.reduction_ratio() > 0.8);
    }

    #[test]
    fn test_minimize_with_required_step() {
        let trace = sample_trace(10);
        let oracle = RequiresStep { required_index: 5 };
        let minimizer = TraceMinimizer::new(&oracle);
        let result = minimizer.minimize(&trace);

        // Should reduce to just the required step.
        assert_eq!(result.minimized_length, 1);
        assert!(result.minimal_trace.steps.iter().any(|s| s.index == 5));
    }

    #[test]
    fn test_minimize_empty_trace() {
        let trace = ErrorTrace::new(vec![], "error");
        let oracle = AlwaysReproduces;
        let minimizer = TraceMinimizer::new(&oracle);
        let result = minimizer.minimize(&trace);
        assert_eq!(result.minimized_length, 0);
        assert_eq!(result.original_length, 0);
    }

    #[test]
    fn test_minimize_single_step() {
        let trace = sample_trace(1);
        let oracle = AlwaysReproduces;
        let minimizer = TraceMinimizer::new(&oracle);
        let result = minimizer.minimize(&trace);
        assert_eq!(result.minimized_length, 1);
    }

    #[test]
    fn test_reduction_ratio() {
        let result = MinimizationResult {
            minimal_trace: ErrorTrace::new(vec![], "e"),
            removed_steps: vec![],
            original_length: 10,
            minimized_length: 3,
            iterations: 5,
        };
        assert!((result.reduction_ratio() - 0.7).abs() < 0.01);
    }

    #[test]
    fn test_reduction_ratio_no_reduction() {
        let result = MinimizationResult {
            minimal_trace: ErrorTrace::new(vec![], "e"),
            removed_steps: vec![],
            original_length: 5,
            minimized_length: 5,
            iterations: 0,
        };
        assert_eq!(result.reduction_ratio(), 0.0);
    }

    #[test]
    fn test_reduction_ratio_empty() {
        let result = MinimizationResult {
            minimal_trace: ErrorTrace::new(vec![], "e"),
            removed_steps: vec![],
            original_length: 0,
            minimized_length: 0,
            iterations: 0,
        };
        assert_eq!(result.reduction_ratio(), 0.0);
    }

    #[test]
    fn test_score_relevance() {
        let trace = sample_trace(4);
        let scores = score_relevance(&trace);
        assert_eq!(scores.len(), 4);
        assert!(scores[0] < scores[3]); // later steps more relevant
    }

    #[test]
    fn test_score_relevance_empty() {
        let trace = ErrorTrace::new(vec![], "e");
        assert!(score_relevance(&trace).is_empty());
    }

    #[test]
    fn test_max_iterations_limit() {
        let trace = sample_trace(100);
        let oracle = AlwaysReproduces;
        let minimizer = TraceMinimizer::new(&oracle).with_max_iterations(5);
        let result = minimizer.minimize(&trace);
        assert!(result.iterations <= 6); // may slightly exceed due to loop structure
    }

    #[test]
    fn test_removed_steps_tracked() {
        let trace = sample_trace(5);
        let oracle = RequiresStep { required_index: 2 };
        let minimizer = TraceMinimizer::new(&oracle);
        let result = minimizer.minimize(&trace);
        assert!(!result.removed_steps.is_empty());
        assert!(result.removed_steps.iter().all(|s| s.index != 2));
    }
}
