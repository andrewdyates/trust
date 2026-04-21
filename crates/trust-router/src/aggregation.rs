// trust-router/aggregation.rs: Result aggregation for portfolio solver
//
// tRust: Aggregates verification results from multiple strategies. Handles
// partial results (e.g., timeout from one solver, success from another),
// merges counterexamples, and selects the best overall result.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashSet;
use trust_types::{Counterexample, CounterexampleValue, ProofStrength, VerificationResult};

/// tRust: A single solver's contribution to the aggregated result.
#[derive(Debug, Clone)]
pub struct SolverContribution {
    /// Name of the solver/strategy that produced this result.
    pub solver: String,
    /// The verification result.
    pub result: VerificationResult,
    /// Wall-clock time in milliseconds.
    pub time_ms: u64,
}

/// tRust: Aggregated result from multiple solver strategies.
#[derive(Debug, Clone)]
pub struct AggregatedResult {
    /// The best result selected from all contributions.
    pub best: VerificationResult,
    /// Which solver produced the best result.
    pub best_solver: String,
    /// All individual contributions, ordered by arrival time.
    pub contributions: Vec<SolverContribution>,
    /// Merged counterexample (if any solver found one).
    pub merged_counterexample: Option<Counterexample>,
    /// Total wall-clock time for the entire aggregation.
    pub total_time_ms: u64,
}

impl AggregatedResult {
    /// Whether the best result is definitive (Proved or Failed).
    #[must_use]
    pub fn is_definitive(&self) -> bool {
        self.best.is_proved() || self.best.is_failed()
    }

    /// Number of solvers that contributed.
    #[must_use]
    pub fn solver_count(&self) -> usize {
        self.contributions.len()
    }

    /// How many solvers produced a Proved result.
    #[must_use]
    pub fn proved_count(&self) -> usize {
        self.contributions
            .iter()
            .filter(|c| c.result.is_proved())
            .count()
    }

    /// How many solvers produced a Failed result.
    #[must_use]
    pub fn failed_count(&self) -> usize {
        self.contributions
            .iter()
            .filter(|c| c.result.is_failed())
            .count()
    }

    /// How many solvers timed out.
    #[must_use]
    pub fn timeout_count(&self) -> usize {
        self.contributions
            .iter()
            .filter(|c| matches!(c.result, VerificationResult::Timeout { .. }))
            .count()
    }
}

/// tRust: Aggregate results from multiple solver contributions.
///
/// Selection priority:
/// 1. Proved results (strongest proof strength wins).
/// 2. Failed results (with counterexample preferred over without).
/// 3. Timeout / Unknown (first non-timeout preferred).
///
/// Counterexamples from all Failed results are merged into a single
/// combined counterexample.
#[must_use]
pub fn aggregate(contributions: Vec<SolverContribution>) -> AggregatedResult {
    if contributions.is_empty() {
        return AggregatedResult {
            best: VerificationResult::Unknown {
                solver: "none".to_string(),
                time_ms: 0,
                reason: "no solver contributions".to_string(),
            },
            best_solver: "none".to_string(),
            contributions: Vec::new(),
            merged_counterexample: None,
            total_time_ms: 0,
        };
    }

    let total_time_ms = contributions.iter().map(|c| c.time_ms).max().unwrap_or(0);

    // Collect all counterexamples for merging.
    let counterexamples: Vec<&Counterexample> = contributions
        .iter()
        .filter_map(|c| match &c.result {
            VerificationResult::Failed { counterexample: Some(cex), .. } => Some(cex),
            _ => None,
        })
        .collect();
    let merged_counterexample = merge_counterexamples(&counterexamples);

    // Select the best result.
    // SAFETY: We returned early above when contributions.is_empty().
    let (best_idx, _) = contributions
        .iter()
        .enumerate()
        .max_by(|(_, a), (_, b)| result_quality(&a.result).cmp(&result_quality(&b.result)))
        .unwrap_or_else(|| unreachable!("contributions empty after non-empty check"));

    let best = contributions[best_idx].result.clone();
    let best_solver = contributions[best_idx].solver.clone();

    AggregatedResult {
        best,
        best_solver,
        contributions,
        merged_counterexample,
        total_time_ms,
    }
}

/// tRust: Merge multiple counterexamples into one.
///
/// Combines variable assignments from all counterexamples. When the same
/// variable appears in multiple counterexamples, the first assignment wins
/// (stable ordering).
#[must_use]
pub fn merge_counterexamples(counterexamples: &[&Counterexample]) -> Option<Counterexample> {
    if counterexamples.is_empty() {
        return None;
    }

    let mut seen = FxHashSet::default();
    let mut merged_assignments: Vec<(String, CounterexampleValue)> = Vec::new();

    for cex in counterexamples {
        for (name, value) in &cex.assignments {
            if seen.insert(name.clone()) {
                merged_assignments.push((name.clone(), value.clone()));
            }
        }
    }

    if merged_assignments.is_empty() {
        return None;
    }

    Some(Counterexample::new(merged_assignments))
}

/// tRust: Quality score for a verification result (higher = better).
///
/// Used to select the "best" result from multiple contributions.
fn result_quality(result: &VerificationResult) -> u32 {
    match result {
        VerificationResult::Proved { strength, .. } => 100 + strength_bonus(strength),
        VerificationResult::Failed { counterexample: Some(_), .. } => 80,
        VerificationResult::Failed { counterexample: None, .. } => 70,
        VerificationResult::Unknown { .. } => 10,
        VerificationResult::Timeout { .. } => 5,
        // tRust #734: non-panicking fallback for #[non_exhaustive] forward compat
        _ => 0,
    }
}

/// Bonus for stronger proof strengths.
fn strength_bonus(strength: &ProofStrength) -> u32 {
    use trust_types::ReasoningKind;
    match &strength.reasoning {
        ReasoningKind::Constructive => 50,
        ReasoningKind::Deductive => 40,
        ReasoningKind::Inductive | ReasoningKind::Pdr | ReasoningKind::ChcSpacer => 30,
        ReasoningKind::Smt => 20,
        ReasoningKind::BoundedModelCheck { depth } => (*depth).min(10) as u32,
        _ => 20, // default to SMT-level for unknown future variants
    }
}

#[cfg(test)]
mod tests {
    use trust_types::*;

    use super::*;

    fn proved(solver: &str, strength: ProofStrength) -> VerificationResult {
        VerificationResult::Proved {
            solver: solver.to_string(),
            time_ms: 10,
            strength,
            proof_certificate: None,
                solver_warnings: None,
        }
    }

    fn failed_with_cex(solver: &str) -> VerificationResult {
        VerificationResult::Failed {
            solver: solver.to_string(),
            time_ms: 10,
            counterexample: Some(Counterexample::new(vec![
                (format!("{solver}_x"), CounterexampleValue::Int(42)),
            ])),
        }
    }

    fn failed_no_cex(solver: &str) -> VerificationResult {
        VerificationResult::Failed {
            solver: solver.to_string(),
            time_ms: 10,
            counterexample: None,
        }
    }

    fn unknown(solver: &str) -> VerificationResult {
        VerificationResult::Unknown {
            solver: solver.to_string(),
            time_ms: 10,
            reason: "unknown".to_string(),
        }
    }

    fn timeout(solver: &str) -> VerificationResult {
        VerificationResult::Timeout {
            solver: solver.to_string(),
            timeout_ms: 5000,
        }
    }

    fn contrib(solver: &str, result: VerificationResult) -> SolverContribution {
        SolverContribution {
            solver: solver.to_string(),
            result,
            time_ms: 10,
        }
    }

    #[test]
    fn test_aggregate_empty() {
        let result = aggregate(vec![]);
        assert!(!result.is_definitive());
        assert_eq!(result.solver_count(), 0);
        assert_eq!(result.best_solver, "none");
    }

    #[test]
    fn test_aggregate_single_proved() {
        let contributions = vec![
            contrib("z4", proved("z4", ProofStrength::smt_unsat())),
        ];
        let result = aggregate(contributions);
        assert!(result.is_definitive());
        assert!(result.best.is_proved());
        assert_eq!(result.best_solver, "z4");
        assert_eq!(result.proved_count(), 1);
        assert_eq!(result.failed_count(), 0);
    }

    #[test]
    fn test_aggregate_proved_beats_failed() {
        let contributions = vec![
            contrib("zani", failed_with_cex("zani")),
            contrib("z4", proved("z4", ProofStrength::smt_unsat())),
        ];
        let result = aggregate(contributions);
        assert!(result.best.is_proved());
        assert_eq!(result.best_solver, "z4");
    }

    #[test]
    fn test_aggregate_stronger_proof_wins() {
        let contributions = vec![
            contrib("z4", proved("z4", ProofStrength::smt_unsat())),
            contrib("cegar", proved("cegar", ProofStrength::inductive())),
        ];
        let result = aggregate(contributions);
        assert!(result.best.is_proved());
        // Inductive (bonus 30) beats SmtUnsat (bonus 20).
        assert_eq!(result.best_solver, "cegar");
    }

    #[test]
    fn test_aggregate_failed_with_cex_beats_without() {
        let contributions = vec![
            contrib("zani", failed_no_cex("zani")),
            contrib("z4", failed_with_cex("z4")),
        ];
        let result = aggregate(contributions);
        assert!(result.best.is_failed());
        assert_eq!(result.best_solver, "z4");
    }

    #[test]
    fn test_aggregate_failed_beats_unknown() {
        let contributions = vec![
            contrib("z4", unknown("z4")),
            contrib("zani", failed_no_cex("zani")),
        ];
        let result = aggregate(contributions);
        assert!(result.best.is_failed());
        assert_eq!(result.best_solver, "zani");
    }

    #[test]
    fn test_aggregate_unknown_beats_timeout() {
        let contributions = vec![
            contrib("z4", timeout("z4")),
            contrib("zani", unknown("zani")),
        ];
        let result = aggregate(contributions);
        assert_eq!(result.best_solver, "zani");
        assert!(matches!(result.best, VerificationResult::Unknown { .. }));
    }

    #[test]
    fn test_aggregate_timeout_count() {
        let contributions = vec![
            contrib("z4", timeout("z4")),
            contrib("zani", timeout("zani")),
            contrib("cegar", proved("cegar", ProofStrength::inductive())),
        ];
        let result = aggregate(contributions);
        assert_eq!(result.timeout_count(), 2);
        assert_eq!(result.proved_count(), 1);
        assert!(result.best.is_proved());
    }

    #[test]
    fn test_merge_counterexamples_empty() {
        let merged = merge_counterexamples(&[]);
        assert!(merged.is_none());
    }

    #[test]
    fn test_merge_counterexamples_single() {
        let cex = Counterexample::new(vec![
            ("x".to_string(), CounterexampleValue::Int(1)),
        ]);
        let merged = merge_counterexamples(&[&cex]).expect("should merge");
        assert_eq!(merged.assignments.len(), 1);
        assert_eq!(merged.assignments[0].0, "x");
    }

    #[test]
    fn test_merge_counterexamples_disjoint() {
        let cex1 = Counterexample::new(vec![
            ("x".to_string(), CounterexampleValue::Int(1)),
        ]);
        let cex2 = Counterexample::new(vec![
            ("y".to_string(), CounterexampleValue::Int(2)),
        ]);
        let merged = merge_counterexamples(&[&cex1, &cex2]).expect("should merge");
        assert_eq!(merged.assignments.len(), 2);
    }

    #[test]
    fn test_merge_counterexamples_duplicate_vars() {
        let cex1 = Counterexample::new(vec![
            ("x".to_string(), CounterexampleValue::Int(1)),
        ]);
        let cex2 = Counterexample::new(vec![
            ("x".to_string(), CounterexampleValue::Int(99)),
            ("y".to_string(), CounterexampleValue::Int(2)),
        ]);
        let merged = merge_counterexamples(&[&cex1, &cex2]).expect("should merge");
        // x from cex1 wins (first-seen).
        assert_eq!(merged.assignments.len(), 2);
        let x_val = merged
            .assignments
            .iter()
            .find(|(n, _)| n == "x")
            .expect("x should exist");
        assert!(matches!(x_val.1, CounterexampleValue::Int(1)));
    }

    #[test]
    fn test_aggregate_merges_counterexamples() {
        let contributions = vec![
            contrib("z4", failed_with_cex("z4")),
            contrib("zani", failed_with_cex("zani")),
        ];
        let result = aggregate(contributions);
        let merged = result.merged_counterexample.expect("should have merged cex");
        // z4_x and zani_x should both appear.
        assert_eq!(merged.assignments.len(), 2);
    }

    #[test]
    fn test_aggregate_total_time() {
        let contributions = vec![
            SolverContribution {
                solver: "z4".to_string(),
                result: proved("z4", ProofStrength::smt_unsat()),
                time_ms: 100,
            },
            SolverContribution {
                solver: "zani".to_string(),
                result: timeout("zani"),
                time_ms: 5000,
            },
        ];
        let result = aggregate(contributions);
        assert_eq!(result.total_time_ms, 5000);
    }

    #[test]
    fn test_result_quality_ordering() {
        // Proved > Failed+cex > Failed > Unknown > Timeout
        let p = result_quality(&proved("z4", ProofStrength::smt_unsat()));
        let fc = result_quality(&failed_with_cex("z4"));
        let f = result_quality(&failed_no_cex("z4"));
        let u = result_quality(&unknown("z4"));
        let t = result_quality(&timeout("z4"));

        assert!(p > fc, "proved ({p}) should beat failed+cex ({fc})");
        assert!(fc > f, "failed+cex ({fc}) should beat failed ({f})");
        assert!(f > u, "failed ({f}) should beat unknown ({u})");
        assert!(u > t, "unknown ({u}) should beat timeout ({t})");
    }

    #[test]
    fn test_strength_bonus_ordering() {
        let constructive = strength_bonus(&ProofStrength::constructive());
        let deductive = strength_bonus(&ProofStrength::deductive());
        let inductive = strength_bonus(&ProofStrength::inductive());
        let smt = strength_bonus(&ProofStrength::smt_unsat());
        let bounded = strength_bonus(&ProofStrength::bounded(5));

        assert!(constructive > deductive);
        assert!(deductive > inductive);
        assert!(inductive > smt);
        assert!(smt > bounded);
    }
}
