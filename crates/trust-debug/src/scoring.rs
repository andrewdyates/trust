// trust-debug/scoring.rs: Violation severity scoring and prioritization
//
// Computes composite scores for security violations based on severity,
// exploitability, and blast radius. Used by the verification loop to
// prioritize which violations to address first.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::{DebugReport, ExploitChain, SecurityViolation, SecurityViolationKind, Severity};

/// Composite score for a single violation.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct ScoredViolation {
    /// Index into the original violations list.
    pub original_index: usize,
    /// Reference to the violation ID.
    pub violation_id: String,
    /// Composite score (0.0 to 1.0, higher = more severe).
    pub composite_score: f64,
    /// Severity component (0.0 to 1.0).
    pub severity_score: f64,
    /// Exploitability component (0.0 to 1.0).
    pub exploitability_score: f64,
    /// Blast radius component (0.0 to 1.0).
    pub blast_radius_score: f64,
    /// Rank (1 = highest priority).
    pub rank: usize,
    /// Suggested priority for the verification loop.
    pub suggested_priority: SuggestedPriority,
}

/// Suggested priority level for a scored violation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SuggestedPriority {
    /// Must fix immediately — blocks release.
    Critical,
    /// Fix in current iteration.
    High,
    /// Fix when bandwidth allows.
    Medium,
    /// Informational — may defer.
    Low,
}

/// Configuration for the scoring algorithm.
#[derive(Debug, Clone)]
pub(crate) struct ScoringConfig {
    /// Weight for the severity factor (default 0.5).
    pub severity_weight: f64,
    /// Weight for the exploitability factor (default 0.3).
    pub exploitability_weight: f64,
    /// Weight for the blast radius factor (default 0.2).
    pub blast_radius_weight: f64,
    /// Composite score threshold above which a violation is "critical" (default 0.8).
    pub critical_threshold: f64,
    /// Composite score threshold for "high" priority (default 0.6).
    pub high_threshold: f64,
    /// Composite score threshold for "medium" priority (default 0.3).
    pub medium_threshold: f64,
}

impl Default for ScoringConfig {
    fn default() -> Self {
        Self {
            severity_weight: 0.5,
            exploitability_weight: 0.3,
            blast_radius_weight: 0.2,
            critical_threshold: 0.8,
            high_threshold: 0.6,
            medium_threshold: 0.3,
        }
    }
}

/// Score all violations in a debug report.
///
/// Returns a list of `ScoredViolation`s sorted by composite score (descending),
/// with ties broken by exploitability score (descending). Each entry includes
/// the rank and a suggested priority level.
#[must_use]
pub(crate) fn score_violations(report: &DebugReport, config: &ScoringConfig) -> Vec<ScoredViolation> {
    let mut scored: Vec<ScoredViolation> = report
        .violations
        .iter()
        .enumerate()
        .map(|(i, v)| {
            let severity_score = severity_to_score(v.severity);
            let exploitability_score = exploitability_score(v, &report.chains);
            let blast_radius_score = blast_radius_score(v, report);

            let composite = config.severity_weight * severity_score
                + config.exploitability_weight * exploitability_score
                + config.blast_radius_weight * blast_radius_score;
            // Clamp to [0.0, 1.0]
            let composite = composite.clamp(0.0, 1.0);

            let suggested_priority = if composite >= config.critical_threshold {
                SuggestedPriority::Critical
            } else if composite >= config.high_threshold {
                SuggestedPriority::High
            } else if composite >= config.medium_threshold {
                SuggestedPriority::Medium
            } else {
                SuggestedPriority::Low
            };

            ScoredViolation {
                original_index: i,
                violation_id: v.id.clone(),
                composite_score: composite,
                severity_score,
                exploitability_score,
                blast_radius_score,
                rank: 0, // filled after sorting
                suggested_priority,
            }
        })
        .collect();

    // Sort by composite score descending, break ties by exploitability descending
    scored.sort_by(|a, b| {
        b.composite_score
            .partial_cmp(&a.composite_score)
            .unwrap_or(std::cmp::Ordering::Equal)
            .then_with(|| {
                b.exploitability_score
                    .partial_cmp(&a.exploitability_score)
                    .unwrap_or(std::cmp::Ordering::Equal)
            })
    });

    // Assign ranks (1-based)
    for (i, sv) in scored.iter_mut().enumerate() {
        sv.rank = i + 1;
    }

    scored
}

/// Map severity enum to a 0.0-1.0 score.
fn severity_to_score(severity: Severity) -> f64 {
    match severity {
        Severity::Critical => 1.0,
        Severity::High => 0.8,
        Severity::Medium => 0.5,
        Severity::Low => 0.2,
        Severity::Info => 0.05,
    }
}

/// Compute exploitability score for a violation.
///
/// Higher if:
/// - The violation kind is directly exploitable (injection, RCE)
/// - The violation has a concrete counterexample (solver proved it reachable)
/// - The violation appears in an exploitation chain
fn exploitability_score(violation: &SecurityViolation, chains: &[ExploitChain]) -> f64 {
    let mut score = kind_exploitability(&violation.kind);

    // Counterexample proves reachability => higher exploitability
    if violation.counterexample.is_some() {
        score += 0.2;
    }

    // Part of an exploitation chain => higher exploitability
    let in_chain = chains
        .iter()
        .any(|c| c.violation_ids.contains(&violation.id));
    if in_chain {
        score += 0.2;
    }

    // Has a concrete data flow path => easier to exploit
    if !violation.flow_path.is_empty() {
        score += 0.1;
    }

    score.clamp(0.0, 1.0)
}

/// Base exploitability by violation kind.
fn kind_exploitability(kind: &SecurityViolationKind) -> f64 {
    match kind {
        // Directly exploitable for RCE
        SecurityViolationKind::TaintedIndirectCall { .. }
        | SecurityViolationKind::CommandInjection { .. }
        | SecurityViolationKind::TaintedSyscall { .. }
        | SecurityViolationKind::ArbitraryWrite { .. } => 0.9,

        // High exploitability
        SecurityViolationKind::SqlInjection { .. }
        | SecurityViolationKind::FormatStringInjection { .. }
        | SecurityViolationKind::BufferOverflow { .. }
        | SecurityViolationKind::UseAfterFree { .. } => 0.8,

        // Medium exploitability
        SecurityViolationKind::IntegerOverflowToBufferCorruption { .. }
        | SecurityViolationKind::DoubleFree { .. }
        | SecurityViolationKind::PrivilegeEscalation { .. } => 0.6,

        // Conditional exploitability
        SecurityViolationKind::Toctou { .. }
        | SecurityViolationKind::DataRace { .. }
        | SecurityViolationKind::IndexOutOfBounds { .. } => 0.5,

        // Rarely directly exploitable
        SecurityViolationKind::Deadlock { .. }
        | SecurityViolationKind::ArithmeticOverflow { .. }
        | SecurityViolationKind::TaintFlow { .. } => 0.3,

        // Not exploitable
        SecurityViolationKind::DivisionByZero
        | SecurityViolationKind::UnreachableReached
        | SecurityViolationKind::DeadCode { .. } => 0.1,
    }
}

/// Compute blast radius: how much of the codebase is affected.
///
/// Higher if:
/// - The violation is in a function that appears in many chains
/// - The violation kind affects control flow (vs. just data)
/// - The violation is in a public/entry-point function
fn blast_radius_score(violation: &SecurityViolation, report: &DebugReport) -> f64 {
    let mut score = 0.0;

    // Count how many chains reference this violation
    let chain_count = report
        .chains
        .iter()
        .filter(|c| c.violation_ids.contains(&violation.id))
        .count();
    score += (chain_count as f64 * 0.2).min(0.6);

    // Control-flow violations have higher blast radius than data-only
    if is_control_flow_violation(&violation.kind) {
        score += 0.3;
    }

    // Violations in functions that have multiple violations indicate a
    // hot spot — fixing one may address several
    let same_func_count = report
        .violations
        .iter()
        .filter(|v| v.function == violation.function)
        .count();
    if same_func_count > 1 {
        score += (same_func_count as f64 * 0.05).min(0.3);
    }

    score.clamp(0.0, 1.0)
}

fn is_control_flow_violation(kind: &SecurityViolationKind) -> bool {
    matches!(
        kind,
        SecurityViolationKind::TaintedIndirectCall { .. }
            | SecurityViolationKind::CommandInjection { .. }
            | SecurityViolationKind::TaintedSyscall { .. }
            | SecurityViolationKind::BufferOverflow { .. }
            | SecurityViolationKind::ArbitraryWrite { .. }
            | SecurityViolationKind::UseAfterFree { .. }
            | SecurityViolationKind::DoubleFree { .. }
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::DebugSummary;

    fn make_violation(id: &str, severity: Severity, kind: SecurityViolationKind) -> SecurityViolation {
        SecurityViolation {
            id: id.to_string(),
            severity,
            kind,
            function: "test::func".to_string(),
            location: None,
            description: String::new(),
            flow_path: vec![],
            counterexample: None,
            solver: "test".to_string(),
            time_ms: 0,
        }
    }

    fn make_report(violations: Vec<SecurityViolation>, chains: Vec<ExploitChain>) -> DebugReport {
        let summary = DebugSummary::from_violations(&violations, &chains);
        DebugReport {
            target: "test".to_string(),
            violations,
            chains,
            summary,
        }
    }

    #[test]
    fn test_score_empty_report() {
        let report = make_report(vec![], vec![]);
        let scored = score_violations(&report, &ScoringConfig::default());
        assert!(scored.is_empty());
    }

    #[test]
    fn test_critical_ranks_above_medium() {
        let report = make_report(
            vec![
                make_violation(
                    "V1",
                    Severity::Medium,
                    SecurityViolationKind::ArithmeticOverflow {
                        operation: "Add".to_string(),
                    },
                ),
                make_violation(
                    "V2",
                    Severity::Critical,
                    SecurityViolationKind::SqlInjection {
                        sink_func: "query".to_string(),
                        taint_source: "user-input".to_string(),
                    },
                ),
            ],
            vec![],
        );

        let scored = score_violations(&report, &ScoringConfig::default());
        assert_eq!(scored.len(), 2);
        assert_eq!(scored[0].violation_id, "V2"); // Critical first
        assert_eq!(scored[0].rank, 1);
        assert_eq!(scored[1].violation_id, "V1"); // Medium second
        assert_eq!(scored[1].rank, 2);
        assert!(scored[0].composite_score > scored[1].composite_score);
    }

    #[test]
    fn test_chain_membership_boosts_score() {
        let v1 = make_violation(
            "V1",
            Severity::Medium,
            SecurityViolationKind::ArithmeticOverflow {
                operation: "Add".to_string(),
            },
        );
        let v2 = make_violation(
            "V2",
            Severity::Medium,
            SecurityViolationKind::ArithmeticOverflow {
                operation: "Mul".to_string(),
            },
        );
        let chain = ExploitChain {
            name: "test-chain".to_string(),
            severity: Severity::Critical,
            violation_ids: vec!["V1".to_string()],
            description: "test".to_string(),
        };

        let report = make_report(vec![v1, v2], vec![chain]);
        let scored = score_violations(&report, &ScoringConfig::default());

        // V1 is in a chain, should score higher than V2
        let v1_score = scored.iter().find(|s| s.violation_id == "V1").expect("V1");
        let v2_score = scored.iter().find(|s| s.violation_id == "V2").expect("V2");
        assert!(
            v1_score.composite_score > v2_score.composite_score,
            "V1 (in chain) should score higher: {} vs {}",
            v1_score.composite_score,
            v2_score.composite_score,
        );
    }

    #[test]
    fn test_counterexample_boosts_exploitability() {
        let mut v_with_cx = make_violation(
            "V1",
            Severity::Medium,
            SecurityViolationKind::IndexOutOfBounds {
                index_expr: "i".to_string(),
            },
        );
        v_with_cx.counterexample = Some(trust_types::Counterexample { trace: None,
            assignments: vec![("i".to_string(), trust_types::CounterexampleValue::Uint(999))],
        });

        let v_without_cx = make_violation(
            "V2",
            Severity::Medium,
            SecurityViolationKind::IndexOutOfBounds {
                index_expr: "j".to_string(),
            },
        );

        let report = make_report(vec![v_with_cx, v_without_cx], vec![]);
        let scored = score_violations(&report, &ScoringConfig::default());

        let s1 = scored.iter().find(|s| s.violation_id == "V1").expect("V1");
        let s2 = scored.iter().find(|s| s.violation_id == "V2").expect("V2");
        assert!(
            s1.exploitability_score > s2.exploitability_score,
            "counterexample should boost exploitability"
        );
    }

    #[test]
    fn test_suggested_priority_thresholds() {
        let config = ScoringConfig::default();
        let report = make_report(
            vec![
                make_violation(
                    "V1",
                    Severity::Critical,
                    SecurityViolationKind::CommandInjection {
                        command_func: "exec".to_string(),
                        taint_source: "user".to_string(),
                    },
                ),
                make_violation("V2", Severity::Info, SecurityViolationKind::DeadCode {
                    function: "unused".to_string(),
                }),
            ],
            vec![],
        );

        let scored = score_violations(&report, &config);
        let critical = scored.iter().find(|s| s.violation_id == "V1").expect("V1");
        let info = scored.iter().find(|s| s.violation_id == "V2").expect("V2");

        assert_eq!(critical.suggested_priority, SuggestedPriority::Critical);
        assert_eq!(info.suggested_priority, SuggestedPriority::Low);
    }

    #[test]
    fn test_scores_are_clamped() {
        // Even with extreme weights, scores stay in [0, 1]
        let config = ScoringConfig {
            severity_weight: 2.0,
            exploitability_weight: 2.0,
            blast_radius_weight: 2.0,
            ..Default::default()
        };

        let report = make_report(
            vec![make_violation(
                "V1",
                Severity::Critical,
                SecurityViolationKind::CommandInjection {
                    command_func: "exec".to_string(),
                    taint_source: "user".to_string(),
                },
            )],
            vec![],
        );

        let scored = score_violations(&report, &config);
        assert!(scored[0].composite_score <= 1.0);
        assert!(scored[0].composite_score >= 0.0);
    }

    #[test]
    fn test_tie_broken_by_exploitability() {
        // Two violations with same severity but different exploitability
        let report = make_report(
            vec![
                make_violation(
                    "V1",
                    Severity::High,
                    SecurityViolationKind::Deadlock {
                        lock_cycle: vec!["A".into(), "B".into()],
                    },
                ),
                make_violation(
                    "V2",
                    Severity::High,
                    SecurityViolationKind::BufferOverflow {
                        write_size: "n+1".to_string(),
                        buffer_size: "n".to_string(),
                    },
                ),
            ],
            vec![],
        );

        let scored = score_violations(&report, &ScoringConfig::default());
        // BufferOverflow is more exploitable than Deadlock
        assert_eq!(scored[0].violation_id, "V2");
        assert_eq!(scored[1].violation_id, "V1");
    }

    #[test]
    fn test_default_config_weights_sum_to_one() {
        let config = ScoringConfig::default();
        let sum = config.severity_weight + config.exploitability_weight + config.blast_radius_weight;
        assert!((sum - 1.0).abs() < f64::EPSILON, "weights should sum to 1.0: got {sum}");
    }

    #[test]
    fn test_severity_ordering_in_scores() {
        assert!(severity_to_score(Severity::Critical) > severity_to_score(Severity::High));
        assert!(severity_to_score(Severity::High) > severity_to_score(Severity::Medium));
        assert!(severity_to_score(Severity::Medium) > severity_to_score(Severity::Low));
        assert!(severity_to_score(Severity::Low) > severity_to_score(Severity::Info));
    }
}
