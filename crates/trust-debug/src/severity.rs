// trust-debug/severity.rs: Numerical severity scoring (0-100) with categories
//
// Extends the existing scoring module with a finer-grained 0-100 numerical
// severity score per violation, factoring in violation kind, context (flow
// path length, counterexample presence), and potential impact. The Prioritizer
// combines severity with exploitability to produce a final priority ordering.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::exploitability::{assess_exploitability, ExploitabilityAssessment};
use crate::{ExploitChain, SecurityViolation, SecurityViolationKind, Severity};

/// Numerical severity score on a 0-100 scale with a category.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct SeverityScore {
    /// Numerical score (0 = informational, 100 = critical RCE).
    pub score: u8,
    /// Categorical classification.
    pub category: SeverityCategory,
    /// Brief rationale for the assigned score.
    pub rationale: String,
}

/// Categorical severity classification.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize)]
pub(crate) enum SeverityCategory {
    /// Score 90-100: Allows arbitrary code execution or full system compromise.
    Critical,
    /// Score 70-89: Significant data corruption, info disclosure, or privilege escalation.
    High,
    /// Score 40-69: Safety violation exploitable under certain conditions.
    Medium,
    /// Score 20-39: Safety violation unlikely to be exploitable.
    Low,
    /// Score 0-19: Informational finding (dead code, style).
    Info,
}

impl SeverityCategory {
    /// Map from a 0-100 score to its category.
    #[must_use]
    pub(crate) fn from_score(score: u8) -> Self {
        match score {
            90..=100 => Self::Critical,
            70..=89 => Self::High,
            40..=69 => Self::Medium,
            20..=39 => Self::Low,
            _ => Self::Info,
        }
    }
}

/// Compute a numerical 0-100 severity score for a single violation.
///
/// The base score comes from the violation kind. Modifiers adjust it:
/// - +5 if a concrete counterexample exists (proves reachability)
/// - +5 if a data flow path exists (shows exploitability)
/// - +5 if the flow path is long (3+ steps, complex attack surface)
/// - +5 if the violation is part of an exploitation chain
/// - Capped at 100.
#[must_use]
pub(crate) fn score_violation(violation: &SecurityViolation, chains: &[ExploitChain]) -> SeverityScore {
    let base = base_score(&violation.kind);

    let mut modifiers = 0i16;
    let mut reasons = vec![format!("base={base} ({})", kind_label(&violation.kind))];

    // Counterexample proves the violation is reachable
    if violation.counterexample.is_some() {
        modifiers += 5;
        reasons.push("counterexample=+5".to_string());
    }

    // Data flow path shows attacker-controlled input reaches the sink
    if !violation.flow_path.is_empty() {
        modifiers += 5;
        reasons.push("flow_path=+5".to_string());

        if violation.flow_path.len() >= 3 {
            modifiers += 5;
            reasons.push("long_flow=+5".to_string());
        }
    }

    // Part of an exploitation chain elevates severity
    let in_chain = chains
        .iter()
        .any(|c| c.violation_ids.contains(&violation.id));
    if in_chain {
        modifiers += 5;
        reasons.push("in_chain=+5".to_string());
    }

    let final_score = (base as i16 + modifiers).clamp(0, 100) as u8;
    let category = SeverityCategory::from_score(final_score);

    SeverityScore {
        score: final_score,
        category,
        rationale: reasons.join(", "),
    }
}

/// Base severity score by violation kind (0-100).
fn base_score(kind: &SecurityViolationKind) -> u8 {
    match kind {
        // RCE-class: 95
        SecurityViolationKind::TaintedIndirectCall { .. }
        | SecurityViolationKind::CommandInjection { .. }
        | SecurityViolationKind::TaintedSyscall { .. }
        | SecurityViolationKind::ArbitraryWrite { .. } => 95,

        // Critical injection / memory corruption: 90
        SecurityViolationKind::SqlInjection { .. }
        | SecurityViolationKind::FormatStringInjection { .. }
        | SecurityViolationKind::BufferOverflow { .. }
        | SecurityViolationKind::UseAfterFree { .. } => 90,

        // High: indirect memory corruption, double-free, privilege escalation
        SecurityViolationKind::IntegerOverflowToBufferCorruption { .. }
        | SecurityViolationKind::DoubleFree { .. }
        | SecurityViolationKind::PrivilegeEscalation { .. } => 75,

        // Medium-high: concurrency issues, OOB
        SecurityViolationKind::Toctou { .. }
        | SecurityViolationKind::DataRace { .. }
        | SecurityViolationKind::IndexOutOfBounds { .. } => 60,

        // Medium: generic safety
        SecurityViolationKind::ArithmeticOverflow { .. }
        | SecurityViolationKind::TaintFlow { .. } => 45,

        // Low: deadlock, div-by-zero
        SecurityViolationKind::Deadlock { .. }
        | SecurityViolationKind::DivisionByZero => 30,

        // Low: unreachable
        SecurityViolationKind::UnreachableReached => 20,

        // Info: dead code
        SecurityViolationKind::DeadCode { .. } => 10,
    }
}

/// Short label for a violation kind (for rationale strings).
fn kind_label(kind: &SecurityViolationKind) -> &'static str {
    match kind {
        SecurityViolationKind::TaintedIndirectCall { .. } => "tainted-indirect-call",
        SecurityViolationKind::CommandInjection { .. } => "command-injection",
        SecurityViolationKind::TaintedSyscall { .. } => "tainted-syscall",
        SecurityViolationKind::ArbitraryWrite { .. } => "arbitrary-write",
        SecurityViolationKind::SqlInjection { .. } => "sql-injection",
        SecurityViolationKind::FormatStringInjection { .. } => "format-string-injection",
        SecurityViolationKind::BufferOverflow { .. } => "buffer-overflow",
        SecurityViolationKind::UseAfterFree { .. } => "use-after-free",
        SecurityViolationKind::IntegerOverflowToBufferCorruption { .. } => "int-overflow-to-buffer",
        SecurityViolationKind::DoubleFree { .. } => "double-free",
        SecurityViolationKind::PrivilegeEscalation { .. } => "privilege-escalation",
        SecurityViolationKind::Toctou { .. } => "toctou",
        SecurityViolationKind::DataRace { .. } => "data-race",
        SecurityViolationKind::IndexOutOfBounds { .. } => "index-oob",
        SecurityViolationKind::ArithmeticOverflow { .. } => "arithmetic-overflow",
        SecurityViolationKind::TaintFlow { .. } => "taint-flow",
        SecurityViolationKind::Deadlock { .. } => "deadlock",
        SecurityViolationKind::DivisionByZero => "division-by-zero",
        SecurityViolationKind::UnreachableReached => "unreachable",
        SecurityViolationKind::DeadCode { .. } => "dead-code",
    }
}

/// A violation with its computed severity and exploitability scores.
#[derive(Debug, Clone)]
pub(crate) struct PrioritizedViolation {
    /// Index into the original violations list.
    pub original_index: usize,
    /// Violation ID.
    pub violation_id: String,
    /// Numerical severity score (0-100).
    pub severity: SeverityScore,
    /// Exploitability assessment.
    pub exploitability: ExploitabilityAssessment,
    /// Final priority score (0-100), combining severity and exploitability.
    pub priority_score: u8,
    /// 1-based rank (1 = highest priority).
    pub rank: usize,
}

/// Configuration for the prioritizer.
#[derive(Debug, Clone)]
pub(crate) struct PrioritizerConfig {
    /// Weight for severity in the final priority (0.0-1.0, default 0.6).
    pub severity_weight: f64,
    /// Weight for exploitability in the final priority (0.0-1.0, default 0.4).
    pub exploitability_weight: f64,
}

impl Default for PrioritizerConfig {
    fn default() -> Self {
        Self {
            severity_weight: 0.6,
            exploitability_weight: 0.4,
        }
    }
}

/// Prioritizer combines severity scoring with exploitability assessment
/// to produce a final priority ordering of violations.
pub(crate) struct Prioritizer {
    config: PrioritizerConfig,
}

impl Prioritizer {
    #[must_use]
    pub(crate) fn new(config: PrioritizerConfig) -> Self {
        Self { config }
    }

    /// Prioritize all violations, returning them sorted highest-priority first.
    #[must_use]
    pub(crate) fn prioritize(
        &self,
        violations: &[SecurityViolation],
        chains: &[ExploitChain],
    ) -> Vec<PrioritizedViolation> {
        let mut results: Vec<PrioritizedViolation> = violations
            .iter()
            .enumerate()
            .map(|(i, v)| {
                let severity = score_violation(v, chains);
                let exploitability = assess_exploitability(v, chains);

                let priority_score = self.compute_priority(severity.score, exploitability.score);

                PrioritizedViolation {
                    original_index: i,
                    violation_id: v.id.clone(),
                    severity,
                    exploitability,
                    priority_score,
                    rank: 0, // filled after sorting
                }
            })
            .collect();

        // Sort by priority_score descending, break ties by severity descending
        results.sort_by(|a, b| {
            b.priority_score
                .cmp(&a.priority_score)
                .then_with(|| b.severity.score.cmp(&a.severity.score))
        });

        // Assign 1-based ranks
        for (i, pv) in results.iter_mut().enumerate() {
            pv.rank = i + 1;
        }

        results
    }

    /// Compute a 0-100 priority score from severity and exploitability.
    fn compute_priority(&self, severity_score: u8, exploitability_score: u8) -> u8 {
        let weighted = self.config.severity_weight * f64::from(severity_score)
            + self.config.exploitability_weight * f64::from(exploitability_score);
        (weighted.round() as u8).min(100)
    }
}

/// Map the existing Severity enum to a SeverityCategory for interop.
impl From<Severity> for SeverityCategory {
    fn from(s: Severity) -> Self {
        match s {
            Severity::Critical => SeverityCategory::Critical,
            Severity::High => SeverityCategory::High,
            Severity::Medium => SeverityCategory::Medium,
            Severity::Low => SeverityCategory::Low,
            Severity::Info => SeverityCategory::Info,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_types::{Counterexample, CounterexampleValue, FlowStep};

    fn make_violation(id: &str, kind: SecurityViolationKind) -> SecurityViolation {
        SecurityViolation {
            id: id.to_string(),
            severity: Severity::Medium,
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

    // --- SeverityCategory::from_score tests ---

    #[test]
    fn test_category_from_score_critical() {
        assert_eq!(SeverityCategory::from_score(100), SeverityCategory::Critical);
        assert_eq!(SeverityCategory::from_score(95), SeverityCategory::Critical);
        assert_eq!(SeverityCategory::from_score(90), SeverityCategory::Critical);
    }

    #[test]
    fn test_category_from_score_high() {
        assert_eq!(SeverityCategory::from_score(89), SeverityCategory::High);
        assert_eq!(SeverityCategory::from_score(75), SeverityCategory::High);
        assert_eq!(SeverityCategory::from_score(70), SeverityCategory::High);
    }

    #[test]
    fn test_category_from_score_medium() {
        assert_eq!(SeverityCategory::from_score(69), SeverityCategory::Medium);
        assert_eq!(SeverityCategory::from_score(50), SeverityCategory::Medium);
        assert_eq!(SeverityCategory::from_score(40), SeverityCategory::Medium);
    }

    #[test]
    fn test_category_from_score_low() {
        assert_eq!(SeverityCategory::from_score(39), SeverityCategory::Low);
        assert_eq!(SeverityCategory::from_score(25), SeverityCategory::Low);
        assert_eq!(SeverityCategory::from_score(20), SeverityCategory::Low);
    }

    #[test]
    fn test_category_from_score_info() {
        assert_eq!(SeverityCategory::from_score(19), SeverityCategory::Info);
        assert_eq!(SeverityCategory::from_score(5), SeverityCategory::Info);
        assert_eq!(SeverityCategory::from_score(0), SeverityCategory::Info);
    }

    // --- score_violation tests ---

    #[test]
    fn test_score_rce_class_base_95() {
        let v = make_violation("V1", SecurityViolationKind::CommandInjection {
            command_func: "exec".to_string(),
            taint_source: "user".to_string(),
        });
        let score = score_violation(&v, &[]);
        assert_eq!(score.score, 95);
        assert_eq!(score.category, SeverityCategory::Critical);
    }

    #[test]
    fn test_score_sql_injection_base_90() {
        let v = make_violation("V1", SecurityViolationKind::SqlInjection {
            sink_func: "query".to_string(),
            taint_source: "user".to_string(),
        });
        let score = score_violation(&v, &[]);
        assert_eq!(score.score, 90);
        assert_eq!(score.category, SeverityCategory::Critical);
    }

    #[test]
    fn test_score_dead_code_info() {
        let v = make_violation("V1", SecurityViolationKind::DeadCode {
            function: "unused".to_string(),
        });
        let score = score_violation(&v, &[]);
        assert_eq!(score.score, 10);
        assert_eq!(score.category, SeverityCategory::Info);
    }

    #[test]
    fn test_score_counterexample_adds_5() {
        let mut v = make_violation("V1", SecurityViolationKind::ArithmeticOverflow {
            operation: "Add".to_string(),
        });
        let base = score_violation(&v, &[]).score;

        v.counterexample = Some(Counterexample { trace: None,
            assignments: vec![("x".to_string(), CounterexampleValue::Uint(42))],
        });
        let boosted = score_violation(&v, &[]).score;
        assert_eq!(boosted, base + 5);
    }

    #[test]
    fn test_score_flow_path_adds_5() {
        let mut v = make_violation("V1", SecurityViolationKind::TaintFlow {
            source: "user".to_string(),
            sink: "db".to_string(),
        });
        let base = score_violation(&v, &[]).score;

        v.flow_path = vec![FlowStep {
            local: 1,
            block: 0,
            description: "step1".to_string(),
        }];
        let boosted = score_violation(&v, &[]).score;
        assert_eq!(boosted, base + 5);
    }

    #[test]
    fn test_score_long_flow_path_adds_10() {
        let mut v = make_violation("V1", SecurityViolationKind::TaintFlow {
            source: "user".to_string(),
            sink: "db".to_string(),
        });
        let base = score_violation(&v, &[]).score;

        v.flow_path = vec![
            FlowStep { local: 1, block: 0, description: "a".to_string() },
            FlowStep { local: 2, block: 1, description: "b".to_string() },
            FlowStep { local: 3, block: 2, description: "c".to_string() },
        ];
        let boosted = score_violation(&v, &[]).score;
        assert_eq!(boosted, base + 10); // +5 for flow, +5 for long flow
    }

    #[test]
    fn test_score_chain_membership_adds_5() {
        let v = make_violation("V1", SecurityViolationKind::ArithmeticOverflow {
            operation: "Add".to_string(),
        });
        let base = score_violation(&v, &[]).score;

        let chain = ExploitChain {
            name: "chain".to_string(),
            severity: Severity::Critical,
            violation_ids: vec!["V1".to_string()],
            description: "test".to_string(),
        };
        let boosted = score_violation(&v, &[chain]).score;
        assert_eq!(boosted, base + 5);
    }

    #[test]
    fn test_score_capped_at_100() {
        let mut v = make_violation("V1", SecurityViolationKind::CommandInjection {
            command_func: "exec".to_string(),
            taint_source: "user".to_string(),
        });
        // Base = 95, add counterexample (+5) + flow (+5) + long flow (+5) + chain (+5) = 115 -> capped 100
        v.counterexample = Some(Counterexample { trace: None,
            assignments: vec![("x".to_string(), CounterexampleValue::Uint(1))],
        });
        v.flow_path = vec![
            FlowStep { local: 1, block: 0, description: "a".to_string() },
            FlowStep { local: 2, block: 1, description: "b".to_string() },
            FlowStep { local: 3, block: 2, description: "c".to_string() },
        ];
        let chain = ExploitChain {
            name: "chain".to_string(),
            severity: Severity::Critical,
            violation_ids: vec!["V1".to_string()],
            description: "test".to_string(),
        };
        let score = score_violation(&v, &[chain]);
        assert_eq!(score.score, 100);
    }

    #[test]
    fn test_score_rationale_contains_base() {
        let v = make_violation("V1", SecurityViolationKind::DivisionByZero);
        let score = score_violation(&v, &[]);
        assert!(score.rationale.contains("base=30"), "rationale: {}", score.rationale);
        assert!(score.rationale.contains("division-by-zero"), "rationale: {}", score.rationale);
    }

    // --- Prioritizer tests ---

    #[test]
    fn test_prioritizer_orders_by_priority_score() {
        let violations = vec![
            make_violation("V1", SecurityViolationKind::DeadCode {
                function: "unused".to_string(),
            }),
            make_violation("V2", SecurityViolationKind::CommandInjection {
                command_func: "exec".to_string(),
                taint_source: "user".to_string(),
            }),
        ];

        let p = Prioritizer::new(PrioritizerConfig::default());
        let result = p.prioritize(&violations, &[]);
        assert_eq!(result.len(), 2);
        assert_eq!(result[0].violation_id, "V2"); // Command injection first
        assert_eq!(result[0].rank, 1);
        assert_eq!(result[1].violation_id, "V1"); // Dead code last
        assert_eq!(result[1].rank, 2);
        assert!(result[0].priority_score > result[1].priority_score);
    }

    #[test]
    fn test_prioritizer_empty_violations() {
        let p = Prioritizer::new(PrioritizerConfig::default());
        let result = p.prioritize(&[], &[]);
        assert!(result.is_empty());
    }

    #[test]
    fn test_prioritizer_custom_weights() {
        let config = PrioritizerConfig {
            severity_weight: 1.0,
            exploitability_weight: 0.0,
        };
        let violations = vec![
            make_violation("V1", SecurityViolationKind::ArithmeticOverflow {
                operation: "Add".to_string(),
            }),
        ];

        let p = Prioritizer::new(config);
        let result = p.prioritize(&violations, &[]);
        assert_eq!(result.len(), 1);
        // With exploitability_weight=0, priority = severity only
        assert_eq!(result[0].priority_score, result[0].severity.score);
    }

    #[test]
    fn test_prioritizer_ranks_are_sequential() {
        let violations = vec![
            make_violation("V1", SecurityViolationKind::DivisionByZero),
            make_violation("V2", SecurityViolationKind::BufferOverflow {
                write_size: "n".to_string(),
                buffer_size: "m".to_string(),
            }),
            make_violation("V3", SecurityViolationKind::ArithmeticOverflow {
                operation: "Add".to_string(),
            }),
        ];

        let p = Prioritizer::new(PrioritizerConfig::default());
        let result = p.prioritize(&violations, &[]);
        let ranks: Vec<usize> = result.iter().map(|r| r.rank).collect();
        assert_eq!(ranks, vec![1, 2, 3]);
    }

    // --- Severity conversion tests ---

    #[test]
    fn test_severity_to_category_conversion() {
        assert_eq!(SeverityCategory::from(Severity::Critical), SeverityCategory::Critical);
        assert_eq!(SeverityCategory::from(Severity::High), SeverityCategory::High);
        assert_eq!(SeverityCategory::from(Severity::Medium), SeverityCategory::Medium);
        assert_eq!(SeverityCategory::from(Severity::Low), SeverityCategory::Low);
        assert_eq!(SeverityCategory::from(Severity::Info), SeverityCategory::Info);
    }

    // --- Base score ordering tests ---

    #[test]
    fn test_base_scores_monotonic() {
        assert!(base_score(&SecurityViolationKind::CommandInjection {
            command_func: "x".into(),
            taint_source: "y".into(),
        }) > base_score(&SecurityViolationKind::SqlInjection {
            sink_func: "x".into(),
            taint_source: "y".into(),
        }));

        assert!(base_score(&SecurityViolationKind::SqlInjection {
            sink_func: "x".into(),
            taint_source: "y".into(),
        }) > base_score(&SecurityViolationKind::DoubleFree {
            first_free: "a".into(),
            second_free: "b".into(),
        }));

        assert!(base_score(&SecurityViolationKind::DoubleFree {
            first_free: "a".into(),
            second_free: "b".into(),
        }) > base_score(&SecurityViolationKind::IndexOutOfBounds {
            index_expr: "i".into(),
        }));

        assert!(base_score(&SecurityViolationKind::IndexOutOfBounds {
            index_expr: "i".into(),
        }) > base_score(&SecurityViolationKind::ArithmeticOverflow {
            operation: "Add".into(),
        }));

        assert!(base_score(&SecurityViolationKind::ArithmeticOverflow {
            operation: "Add".into(),
        }) > base_score(&SecurityViolationKind::DivisionByZero));

        assert!(base_score(&SecurityViolationKind::DivisionByZero)
            > base_score(&SecurityViolationKind::DeadCode {
                function: "x".into(),
            }));
    }
}
