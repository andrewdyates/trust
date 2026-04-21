// trust-debug/triage.rs: Violation triage and fix-order recommendation
//
// Groups violations by affected function, identifies root-cause chains
// (violation A enables violation B), and recommends which violations to
// fix first for maximum impact in the verification loop.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;

use crate::scoring::{ScoredViolation, ScoringConfig, SuggestedPriority};
use crate::{DebugReport, ExploitChain, SecurityViolation, SecurityViolationKind, Severity};

/// Result of triaging a debug report.
#[derive(Debug, Clone)]
pub(crate) struct TriageReport {
    /// Violations grouped by affected function.
    pub function_groups: Vec<FunctionGroup>,
    /// Root-cause chains: fixing the root cause eliminates downstream violations.
    pub root_cause_chains: Vec<RootCauseChain>,
    /// Prioritized action items in recommended fix order.
    pub action_items: Vec<ActionItem>,
    /// Summary statistics.
    pub summary: TriageSummary,
}

/// A group of violations in the same function.
#[derive(Debug, Clone)]
pub(crate) struct FunctionGroup {
    /// Function path (e.g., "crate::module::func").
    pub function: String,
    /// Violation IDs in this function.
    pub violation_ids: Vec<String>,
    /// Highest severity among violations in this group.
    pub max_severity: Severity,
    /// Number of violations in this function.
    pub count: usize,
}

/// A root-cause chain: one violation enables others downstream.
#[derive(Debug, Clone)]
pub(crate) struct RootCauseChain {
    /// The root-cause violation ID.
    pub root_id: String,
    /// Violation IDs that depend on (are enabled by) the root cause.
    pub dependent_ids: Vec<String>,
    /// Description of the causal relationship.
    pub description: String,
    /// If the root is fixed, how many violations are eliminated.
    pub eliminated_count: usize,
}

/// A prioritized action item for the verification loop.
#[derive(Debug, Clone)]
pub(crate) struct ActionItem {
    /// 1-based rank (1 = fix first).
    pub rank: usize,
    /// Violation ID to address.
    pub violation_id: String,
    /// Function containing the violation.
    pub function: String,
    /// Why this should be fixed at this priority.
    pub rationale: String,
    /// Estimated number of violations eliminated by fixing this one.
    pub estimated_impact: usize,
    /// Suggested priority level.
    pub priority: SuggestedPriority,
}

/// Summary statistics from triage.
#[derive(Debug, Clone)]
pub(crate) struct TriageSummary {
    /// Total violations triaged.
    pub total_violations: usize,
    /// Number of distinct functions affected.
    pub affected_functions: usize,
    /// Number of root-cause chains found.
    pub root_cause_chains: usize,
    /// Number of action items generated.
    pub action_items: usize,
    /// Estimated violations eliminated by fixing all action items.
    pub estimated_total_impact: usize,
}

/// Triage a debug report into prioritized action items.
///
/// This is the main entry point. It:
/// 1. Groups violations by function to identify hot spots
/// 2. Identifies root-cause chains from exploitation chains
/// 3. Scores violations and builds a fix-first ordering
/// 4. Returns a `TriageReport` with actionable recommendations
#[must_use]
pub(crate) fn triage(report: &DebugReport, config: &ScoringConfig) -> TriageReport {
    let function_groups = group_by_function(&report.violations);
    let root_cause_chains = identify_root_causes(&report.violations, &report.chains);
    let scored = crate::scoring::score_violations(report, config);
    let action_items = build_action_items(&scored, &root_cause_chains, &report.violations);

    let estimated_total_impact: usize = action_items.iter().map(|a| a.estimated_impact).sum();

    let summary = TriageSummary {
        total_violations: report.violations.len(),
        affected_functions: function_groups.len(),
        root_cause_chains: root_cause_chains.len(),
        action_items: action_items.len(),
        estimated_total_impact,
    };

    TriageReport {
        function_groups,
        root_cause_chains,
        action_items,
        summary,
    }
}

/// Group violations by their containing function.
fn group_by_function(violations: &[SecurityViolation]) -> Vec<FunctionGroup> {
    let mut map: FxHashMap<&str, Vec<&SecurityViolation>> = FxHashMap::default();
    for v in violations {
        map.entry(v.function.as_str()).or_default().push(v);
    }

    let mut groups: Vec<FunctionGroup> = map
        .into_iter()
        .map(|(func, vs)| {
            let max_severity = vs
                .iter()
                .map(|v| v.severity)
                .min() // Severity::Critical < Severity::Info in Ord
                .unwrap_or(Severity::Info);
            let count = vs.len();
            let violation_ids = vs.iter().map(|v| v.id.clone()).collect();
            FunctionGroup {
                function: func.to_string(),
                violation_ids,
                max_severity,
                count,
            }
        })
        .collect();

    // Sort: most severe first, then by count descending
    groups.sort_by(|a, b| {
        a.max_severity
            .cmp(&b.max_severity)
            .then_with(|| b.count.cmp(&a.count))
    });

    groups
}

/// Identify root-cause chains from exploitation chains and violation kinds.
///
/// A root cause is a violation that enables other violations:
/// - Arithmetic overflow that controls a buffer size (enables buffer overflow)
/// - Taint flow that reaches an injection point
/// - Use-after-free that enables arbitrary write
fn identify_root_causes(
    violations: &[SecurityViolation],
    chains: &[ExploitChain],
) -> Vec<RootCauseChain> {
    let mut root_causes = Vec::new();

    // From exploitation chains: first violation in each chain is the root cause
    for chain in chains {
        if chain.violation_ids.len() < 2 {
            continue;
        }

        let root_id = &chain.violation_ids[0];
        let dependent_ids: Vec<String> = chain.violation_ids[1..].to_vec();
        let eliminated_count = dependent_ids.len();

        root_causes.push(RootCauseChain {
            root_id: root_id.clone(),
            dependent_ids,
            description: format!(
                "Fixing {} eliminates downstream violations in chain '{}'",
                root_id, chain.name,
            ),
            eliminated_count,
        });
    }

    // Heuristic: if a function has an overflow AND a buffer/index violation,
    // the overflow is likely the root cause
    let by_func = group_violations_by_func(violations);
    for func_violations in by_func.values() {
        let overflows: Vec<&SecurityViolation> = func_violations
            .iter()
            .filter(|v| matches!(&v.kind, SecurityViolationKind::ArithmeticOverflow { .. }))
            .copied()
            .collect();

        let memory_issues: Vec<&SecurityViolation> = func_violations
            .iter()
            .filter(|v| {
                matches!(
                    &v.kind,
                    SecurityViolationKind::BufferOverflow { .. }
                        | SecurityViolationKind::IndexOutOfBounds { .. }
                        | SecurityViolationKind::IntegerOverflowToBufferCorruption { .. }
                )
            })
            .copied()
            .collect();

        for overflow in &overflows {
            if !memory_issues.is_empty() {
                // Check this root cause is not already covered by a chain
                let already_covered = root_causes
                    .iter()
                    .any(|rc| rc.root_id == overflow.id);
                if already_covered {
                    continue;
                }

                let dependent_ids: Vec<String> =
                    memory_issues.iter().map(|v| v.id.clone()).collect();
                let eliminated_count = dependent_ids.len();

                root_causes.push(RootCauseChain {
                    root_id: overflow.id.clone(),
                    dependent_ids,
                    description: format!(
                        "Arithmetic overflow '{}' likely controls buffer size — \
                         fixing it may eliminate memory corruption violations",
                        overflow.id,
                    ),
                    eliminated_count,
                });
            }
        }
    }

    // Deduplicate: if same root_id appears multiple times, merge dependents
    let mut merged: FxHashMap<String, RootCauseChain> = FxHashMap::default();
    for rc in root_causes {
        merged
            .entry(rc.root_id.clone())
            .and_modify(|existing| {
                for dep in &rc.dependent_ids {
                    if !existing.dependent_ids.contains(dep) {
                        existing.dependent_ids.push(dep.clone());
                        existing.eliminated_count += 1;
                    }
                }
            })
            .or_insert(rc);
    }

    let mut result: Vec<RootCauseChain> = merged.into_values().collect();
    // Sort by impact (most eliminated first)
    result.sort_by(|a, b| b.eliminated_count.cmp(&a.eliminated_count));

    result
}

fn group_violations_by_func(
    violations: &[SecurityViolation],
) -> FxHashMap<&str, Vec<&SecurityViolation>> {
    let mut map: FxHashMap<&str, Vec<&SecurityViolation>> = FxHashMap::default();
    for v in violations {
        map.entry(v.function.as_str()).or_default().push(v);
    }
    map
}

/// Build ordered action items from scored violations and root-cause analysis.
fn build_action_items(
    scored: &[ScoredViolation],
    root_causes: &[RootCauseChain],
    violations: &[SecurityViolation],
) -> Vec<ActionItem> {
    let mut items = Vec::new();
    let mut addressed: Vec<String> = Vec::new();

    // Phase 1: Root causes first (fixing one eliminates many)
    // Sort root causes by their scored violation's composite score
    let mut root_cause_order: Vec<(usize, &RootCauseChain)> = root_causes
        .iter()
        .enumerate()
        .collect();
    root_cause_order.sort_by(|a, b| {
        let score_a = scored
            .iter()
            .find(|s| s.violation_id == a.1.root_id)
            .map(|s| s.composite_score)
            .unwrap_or(0.0);
        let score_b = scored
            .iter()
            .find(|s| s.violation_id == b.1.root_id)
            .map(|s| s.composite_score)
            .unwrap_or(0.0);
        score_b
            .partial_cmp(&score_a)
            .unwrap_or(std::cmp::Ordering::Equal)
    });

    for (_i, rc) in &root_cause_order {
        if addressed.contains(&rc.root_id) {
            continue;
        }

        let sv = scored.iter().find(|s| s.violation_id == rc.root_id);
        let (priority, func) = match sv {
            Some(s) => {
                let func = violations
                    .get(s.original_index)
                    .map(|v| v.function.clone())
                    .unwrap_or_default();
                (s.suggested_priority, func)
            }
            None => (SuggestedPriority::High, String::new()),
        };

        items.push(ActionItem {
            rank: 0, // filled below
            violation_id: rc.root_id.clone(),
            function: func,
            rationale: format!(
                "Root cause: fixing this eliminates {} downstream violation(s)",
                rc.eliminated_count,
            ),
            estimated_impact: 1 + rc.eliminated_count,
            priority,
        });

        addressed.push(rc.root_id.clone());
        for dep in &rc.dependent_ids {
            addressed.push(dep.clone());
        }
    }

    // Phase 2: Remaining violations by score
    for sv in scored {
        if addressed.contains(&sv.violation_id) {
            continue;
        }

        let func = violations
            .get(sv.original_index)
            .map(|v| v.function.clone())
            .unwrap_or_default();

        items.push(ActionItem {
            rank: 0,
            violation_id: sv.violation_id.clone(),
            function: func,
            rationale: format!(
                "Score {:.2}: severity={:.2}, exploitability={:.2}, blast_radius={:.2}",
                sv.composite_score,
                sv.severity_score,
                sv.exploitability_score,
                sv.blast_radius_score,
            ),
            estimated_impact: 1,
            priority: sv.suggested_priority,
        });

        addressed.push(sv.violation_id.clone());
    }

    // Assign ranks
    for (i, item) in items.iter_mut().enumerate() {
        item.rank = i + 1;
    }

    items
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::DebugSummary;

    fn make_violation(
        id: &str,
        func: &str,
        severity: Severity,
        kind: SecurityViolationKind,
    ) -> SecurityViolation {
        SecurityViolation {
            id: id.to_string(),
            severity,
            kind,
            function: func.to_string(),
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
    fn test_triage_empty_report() {
        let report = make_report(vec![], vec![]);
        let result = triage(&report, &ScoringConfig::default());
        assert!(result.function_groups.is_empty());
        assert!(result.root_cause_chains.is_empty());
        assert!(result.action_items.is_empty());
        assert_eq!(result.summary.total_violations, 0);
    }

    #[test]
    fn test_group_by_function() {
        let violations = vec![
            make_violation("V1", "mod::foo", Severity::High, SecurityViolationKind::BufferOverflow {
                write_size: "n".to_string(),
                buffer_size: "m".to_string(),
            }),
            make_violation("V2", "mod::foo", Severity::Medium, SecurityViolationKind::ArithmeticOverflow {
                operation: "Add".to_string(),
            }),
            make_violation("V3", "mod::bar", Severity::Critical, SecurityViolationKind::SqlInjection {
                sink_func: "query".to_string(),
                taint_source: "user".to_string(),
            }),
        ];

        let groups = group_by_function(&violations);
        assert_eq!(groups.len(), 2);
        // Critical (bar) should come first
        assert_eq!(groups[0].function, "mod::bar");
        assert_eq!(groups[0].count, 1);
        // foo has 2 violations
        assert_eq!(groups[1].function, "mod::foo");
        assert_eq!(groups[1].count, 2);
    }

    #[test]
    fn test_root_cause_from_chain() {
        let violations = vec![
            make_violation("V1", "func", Severity::Medium, SecurityViolationKind::ArithmeticOverflow {
                operation: "Add".to_string(),
            }),
            make_violation("V2", "func", Severity::High, SecurityViolationKind::BufferOverflow {
                write_size: "n".to_string(),
                buffer_size: "m".to_string(),
            }),
        ];
        let chains = vec![ExploitChain {
            name: "overflow-chain".to_string(),
            severity: Severity::Critical,
            violation_ids: vec!["V1".to_string(), "V2".to_string()],
            description: "test chain".to_string(),
        }];

        let rcs = identify_root_causes(&violations, &chains);
        assert_eq!(rcs.len(), 1);
        assert_eq!(rcs[0].root_id, "V1");
        assert_eq!(rcs[0].dependent_ids, vec!["V2".to_string()]);
        assert_eq!(rcs[0].eliminated_count, 1);
    }

    #[test]
    fn test_root_cause_heuristic_overflow_to_buffer() {
        let violations = vec![
            make_violation("V1", "func", Severity::Medium, SecurityViolationKind::ArithmeticOverflow {
                operation: "Add".to_string(),
            }),
            make_violation("V2", "func", Severity::High, SecurityViolationKind::IndexOutOfBounds {
                index_expr: "i".to_string(),
            }),
        ];

        let rcs = identify_root_causes(&violations, &[]);
        assert_eq!(rcs.len(), 1);
        assert_eq!(rcs[0].root_id, "V1");
        assert!(rcs[0].dependent_ids.contains(&"V2".to_string()));
    }

    #[test]
    fn test_action_items_root_causes_first() {
        let violations = vec![
            make_violation("V1", "func", Severity::Medium, SecurityViolationKind::ArithmeticOverflow {
                operation: "Add".to_string(),
            }),
            make_violation("V2", "func", Severity::High, SecurityViolationKind::BufferOverflow {
                write_size: "n".to_string(),
                buffer_size: "m".to_string(),
            }),
            make_violation("V3", "other", Severity::Low, SecurityViolationKind::DeadCode {
                function: "unused".to_string(),
            }),
        ];
        let chains = vec![ExploitChain {
            name: "overflow-chain".to_string(),
            severity: Severity::Critical,
            violation_ids: vec!["V1".to_string(), "V2".to_string()],
            description: "test chain".to_string(),
        }];

        let report = make_report(violations, chains);
        let result = triage(&report, &ScoringConfig::default());

        // Root cause V1 should be first action item
        assert!(!result.action_items.is_empty());
        assert_eq!(result.action_items[0].violation_id, "V1");
        assert!(result.action_items[0].estimated_impact > 1);
        assert!(result.action_items[0].rationale.contains("Root cause"));

        // V2 should be eliminated (not a separate action item)
        let v2_item = result
            .action_items
            .iter()
            .find(|a| a.violation_id == "V2");
        assert!(v2_item.is_none(), "V2 should be covered by root cause V1");

        // V3 should be a separate action item
        let v3_item = result
            .action_items
            .iter()
            .find(|a| a.violation_id == "V3");
        assert!(v3_item.is_some(), "V3 should be a standalone action item");
    }

    #[test]
    fn test_triage_summary_counts() {
        let violations = vec![
            make_violation("V1", "foo", Severity::High, SecurityViolationKind::BufferOverflow {
                write_size: "n".to_string(),
                buffer_size: "m".to_string(),
            }),
            make_violation("V2", "bar", Severity::Medium, SecurityViolationKind::ArithmeticOverflow {
                operation: "Mul".to_string(),
            }),
        ];

        let report = make_report(violations, vec![]);
        let result = triage(&report, &ScoringConfig::default());

        assert_eq!(result.summary.total_violations, 2);
        assert_eq!(result.summary.affected_functions, 2);
        assert_eq!(result.summary.root_cause_chains, 0);
        assert_eq!(result.summary.action_items, 2);
    }

    #[test]
    fn test_action_items_have_sequential_ranks() {
        let violations = vec![
            make_violation("V1", "a", Severity::High, SecurityViolationKind::BufferOverflow {
                write_size: "n".to_string(),
                buffer_size: "m".to_string(),
            }),
            make_violation("V2", "b", Severity::Medium, SecurityViolationKind::ArithmeticOverflow {
                operation: "Add".to_string(),
            }),
            make_violation("V3", "c", Severity::Low, SecurityViolationKind::DivisionByZero),
        ];

        let report = make_report(violations, vec![]);
        let result = triage(&report, &ScoringConfig::default());

        let ranks: Vec<usize> = result.action_items.iter().map(|a| a.rank).collect();
        assert_eq!(ranks, vec![1, 2, 3]);
    }

    #[test]
    fn test_multiple_functions_sorted_by_severity() {
        let violations = vec![
            make_violation("V1", "low_func", Severity::Low, SecurityViolationKind::DeadCode {
                function: "unused".to_string(),
            }),
            make_violation("V2", "crit_func", Severity::Critical, SecurityViolationKind::SqlInjection {
                sink_func: "query".to_string(),
                taint_source: "user".to_string(),
            }),
            make_violation("V3", "med_func", Severity::Medium, SecurityViolationKind::ArithmeticOverflow {
                operation: "Add".to_string(),
            }),
        ];

        let groups = group_by_function(&violations);
        // Critical function should be first
        assert_eq!(groups[0].function, "crit_func");
        assert_eq!(groups[0].max_severity, Severity::Critical);
    }
}
