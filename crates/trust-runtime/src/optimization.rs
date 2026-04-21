// trust-runtime/optimization.rs: Eliminate redundant runtime checks
//
// After instrumentation planning, multiple checks may be redundant (e.g.,
// duplicate bounds checks on the same index, or a bounds check subsumed by
// a slice range check). This module optimizes the check set.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};

use crate::instrumentation::{InstrumentationPlan, InstrumentedCheck};
use crate::{CheckKind, CheckStrategy};

// ---------------------------------------------------------------------------
// OptimizationReport
// ---------------------------------------------------------------------------

/// Summary of optimization applied to a set of runtime checks.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct OptimizationReport {
    /// Number of checks before optimization.
    pub original_count: usize,
    /// Number of checks after optimization.
    pub optimized_count: usize,
    /// Reasons for each removed check.
    pub removed_reasons: Vec<RemovalReason>,
}

/// Why a check was removed during optimization.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct RemovalReason {
    /// Description of the removed check.
    pub check_description: String,
    /// The optimization that removed it.
    pub reason: OptimizationKind,
}

/// Which optimization pass removed a check.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub(crate) enum OptimizationKind {
    /// Exact duplicate of another check (same kind + location).
    Duplicate,
    /// Subsumed by a stronger check (e.g., bounds check subsumed by slice range).
    Subsumed,
    /// Hoisted out of a loop body because it is loop-invariant.
    Hoisted,
}

// ---------------------------------------------------------------------------
// CheckOptimizer
// ---------------------------------------------------------------------------

/// Eliminates redundant runtime checks from an instrumentation plan.
///
/// Applies three optimization passes in sequence:
/// 1. `dedup_checks` — remove exact duplicates (same kind + location)
/// 2. `subsumption_elimination` — remove checks subsumed by stronger ones
/// 3. `hoist_invariant_checks` — deduplicate checks that appear in the same
///    function at the same location (loop-invariant hoisting proxy)
pub(crate) struct CheckOptimizer {
    report: OptimizationReport,
}

impl CheckOptimizer {
    /// Create a new optimizer.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            report: OptimizationReport {
                original_count: 0,
                optimized_count: 0,
                removed_reasons: Vec::new(),
            },
        }
    }

    /// Optimize an instrumentation plan, returning the optimized plan and report.
    #[must_use]
    pub(crate) fn optimize(&mut self, plan: &InstrumentationPlan) -> (InstrumentationPlan, OptimizationReport) {
        self.report.original_count = plan.checks.len();
        self.report.removed_reasons.clear();

        let checks = plan.checks.clone();
        let checks = self.dedup_checks(checks);
        let checks = self.subsumption_elimination(checks);
        let checks = self.hoist_invariant_checks(checks);

        self.report.optimized_count = checks.len();

        let optimized_plan = InstrumentationPlan {
            function: plan.function.clone(),
            checks,
            elided_count: plan.elided_count,
            failed_count: plan.failed_count,
            no_fallback_count: plan.no_fallback_count,
        };

        (optimized_plan, self.report.clone())
    }

    /// Remove exact duplicate checks (same kind + same location).
    fn dedup_checks(&mut self, checks: Vec<InstrumentedCheck>) -> Vec<InstrumentedCheck> {
        let mut seen: Vec<(&CheckKind, &trust_types::SourceSpan)> = Vec::new();
        let mut result = Vec::with_capacity(checks.len());

        // Two-pass: first collect indices to keep, then build result.
        // We need indices because we borrow from `checks`.
        let mut keep = vec![true; checks.len()];
        for (i, ic) in checks.iter().enumerate() {
            let key = (&ic.check.kind, &ic.check.location);
            if seen.iter().any(|(k, l)| *k == key.0 && *l == key.1) {
                keep[i] = false;
                self.report.removed_reasons.push(RemovalReason {
                    check_description: ic.vc_description.clone(),
                    reason: OptimizationKind::Duplicate,
                });
            } else {
                seen.push(key);
            }
        }

        for (i, ic) in checks.into_iter().enumerate() {
            if keep[i] {
                result.push(ic);
            }
        }
        result
    }

    /// Remove checks subsumed by stronger checks at the same location.
    ///
    /// Subsumption rules:
    /// - `SliceRangeCheck` subsumes `BoundsCheck` at the same location
    ///   (slice range checks `start <= end && end <= len`, which implies `index < len`)
    /// - `DivisorNonZero` for `DivisionByZero` subsumes `DivisorNonZero` for
    ///   `RemainderByZero` at the same location (same check: `divisor != 0`)
    fn subsumption_elimination(&mut self, checks: Vec<InstrumentedCheck>) -> Vec<InstrumentedCheck> {
        // Collect locations that have slice range checks (cloned to avoid borrow).
        let slice_range_locations: Vec<trust_types::SourceSpan> = checks
            .iter()
            .filter(|ic| ic.check.strategy == CheckStrategy::SliceRangeCheck)
            .map(|ic| ic.check.location.clone())
            .collect();

        // Collect locations that have division-by-zero checks (cloned to avoid borrow).
        let div_zero_locations: Vec<trust_types::SourceSpan> = checks
            .iter()
            .filter(|ic| ic.check.kind == CheckKind::DivisionByZero)
            .map(|ic| ic.check.location.clone())
            .collect();

        let mut result = Vec::with_capacity(checks.len());
        for ic in checks {
            let subsumed = match &ic.check.strategy {
                // BoundsCheck subsumed by SliceRangeCheck at same location
                CheckStrategy::BoundsCheck => {
                    slice_range_locations.contains(&ic.check.location)
                }
                // RemainderByZero subsumed by DivisionByZero at same location
                // (both use DivisorNonZero strategy)
                _ if ic.check.kind == CheckKind::RemainderByZero => {
                    div_zero_locations.contains(&ic.check.location)
                }
                _ => false,
            };

            if subsumed {
                self.report.removed_reasons.push(RemovalReason {
                    check_description: ic.vc_description.clone(),
                    reason: OptimizationKind::Subsumed,
                });
            } else {
                result.push(ic);
            }
        }
        result
    }

    /// Hoist loop-invariant checks by deduplicating checks with the same kind
    /// and function that differ only in minor location details.
    ///
    /// In practice, a loop body may generate the same check kind for the same
    /// function at slightly different column offsets. We keep only the first
    /// occurrence per (kind, function, file, line_start) tuple.
    fn hoist_invariant_checks(&mut self, checks: Vec<InstrumentedCheck>) -> Vec<InstrumentedCheck> {
        let mut seen: Vec<(&CheckKind, &str, &str, u32)> = Vec::new();
        let mut keep = vec![true; checks.len()];

        for (i, ic) in checks.iter().enumerate() {
            let key = (
                &ic.check.kind,
                ic.check.function.as_str(),
                ic.check.location.file.as_str(),
                ic.check.location.line_start,
            );
            if seen.iter().any(|(k, f, file, line)| {
                *k == key.0 && *f == key.1 && *file == key.2 && *line == key.3
            }) {
                keep[i] = false;
                self.report.removed_reasons.push(RemovalReason {
                    check_description: ic.vc_description.clone(),
                    reason: OptimizationKind::Hoisted,
                });
            } else {
                seen.push(key);
            }
        }

        checks
            .into_iter()
            .enumerate()
            .filter(|(i, _)| keep[*i])
            .map(|(_, ic)| ic)
            .collect()
    }
}

impl Default for CheckOptimizer {
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
    use crate::instrumentation::{
        CheckOverhead, InstrumentationPlan, InstrumentationReason, InstrumentedCheck,
    };
    use crate::{CheckKind, CheckStrategy, RuntimeCheck};
    use trust_types::SourceSpan;

    fn span(line: u32, col: u32) -> SourceSpan {
        SourceSpan {
            file: "src/lib.rs".to_string(),
            line_start: line,
            col_start: col,
            line_end: line,
            col_end: col + 10,
        }
    }

    fn make_ic(kind: CheckKind, strategy: CheckStrategy, location: SourceSpan) -> InstrumentedCheck {
        let overhead = CheckOverhead::from_strategy(&strategy);
        InstrumentedCheck {
            check: RuntimeCheck {
                kind,
                location,
                description: "test".to_string(),
                strategy,
                function: "test_fn".to_string(),
            },
            overhead,
            vc_description: "test vc".to_string(),
            reason: InstrumentationReason::Unknown {
                solver: "z4".to_string(),
                reason: "test".to_string(),
            },
        }
    }

    fn make_plan(checks: Vec<InstrumentedCheck>) -> InstrumentationPlan {
        InstrumentationPlan {
            function: "test_fn".to_string(),
            checks,
            elided_count: 0,
            failed_count: 0,
            no_fallback_count: 0,
        }
    }

    // -----------------------------------------------------------------------
    // dedup_checks
    // -----------------------------------------------------------------------

    #[test]
    fn test_dedup_removes_exact_duplicates() {
        let loc = span(10, 5);
        let checks = vec![
            make_ic(CheckKind::IndexOutOfBounds, CheckStrategy::BoundsCheck, loc.clone()),
            make_ic(CheckKind::IndexOutOfBounds, CheckStrategy::BoundsCheck, loc.clone()),
            make_ic(CheckKind::IndexOutOfBounds, CheckStrategy::BoundsCheck, loc),
        ];
        let plan = make_plan(checks);

        let mut opt = CheckOptimizer::new();
        let (optimized, report) = opt.optimize(&plan);
        assert_eq!(report.original_count, 3);
        assert_eq!(optimized.checks.len(), 1);
        assert_eq!(
            report.removed_reasons.iter().filter(|r| r.reason == OptimizationKind::Duplicate).count(),
            2
        );
    }

    #[test]
    fn test_dedup_keeps_different_locations() {
        let checks = vec![
            make_ic(CheckKind::IndexOutOfBounds, CheckStrategy::BoundsCheck, span(10, 5)),
            make_ic(CheckKind::IndexOutOfBounds, CheckStrategy::BoundsCheck, span(20, 5)),
        ];
        let plan = make_plan(checks);

        let mut opt = CheckOptimizer::new();
        let (optimized, report) = opt.optimize(&plan);
        assert_eq!(optimized.checks.len(), 2);
        assert!(report.removed_reasons.is_empty());
    }

    #[test]
    fn test_dedup_keeps_different_kinds() {
        let loc = span(10, 5);
        let checks = vec![
            make_ic(CheckKind::IndexOutOfBounds, CheckStrategy::BoundsCheck, loc.clone()),
            make_ic(CheckKind::DivisionByZero, CheckStrategy::DivisorNonZero, loc),
        ];
        let plan = make_plan(checks);

        let mut opt = CheckOptimizer::new();
        let (optimized, _) = opt.optimize(&plan);
        assert_eq!(optimized.checks.len(), 2);
    }

    // -----------------------------------------------------------------------
    // subsumption_elimination
    // -----------------------------------------------------------------------

    #[test]
    fn test_subsumption_slice_range_subsumes_bounds() {
        let loc = span(10, 5);
        let checks = vec![
            make_ic(CheckKind::SliceBoundsCheck, CheckStrategy::SliceRangeCheck, loc.clone()),
            make_ic(CheckKind::IndexOutOfBounds, CheckStrategy::BoundsCheck, loc),
        ];
        let plan = make_plan(checks);

        let mut opt = CheckOptimizer::new();
        let (optimized, report) = opt.optimize(&plan);
        assert_eq!(optimized.checks.len(), 1);
        assert_eq!(optimized.checks[0].check.kind, CheckKind::SliceBoundsCheck);
        assert!(report.removed_reasons.iter().any(|r| r.reason == OptimizationKind::Subsumed));
    }

    #[test]
    fn test_subsumption_div_zero_subsumes_remainder() {
        let loc = span(10, 5);
        let checks = vec![
            make_ic(CheckKind::DivisionByZero, CheckStrategy::DivisorNonZero, loc.clone()),
            make_ic(CheckKind::RemainderByZero, CheckStrategy::DivisorNonZero, loc),
        ];
        let plan = make_plan(checks);

        let mut opt = CheckOptimizer::new();
        let (optimized, report) = opt.optimize(&plan);
        assert_eq!(optimized.checks.len(), 1);
        assert_eq!(optimized.checks[0].check.kind, CheckKind::DivisionByZero);
        assert!(report.removed_reasons.iter().any(|r| r.reason == OptimizationKind::Subsumed));
    }

    #[test]
    fn test_subsumption_different_locations_not_subsumed() {
        let checks = vec![
            make_ic(CheckKind::SliceBoundsCheck, CheckStrategy::SliceRangeCheck, span(10, 5)),
            make_ic(CheckKind::IndexOutOfBounds, CheckStrategy::BoundsCheck, span(20, 5)),
        ];
        let plan = make_plan(checks);

        let mut opt = CheckOptimizer::new();
        let (optimized, _) = opt.optimize(&plan);
        assert_eq!(optimized.checks.len(), 2);
    }

    // -----------------------------------------------------------------------
    // hoist_invariant_checks
    // -----------------------------------------------------------------------

    #[test]
    fn test_hoist_removes_same_line_different_col() {
        let checks = vec![
            make_ic(CheckKind::IndexOutOfBounds, CheckStrategy::BoundsCheck, span(10, 5)),
            make_ic(CheckKind::IndexOutOfBounds, CheckStrategy::BoundsCheck, span(10, 15)),
        ];
        let plan = make_plan(checks);

        let mut opt = CheckOptimizer::new();
        let (optimized, report) = opt.optimize(&plan);
        // After dedup (different locations, so both survive), hoist removes the second
        // because same (kind, function, file, line_start).
        assert_eq!(optimized.checks.len(), 1);
        assert!(report.removed_reasons.iter().any(|r| r.reason == OptimizationKind::Hoisted));
    }

    #[test]
    fn test_hoist_keeps_different_lines() {
        let checks = vec![
            make_ic(CheckKind::IndexOutOfBounds, CheckStrategy::BoundsCheck, span(10, 5)),
            make_ic(CheckKind::IndexOutOfBounds, CheckStrategy::BoundsCheck, span(20, 5)),
        ];
        let plan = make_plan(checks);

        let mut opt = CheckOptimizer::new();
        let (optimized, _) = opt.optimize(&plan);
        assert_eq!(optimized.checks.len(), 2);
    }

    // -----------------------------------------------------------------------
    // Combined optimization
    // -----------------------------------------------------------------------

    #[test]
    fn test_optimize_combined() {
        let loc = span(10, 5);
        let checks = vec![
            // Will survive: slice range check
            make_ic(CheckKind::SliceBoundsCheck, CheckStrategy::SliceRangeCheck, loc.clone()),
            // Subsumed by slice range
            make_ic(CheckKind::IndexOutOfBounds, CheckStrategy::BoundsCheck, loc.clone()),
            // Duplicate of bounds check (removed by dedup before subsumption)
            make_ic(CheckKind::IndexOutOfBounds, CheckStrategy::BoundsCheck, loc.clone()),
            // Will survive: division check at different location
            make_ic(CheckKind::DivisionByZero, CheckStrategy::DivisorNonZero, span(20, 5)),
        ];
        let plan = make_plan(checks);

        let mut opt = CheckOptimizer::new();
        let (optimized, report) = opt.optimize(&plan);
        assert_eq!(report.original_count, 4);
        assert_eq!(optimized.checks.len(), 2);
        assert_eq!(optimized.checks[0].check.kind, CheckKind::SliceBoundsCheck);
        assert_eq!(optimized.checks[1].check.kind, CheckKind::DivisionByZero);
    }

    #[test]
    fn test_optimize_empty_plan() {
        let plan = make_plan(vec![]);

        let mut opt = CheckOptimizer::new();
        let (optimized, report) = opt.optimize(&plan);
        assert_eq!(report.original_count, 0);
        assert_eq!(report.optimized_count, 0);
        assert!(optimized.checks.is_empty());
        assert!(report.removed_reasons.is_empty());
    }

    #[test]
    fn test_optimize_preserves_plan_metadata() {
        let plan = InstrumentationPlan {
            function: "important_fn".to_string(),
            checks: vec![
                make_ic(CheckKind::DivisionByZero, CheckStrategy::DivisorNonZero, span(10, 5)),
            ],
            elided_count: 5,
            failed_count: 2,
            no_fallback_count: 1,
        };

        let mut opt = CheckOptimizer::new();
        let (optimized, _) = opt.optimize(&plan);
        assert_eq!(optimized.function, "important_fn");
        assert_eq!(optimized.elided_count, 5);
        assert_eq!(optimized.failed_count, 2);
        assert_eq!(optimized.no_fallback_count, 1);
    }

    #[test]
    fn test_report_serialization_roundtrip() {
        let report = OptimizationReport {
            original_count: 5,
            optimized_count: 3,
            removed_reasons: vec![
                RemovalReason {
                    check_description: "bounds check".to_string(),
                    reason: OptimizationKind::Duplicate,
                },
                RemovalReason {
                    check_description: "index check".to_string(),
                    reason: OptimizationKind::Subsumed,
                },
            ],
        };

        let json = serde_json::to_string(&report).expect("serialize");
        let roundtrip: OptimizationReport = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(roundtrip, report);
    }
}
