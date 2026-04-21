// trust-runtime/instrumentation.rs: Verification-guided runtime instrumentation planning
//
// Bridges verification results to runtime checks: for each VC that cannot be
// statically proved, plan the minimal runtime check to insert.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};
use trust_types::{VerificationCondition, VerificationResult};

use crate::{CheckStrategy, RuntimeCheck};

// ---------------------------------------------------------------------------
// RuntimeCheck extension: overhead estimation
// ---------------------------------------------------------------------------

/// Overhead classification for a single runtime check.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub(crate) enum CheckOverhead {
    /// Zero-cost: the check is already emitted by rustc in debug mode
    /// (e.g., overflow checks). No additional instructions needed.
    ZeroCost,
    /// Lightweight: a single comparison + branch (e.g., `assert!(idx < len)`).
    /// Typically 1-3 ns overhead.
    Lightweight,
    /// Expensive: requires loading additional state or multi-step validation
    /// (e.g., slice range checks with two comparisons).
    Expensive,
}

impl CheckOverhead {
    /// Classify a check strategy by its estimated overhead.
    #[must_use]
    pub(crate) fn from_strategy(strategy: &CheckStrategy) -> Self {
        match strategy {
            // Overflow, shift, negation checks are already in rustc's debug codegen.
            CheckStrategy::OverflowCheck { .. }
            | CheckStrategy::ShiftCheck
            | CheckStrategy::NegationCheck => CheckOverhead::ZeroCost,
            // Single comparison + branch.
            CheckStrategy::BoundsCheck
            | CheckStrategy::DivisorNonZero
            | CheckStrategy::UnreachablePanic => CheckOverhead::Lightweight,
            // Preserved assertions keep the original (possibly complex) check.
            CheckStrategy::PreserveAssertion { .. } => CheckOverhead::Lightweight,
            // Slice range: two comparisons (start <= end, end <= len).
            CheckStrategy::SliceRangeCheck => CheckOverhead::Expensive,
        }
    }
}

// ---------------------------------------------------------------------------
// InstrumentationPlan
// ---------------------------------------------------------------------------

/// A collection of runtime checks to insert for a function, with summary stats.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct InstrumentationPlan {
    /// Name of the function being instrumented.
    pub function: String,
    /// Runtime checks to insert (one per unproved VC).
    pub checks: Vec<InstrumentedCheck>,
    /// Number of VCs that were proved and need no check.
    pub elided_count: usize,
    /// Number of VCs that failed (have counterexamples) -- not checkable at runtime.
    pub failed_count: usize,
    /// Number of VCs with no runtime fallback (e.g., postconditions).
    pub no_fallback_count: usize,
}

/// A runtime check paired with its overhead classification and originating VC metadata.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct InstrumentedCheck {
    /// The runtime check to insert.
    pub check: RuntimeCheck,
    /// Overhead classification.
    pub overhead: CheckOverhead,
    /// The original VC kind description for diagnostics.
    pub vc_description: String,
    /// Why this check is needed ("unknown", "timeout").
    pub reason: InstrumentationReason,
}

/// Why a runtime check was generated.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum InstrumentationReason {
    /// Solver returned Unknown.
    Unknown { solver: String, reason: String },
    /// Solver timed out.
    Timeout { solver: String, timeout_ms: u64 },
    /// Forced by ForceRuntime policy (even if proved).
    ForcedRuntime,
}

/// Summary of estimated overhead for the instrumentation plan.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct OverheadSummary {
    /// Total checks to insert.
    pub total_checks: usize,
    /// Checks that are zero-cost (already emitted by rustc debug mode).
    pub zero_cost: usize,
    /// Checks that are lightweight (single comparison).
    pub lightweight: usize,
    /// Checks that are expensive (multi-step validation).
    pub expensive: usize,
    /// VCs that were proved and elided.
    pub elided: usize,
}

impl InstrumentationPlan {
    /// Compute an overhead summary for the plan.
    #[must_use]
    pub(crate) fn overhead_summary(&self) -> OverheadSummary {
        let mut zero_cost = 0;
        let mut lightweight = 0;
        let mut expensive = 0;
        for ic in &self.checks {
            match ic.overhead {
                CheckOverhead::ZeroCost => zero_cost += 1,
                CheckOverhead::Lightweight => lightweight += 1,
                CheckOverhead::Expensive => expensive += 1,
            }
        }
        OverheadSummary {
            total_checks: self.checks.len(),
            zero_cost,
            lightweight,
            expensive,
            elided: self.elided_count,
        }
    }

    /// True if all runtime checks are zero-cost.
    #[must_use]
    pub(crate) fn is_zero_overhead(&self) -> bool {
        self.checks.iter().all(|ic| ic.overhead == CheckOverhead::ZeroCost)
    }

    /// True if there are no runtime checks to insert.
    #[must_use]
    pub(crate) fn is_empty(&self) -> bool {
        self.checks.is_empty()
    }
}

// ---------------------------------------------------------------------------
// plan_instrumentation: the main entry point
// ---------------------------------------------------------------------------

/// Plan runtime instrumentation for a function given its verification results.
///
/// For each unproved VC that has a runtime fallback, generates the minimal
/// runtime check. Tracks which checks can be elided (proved VCs) and classifies
/// overhead.
///
/// `overflow_checks` should be true when the target has Rust overflow checks
/// enabled (debug mode). When false, overflow VCs get no runtime fallback.
#[must_use]
pub(crate) fn plan_instrumentation(
    function_name: &str,
    results: &[(VerificationCondition, VerificationResult)],
    overflow_checks: bool,
) -> InstrumentationPlan {
    let mut checks = Vec::new();
    let mut elided_count = 0;
    let mut failed_count = 0;
    let mut no_fallback_count = 0;

    for (vc, result) in results {
        match result {
            VerificationResult::Proved { .. } => {
                // Proved VCs need no runtime check.
                elided_count += 1;
            }
            VerificationResult::Failed { .. } => {
                // Failed VCs have counterexamples -- the code is definitively wrong.
                // Runtime checks won't help; this needs a source fix.
                failed_count += 1;
            }
            VerificationResult::Unknown { solver, reason, .. } => {
                match try_make_check(vc, overflow_checks) {
                    Some((check, overhead)) => {
                        checks.push(InstrumentedCheck {
                            check,
                            overhead,
                            vc_description: vc.kind.description(),
                            reason: InstrumentationReason::Unknown {
                                solver: solver.clone(),
                                reason: reason.clone(),
                            },
                        });
                    }
                    None => no_fallback_count += 1,
                }
            }
            VerificationResult::Timeout { solver, timeout_ms, .. } => {
                match try_make_check(vc, overflow_checks) {
                    Some((check, overhead)) => {
                        checks.push(InstrumentedCheck {
                            check,
                            overhead,
                            vc_description: vc.kind.description(),
                            reason: InstrumentationReason::Timeout {
                                solver: solver.clone(),
                                timeout_ms: *timeout_ms,
                            },
                        });
                    }
                    None => no_fallback_count += 1,
                }
            }
                    _ => {},
        }
    }

    InstrumentationPlan {
        function: function_name.to_string(),
        checks,
        elided_count,
        failed_count,
        no_fallback_count,
    }
}

/// Try to create a RuntimeCheck + overhead for a VC.
/// Returns None if the VcKind has no runtime fallback.
fn try_make_check(
    vc: &VerificationCondition,
    overflow_checks: bool,
) -> Option<(RuntimeCheck, CheckOverhead)> {
    let (kind, strategy) = crate::map_vc_to_check(&vc.kind, overflow_checks)?;
    let overhead = CheckOverhead::from_strategy(&strategy);
    let check = RuntimeCheck {
        kind,
        location: vc.location.clone(),
        description: format!(
            "runtime check: {} ({})",
            vc.kind.description(),
            strategy.description()
        ),
        strategy,
        function: vc.function.clone(),
    };
    Some((check, overhead))
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::CheckKind;
    use trust_types::{BinOp, Counterexample, CounterexampleValue, Formula, ProofStrength, SourceSpan, Ty, VcKind};

    fn vc(kind: VcKind, function: &str) -> VerificationCondition {
        VerificationCondition {
            kind,
            function: function.to_string(),
            location: SourceSpan {
                file: "src/lib.rs".to_string(),
                line_start: 10,
                col_start: 5,
                line_end: 10,
                col_end: 20,
            },
            formula: Formula::Bool(true),
            contract_metadata: None,
        }
    }

    fn unknown() -> VerificationResult {
        VerificationResult::Unknown {
            solver: "z4".to_string(),
            time_ms: 50,
            reason: "nonlinear arithmetic".to_string(),
        }
    }

    fn timeout() -> VerificationResult {
        VerificationResult::Timeout {
            solver: "z4".to_string(),
            timeout_ms: 5000,
        }
    }

    fn proved() -> VerificationResult {
        VerificationResult::Proved {
            solver: "z4".to_string(),
            time_ms: 3,
            strength: ProofStrength::smt_unsat(), proof_certificate: None,
                solver_warnings: None, }
    }

    fn failed() -> VerificationResult {
        VerificationResult::Failed {
            solver: "z4".to_string(),
            time_ms: 5,
            counterexample: Some(Counterexample::new(vec![(
                "x".to_string(),
                CounterexampleValue::Int(-1),
            )])),
        }
    }

    // -----------------------------------------------------------------------
    // CheckOverhead classification
    // -----------------------------------------------------------------------

    #[test]
    fn test_overhead_zero_cost_strategies() {
        assert_eq!(
            CheckOverhead::from_strategy(&CheckStrategy::OverflowCheck { op: trust_types::BinOp::Add }),
            CheckOverhead::ZeroCost
        );
        assert_eq!(
            CheckOverhead::from_strategy(&CheckStrategy::ShiftCheck),
            CheckOverhead::ZeroCost
        );
        assert_eq!(
            CheckOverhead::from_strategy(&CheckStrategy::NegationCheck),
            CheckOverhead::ZeroCost
        );
    }

    #[test]
    fn test_overhead_lightweight_strategies() {
        assert_eq!(
            CheckOverhead::from_strategy(&CheckStrategy::BoundsCheck),
            CheckOverhead::Lightweight
        );
        assert_eq!(
            CheckOverhead::from_strategy(&CheckStrategy::DivisorNonZero),
            CheckOverhead::Lightweight
        );
        assert_eq!(
            CheckOverhead::from_strategy(&CheckStrategy::UnreachablePanic),
            CheckOverhead::Lightweight
        );
        assert_eq!(
            CheckOverhead::from_strategy(&CheckStrategy::PreserveAssertion {
                message: "x".to_string()
            }),
            CheckOverhead::Lightweight
        );
    }

    #[test]
    fn test_overhead_expensive_strategies() {
        assert_eq!(
            CheckOverhead::from_strategy(&CheckStrategy::SliceRangeCheck),
            CheckOverhead::Expensive
        );
    }

    // -----------------------------------------------------------------------
    // plan_instrumentation: basic scenarios
    // -----------------------------------------------------------------------

    #[test]
    fn test_plan_empty_results() {
        let plan = plan_instrumentation("f", &[], true);
        assert!(plan.is_empty());
        assert_eq!(plan.elided_count, 0);
        assert_eq!(plan.failed_count, 0);
        assert_eq!(plan.no_fallback_count, 0);
        assert!(plan.is_zero_overhead());
    }

    #[test]
    fn test_plan_all_proved() {
        let results = vec![
            (vc(VcKind::DivisionByZero, "f"), proved()),
            (vc(VcKind::IndexOutOfBounds, "f"), proved()),
        ];
        let plan = plan_instrumentation("f", &results, true);
        assert!(plan.is_empty());
        assert_eq!(plan.elided_count, 2);
        assert_eq!(plan.failed_count, 0);
    }

    #[test]
    fn test_plan_all_failed() {
        let results = vec![
            (vc(VcKind::DivisionByZero, "f"), failed()),
            (vc(VcKind::IndexOutOfBounds, "f"), failed()),
        ];
        let plan = plan_instrumentation("f", &results, true);
        assert!(plan.is_empty());
        assert_eq!(plan.elided_count, 0);
        assert_eq!(plan.failed_count, 2);
    }

    #[test]
    fn test_plan_unknown_with_fallback() {
        let results = vec![(vc(VcKind::IndexOutOfBounds, "lookup"), unknown())];
        let plan = plan_instrumentation("lookup", &results, true);
        assert_eq!(plan.checks.len(), 1);
        assert_eq!(plan.checks[0].check.kind, CheckKind::IndexOutOfBounds);
        assert_eq!(plan.checks[0].overhead, CheckOverhead::Lightweight);
        assert!(matches!(
            &plan.checks[0].reason,
            InstrumentationReason::Unknown { solver, .. } if solver == "z4"
        ));
    }

    #[test]
    fn test_plan_timeout_with_fallback() {
        let results = vec![(vc(VcKind::DivisionByZero, "safe_div"), timeout())];
        let plan = plan_instrumentation("safe_div", &results, true);
        assert_eq!(plan.checks.len(), 1);
        assert_eq!(plan.checks[0].check.kind, CheckKind::DivisionByZero);
        assert!(matches!(
            &plan.checks[0].reason,
            InstrumentationReason::Timeout { timeout_ms: 5000, .. }
        ));
    }

    #[test]
    fn test_plan_unknown_without_fallback() {
        let results = vec![(vc(VcKind::Postcondition, "f"), unknown())];
        let plan = plan_instrumentation("f", &results, true);
        assert!(plan.is_empty());
        assert_eq!(plan.no_fallback_count, 1);
    }

    #[test]
    fn test_plan_overflow_without_overflow_checks() {
        let results = vec![(
            vc(
                VcKind::ArithmeticOverflow {
                    op: BinOp::Add,
                    operand_tys: (Ty::i32(), Ty::i32()),
                },
                "add",
            ),
            unknown(),
        )];
        let plan = plan_instrumentation("add", &results, false);
        assert!(plan.is_empty());
        assert_eq!(plan.no_fallback_count, 1);
    }

    // -----------------------------------------------------------------------
    // Mixed results
    // -----------------------------------------------------------------------

    #[test]
    fn test_plan_mixed_results() {
        let results = vec![
            // Proved: elided
            (vc(VcKind::DivisionByZero, "f"), proved()),
            // Failed: counted
            (vc(VcKind::IndexOutOfBounds, "f"), failed()),
            // Unknown with fallback: check inserted
            (
                vc(
                    VcKind::ArithmeticOverflow {
                        op: BinOp::Add,
                        operand_tys: (Ty::u32(), Ty::u32()),
                    },
                    "f",
                ),
                unknown(),
            ),
            // Timeout with fallback: check inserted
            (vc(VcKind::SliceBoundsCheck, "f"), timeout()),
            // Unknown without fallback: no_fallback
            (vc(VcKind::Postcondition, "f"), unknown()),
        ];

        let plan = plan_instrumentation("f", &results, true);
        assert_eq!(plan.checks.len(), 2);
        assert_eq!(plan.elided_count, 1);
        assert_eq!(plan.failed_count, 1);
        assert_eq!(plan.no_fallback_count, 1);

        assert_eq!(plan.checks[0].check.kind, CheckKind::ArithmeticOverflow);
        assert_eq!(plan.checks[0].overhead, CheckOverhead::ZeroCost);
        assert_eq!(plan.checks[1].check.kind, CheckKind::SliceBoundsCheck);
        assert_eq!(plan.checks[1].overhead, CheckOverhead::Expensive);
    }

    // -----------------------------------------------------------------------
    // OverheadSummary
    // -----------------------------------------------------------------------

    #[test]
    fn test_overhead_summary() {
        let results = vec![
            (vc(VcKind::DivisionByZero, "f"), proved()),
            (
                vc(
                    VcKind::ArithmeticOverflow {
                        op: BinOp::Add,
                        operand_tys: (Ty::i32(), Ty::i32()),
                    },
                    "f",
                ),
                unknown(),
            ),
            (vc(VcKind::IndexOutOfBounds, "f"), timeout()),
            (vc(VcKind::SliceBoundsCheck, "f"), unknown()),
        ];

        let plan = plan_instrumentation("f", &results, true);
        let summary = plan.overhead_summary();
        assert_eq!(summary.total_checks, 3);
        assert_eq!(summary.zero_cost, 1); // ArithmeticOverflow
        assert_eq!(summary.lightweight, 1); // IndexOutOfBounds
        assert_eq!(summary.expensive, 1); // SliceBoundsCheck
        assert_eq!(summary.elided, 1); // proved DivisionByZero
    }

    #[test]
    fn test_is_zero_overhead_true() {
        let results = vec![(
            vc(
                VcKind::ArithmeticOverflow {
                    op: BinOp::Add,
                    operand_tys: (Ty::i32(), Ty::i32()),
                },
                "f",
            ),
            unknown(),
        )];
        let plan = plan_instrumentation("f", &results, true);
        assert!(plan.is_zero_overhead());
    }

    #[test]
    fn test_is_zero_overhead_false() {
        let results = vec![(vc(VcKind::IndexOutOfBounds, "f"), unknown())];
        let plan = plan_instrumentation("f", &results, true);
        assert!(!plan.is_zero_overhead());
    }

    #[test]
    fn test_plan_function_name() {
        let plan = plan_instrumentation("my_func", &[], true);
        assert_eq!(plan.function, "my_func");
    }

    // -----------------------------------------------------------------------
    // Serialization
    // -----------------------------------------------------------------------

    #[test]
    fn test_plan_serialization_roundtrip() {
        let results = vec![
            (vc(VcKind::IndexOutOfBounds, "lookup"), unknown()),
            (vc(VcKind::DivisionByZero, "divide"), timeout()),
        ];
        let plan = plan_instrumentation("test_fn", &results, true);
        let json = serde_json::to_string(&plan).expect("serialize");
        let roundtrip: InstrumentationPlan = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(roundtrip.function, "test_fn");
        assert_eq!(roundtrip.checks.len(), 2);
        assert_eq!(roundtrip.checks[0].overhead, CheckOverhead::Lightweight);
    }
}
