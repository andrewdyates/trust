#![allow(dead_code)]
//! trust-runtime: Runtime check insertion for unproved verification conditions
//!
//! When a VC cannot be statically proved, this crate generates runtime checks
//! (assertions, bounds checks, overflow guards) as dynamic verification fallback.
//! Respects RuntimeCheckPolicy from trust-types.
//!
//! Author: Andrew Yates <andrew@andrewdyates.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

pub(crate) mod assertions;
pub(crate) mod codegen;
pub(crate) mod contract;
pub(crate) mod instrumentation;
pub(crate) mod monitor;
pub(crate) mod optimization;
pub(crate) mod reporting;
pub(crate) mod sampling;

use serde::{Deserialize, Serialize};
use trust_types::{
    BinOp, RuntimeCheckPolicy, SourceSpan, VcKind, VerificationCondition, VerificationResult,
};

/// A runtime check to be inserted into compiled code as a dynamic verification
/// fallback for an unproved verification condition.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct RuntimeCheck {
    /// The kind of VC this check enforces.
    pub kind: CheckKind,
    /// Source location where the check should be inserted.
    pub location: SourceSpan,
    /// Human-readable description of what this check verifies.
    pub description: String,
    /// The check strategy (what kind of runtime assertion to insert).
    pub strategy: CheckStrategy,
    /// Name of the function containing this check.
    pub function: String,
}

/// Categorization of runtime checks, derived from VcKind but simplified
/// to the set of VcKinds that have runtime fallbacks.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub(crate) enum CheckKind {
    ArithmeticOverflow,
    ShiftOverflow,
    NegationOverflow,
    DivisionByZero,
    RemainderByZero,
    IndexOutOfBounds,
    SliceBoundsCheck,
    Assertion { message: String },
    Unreachable,
}

/// How the runtime check should be enforced.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub(crate) enum CheckStrategy {
    /// Use Rust's built-in overflow-checked arithmetic (debug_assert on overflow).
    /// Carries the [`BinOp`] so codegen emits the correct `checked_*` call.
    OverflowCheck { op: BinOp },
    /// Insert an explicit bounds check: `assert!(index < len)`.
    BoundsCheck,
    /// Insert a divisor-nonzero check: `assert!(divisor != 0)`.
    DivisorNonZero,
    /// Insert a slice range check: `assert!(start <= end && end <= len)`.
    SliceRangeCheck,
    /// Preserve the original `assert!()` / `debug_assert!()`.
    PreserveAssertion { message: String },
    /// Insert `unreachable!()` — Rust already panics on this, but we make it explicit.
    UnreachablePanic,
    /// Use Rust's built-in shift overflow check.
    ShiftCheck,
    /// Use Rust's built-in negation overflow check.
    NegationCheck,
}

impl CheckStrategy {
    /// Human-readable description of the check strategy.
    #[must_use]
    pub(crate) fn description(&self) -> &str {
        match self {
            CheckStrategy::OverflowCheck { .. } => "overflow-checked arithmetic",
            CheckStrategy::BoundsCheck => "index bounds assertion",
            CheckStrategy::DivisorNonZero => "divisor != 0 assertion",
            CheckStrategy::SliceRangeCheck => "slice range assertion",
            CheckStrategy::PreserveAssertion { .. } => "preserved source assertion",
            CheckStrategy::UnreachablePanic => "unreachable!() panic",
            CheckStrategy::ShiftCheck => "shift distance check",
            CheckStrategy::NegationCheck => "negation overflow check",
        }
    }
}

/// Maps a VcKind to a (CheckKind, CheckStrategy) pair if the VcKind supports
/// runtime fallback. Returns None for VcKinds without runtime checks.
pub(crate) fn map_vc_to_check(vc_kind: &VcKind, overflow_checks: bool) -> Option<(CheckKind, CheckStrategy)> {
    match vc_kind {
        VcKind::ArithmeticOverflow { op, .. } if overflow_checks => {
            Some((CheckKind::ArithmeticOverflow, CheckStrategy::OverflowCheck { op: *op }))
        }
        VcKind::ShiftOverflow { .. } if overflow_checks => {
            Some((CheckKind::ShiftOverflow, CheckStrategy::ShiftCheck))
        }
        VcKind::NegationOverflow { .. } if overflow_checks => {
            Some((CheckKind::NegationOverflow, CheckStrategy::NegationCheck))
        }
        VcKind::DivisionByZero => {
            Some((CheckKind::DivisionByZero, CheckStrategy::DivisorNonZero))
        }
        VcKind::RemainderByZero => {
            Some((CheckKind::RemainderByZero, CheckStrategy::DivisorNonZero))
        }
        VcKind::IndexOutOfBounds => {
            Some((CheckKind::IndexOutOfBounds, CheckStrategy::BoundsCheck))
        }
        VcKind::SliceBoundsCheck => {
            Some((CheckKind::SliceBoundsCheck, CheckStrategy::SliceRangeCheck))
        }
        VcKind::Assertion { message } => Some((
            CheckKind::Assertion { message: message.clone() },
            CheckStrategy::PreserveAssertion { message: message.clone() },
        )),
        VcKind::Unreachable => {
            Some((CheckKind::Unreachable, CheckStrategy::UnreachablePanic))
        }
        // All other VcKinds have no runtime fallback.
        _ => None,
    }
}

/// Generates runtime checks for unproved verification conditions.
///
/// Examines each (VC, result) pair and, based on the policy, decides whether
/// to generate a runtime check as fallback for VCs that could not be statically
/// proved.
pub(crate) struct RuntimeCheckInserter {
    policy: RuntimeCheckPolicy,
    overflow_checks: bool,
}

impl RuntimeCheckInserter {
    /// Create a new inserter with the given policy and overflow check configuration.
    #[must_use]
    pub(crate) fn new(policy: RuntimeCheckPolicy, overflow_checks: bool) -> Self {
        Self { policy, overflow_checks }
    }

    /// Generate runtime checks for a set of verification results.
    ///
    /// For each (VC, result) pair:
    /// - If proved or failed with counterexample: no runtime check needed
    /// - If Unknown or Timeout: generate a check if the VcKind has a runtime
    ///   fallback and the policy allows it
    ///
    /// Policy behavior:
    /// - `Auto`: generate checks only for VcKinds with `has_runtime_fallback`
    /// - `ForceRuntime`: generate checks for all inconclusive VcKinds that
    ///   can be mapped to a check (even proved ones get a check)
    /// - `ForceStatic`: never generate runtime checks
    #[must_use]
    pub(crate) fn generate_checks(
        &self,
        results: &[(VerificationCondition, VerificationResult)],
    ) -> Vec<RuntimeCheck> {
        if self.policy == RuntimeCheckPolicy::ForceStatic {
            return Vec::new();
        }

        results
            .iter()
            .filter_map(|(vc, result)| self.maybe_generate_check(vc, result))
            .collect()
    }

    /// Decide whether a single (VC, result) pair needs a runtime check.
    fn maybe_generate_check(
        &self,
        vc: &VerificationCondition,
        result: &VerificationResult,
    ) -> Option<RuntimeCheck> {
        let needs_check = match self.policy {
            RuntimeCheckPolicy::ForceStatic => return None,
            RuntimeCheckPolicy::ForceRuntime => {
                // Generate checks for everything except concrete failures
                // (which have counterexamples — the code is definitively wrong).
                !result.is_failed()
            }
            RuntimeCheckPolicy::Auto => {
                // Only generate checks for inconclusive results (Unknown/Timeout)
                // where the VcKind has a corresponding runtime check.
                matches!(
                    result,
                    VerificationResult::Unknown { .. } | VerificationResult::Timeout { .. }
                ) && vc.kind.has_runtime_fallback(self.overflow_checks)
            }
            _ => false,
        };

        if !needs_check {
            return None;
        }

        let (kind, strategy) = map_vc_to_check(&vc.kind, self.overflow_checks)?;

        Some(RuntimeCheck {
            kind,
            location: vc.location.clone(),
            description: format!(
                "runtime check: {} ({})",
                vc.kind.description(),
                strategy.description()
            ),
            strategy,
            function: vc.function.clone(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_types::{BinOp, Ty};
    use trust_types::{Counterexample, CounterexampleValue, Formula, ProofStrength};

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

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
    // map_vc_to_check tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_map_arithmetic_overflow_with_overflow_checks() {
        let vc_kind = VcKind::ArithmeticOverflow {
            op: BinOp::Add,
            operand_tys: (Ty::i32(), Ty::i32()),
        };
        let result = map_vc_to_check(&vc_kind, true);
        assert!(result.is_some());
        let (kind, strategy) = result.unwrap();
        assert_eq!(kind, CheckKind::ArithmeticOverflow);
        assert_eq!(strategy, CheckStrategy::OverflowCheck { op: BinOp::Add });
    }

    #[test]
    fn test_map_arithmetic_overflow_without_overflow_checks() {
        let vc_kind = VcKind::ArithmeticOverflow {
            op: BinOp::Add,
            operand_tys: (Ty::i32(), Ty::i32()),
        };
        assert!(map_vc_to_check(&vc_kind, false).is_none());
    }

    #[test]
    fn test_map_shift_overflow() {
        let vc_kind = VcKind::ShiftOverflow {
            op: BinOp::Shl,
            operand_ty: Ty::u32(),
            shift_ty: Ty::u32(),
        };
        let (kind, strategy) = map_vc_to_check(&vc_kind, true).unwrap();
        assert_eq!(kind, CheckKind::ShiftOverflow);
        assert_eq!(strategy, CheckStrategy::ShiftCheck);
    }

    #[test]
    fn test_map_negation_overflow() {
        let vc_kind = VcKind::NegationOverflow { ty: Ty::i32() };
        let (kind, strategy) = map_vc_to_check(&vc_kind, true).unwrap();
        assert_eq!(kind, CheckKind::NegationOverflow);
        assert_eq!(strategy, CheckStrategy::NegationCheck);
    }

    #[test]
    fn test_map_division_by_zero() {
        let (kind, strategy) = map_vc_to_check(&VcKind::DivisionByZero, true).unwrap();
        assert_eq!(kind, CheckKind::DivisionByZero);
        assert_eq!(strategy, CheckStrategy::DivisorNonZero);
    }

    #[test]
    fn test_map_remainder_by_zero() {
        let (kind, strategy) = map_vc_to_check(&VcKind::RemainderByZero, true).unwrap();
        assert_eq!(kind, CheckKind::RemainderByZero);
        assert_eq!(strategy, CheckStrategy::DivisorNonZero);
    }

    #[test]
    fn test_map_index_out_of_bounds() {
        let (kind, strategy) = map_vc_to_check(&VcKind::IndexOutOfBounds, true).unwrap();
        assert_eq!(kind, CheckKind::IndexOutOfBounds);
        assert_eq!(strategy, CheckStrategy::BoundsCheck);
    }

    #[test]
    fn test_map_slice_bounds_check() {
        let (kind, strategy) = map_vc_to_check(&VcKind::SliceBoundsCheck, true).unwrap();
        assert_eq!(kind, CheckKind::SliceBoundsCheck);
        assert_eq!(strategy, CheckStrategy::SliceRangeCheck);
    }

    #[test]
    fn test_map_assertion() {
        let vc_kind = VcKind::Assertion { message: "invariant holds".to_string() };
        let (kind, strategy) = map_vc_to_check(&vc_kind, true).unwrap();
        assert_eq!(kind, CheckKind::Assertion { message: "invariant holds".to_string() });
        assert_eq!(
            strategy,
            CheckStrategy::PreserveAssertion { message: "invariant holds".to_string() }
        );
    }

    #[test]
    fn test_map_unreachable() {
        let (kind, strategy) = map_vc_to_check(&VcKind::Unreachable, true).unwrap();
        assert_eq!(kind, CheckKind::Unreachable);
        assert_eq!(strategy, CheckStrategy::UnreachablePanic);
    }

    #[test]
    fn test_map_postcondition_has_no_fallback() {
        assert!(map_vc_to_check(&VcKind::Postcondition, true).is_none());
    }

    #[test]
    fn test_map_precondition_has_no_fallback() {
        let vc_kind = VcKind::Precondition { callee: "foo".to_string() };
        assert!(map_vc_to_check(&vc_kind, true).is_none());
    }

    #[test]
    fn test_map_deadlock_has_no_fallback() {
        assert!(map_vc_to_check(&VcKind::Deadlock, true).is_none());
    }

    #[test]
    fn test_map_cast_overflow_has_no_fallback() {
        let vc_kind = VcKind::CastOverflow { from_ty: Ty::isize(), to_ty: Ty::i32() };
        assert!(map_vc_to_check(&vc_kind, true).is_none());
    }

    // -----------------------------------------------------------------------
    // RuntimeCheckInserter::generate_checks tests — Auto policy
    // -----------------------------------------------------------------------

    #[test]
    fn test_auto_policy_generates_check_for_unknown_with_fallback() {
        let inserter = RuntimeCheckInserter::new(RuntimeCheckPolicy::Auto, true);
        let results = vec![(vc(VcKind::IndexOutOfBounds, "lookup"), unknown())];
        let checks = inserter.generate_checks(&results);
        assert_eq!(checks.len(), 1);
        assert_eq!(checks[0].kind, CheckKind::IndexOutOfBounds);
        assert_eq!(checks[0].strategy, CheckStrategy::BoundsCheck);
        assert_eq!(checks[0].function, "lookup");
    }

    #[test]
    fn test_auto_policy_generates_check_for_timeout_with_fallback() {
        let inserter = RuntimeCheckInserter::new(RuntimeCheckPolicy::Auto, true);
        let results = vec![(vc(VcKind::DivisionByZero, "safe_div"), timeout())];
        let checks = inserter.generate_checks(&results);
        assert_eq!(checks.len(), 1);
        assert_eq!(checks[0].kind, CheckKind::DivisionByZero);
        assert_eq!(checks[0].strategy, CheckStrategy::DivisorNonZero);
    }

    #[test]
    fn test_auto_policy_skips_proved_results() {
        let inserter = RuntimeCheckInserter::new(RuntimeCheckPolicy::Auto, true);
        let results = vec![(vc(VcKind::DivisionByZero, "f"), proved())];
        let checks = inserter.generate_checks(&results);
        assert!(checks.is_empty());
    }

    #[test]
    fn test_auto_policy_skips_failed_results() {
        let inserter = RuntimeCheckInserter::new(RuntimeCheckPolicy::Auto, true);
        let results = vec![(vc(VcKind::IndexOutOfBounds, "f"), failed())];
        let checks = inserter.generate_checks(&results);
        assert!(checks.is_empty());
    }

    #[test]
    fn test_auto_policy_skips_unknown_without_fallback() {
        let inserter = RuntimeCheckInserter::new(RuntimeCheckPolicy::Auto, true);
        let results = vec![(vc(VcKind::Postcondition, "f"), unknown())];
        let checks = inserter.generate_checks(&results);
        assert!(checks.is_empty());
    }

    #[test]
    fn test_auto_policy_respects_overflow_checks_flag() {
        let inserter = RuntimeCheckInserter::new(RuntimeCheckPolicy::Auto, false);
        let results = vec![(
            vc(
                VcKind::ArithmeticOverflow {
                    op: BinOp::Add,
                    operand_tys: (Ty::i32(), Ty::i32()),
                },
                "checked_add",
            ),
            unknown(),
        )];
        let checks = inserter.generate_checks(&results);
        // overflow_checks=false means ArithmeticOverflow has no runtime fallback
        assert!(checks.is_empty());
    }

    #[test]
    fn test_auto_policy_with_overflow_checks_enabled() {
        let inserter = RuntimeCheckInserter::new(RuntimeCheckPolicy::Auto, true);
        let results = vec![(
            vc(
                VcKind::ArithmeticOverflow {
                    op: BinOp::Mul,
                    operand_tys: (Ty::usize(), Ty::usize()),
                },
                "multiply",
            ),
            unknown(),
        )];
        let checks = inserter.generate_checks(&results);
        assert_eq!(checks.len(), 1);
        assert_eq!(checks[0].kind, CheckKind::ArithmeticOverflow);
    }

    // -----------------------------------------------------------------------
    // ForceStatic policy
    // -----------------------------------------------------------------------

    #[test]
    fn test_force_static_never_generates_checks() {
        let inserter = RuntimeCheckInserter::new(RuntimeCheckPolicy::ForceStatic, true);
        let results = vec![
            (vc(VcKind::IndexOutOfBounds, "f"), unknown()),
            (vc(VcKind::DivisionByZero, "g"), timeout()),
            (
                vc(
                    VcKind::ArithmeticOverflow {
                        op: BinOp::Add,
                        operand_tys: (Ty::i32(), Ty::i32()),
                    },
                    "h",
                ),
                unknown(),
            ),
        ];
        let checks = inserter.generate_checks(&results);
        assert!(checks.is_empty());
    }

    // -----------------------------------------------------------------------
    // ForceRuntime policy
    // -----------------------------------------------------------------------

    #[test]
    fn test_force_runtime_generates_checks_for_proved_results() {
        let inserter = RuntimeCheckInserter::new(RuntimeCheckPolicy::ForceRuntime, true);
        let results = vec![(vc(VcKind::DivisionByZero, "safe_div"), proved())];
        let checks = inserter.generate_checks(&results);
        assert_eq!(checks.len(), 1);
        assert_eq!(checks[0].kind, CheckKind::DivisionByZero);
    }

    #[test]
    fn test_force_runtime_generates_checks_for_unknown_results() {
        let inserter = RuntimeCheckInserter::new(RuntimeCheckPolicy::ForceRuntime, true);
        let results = vec![(vc(VcKind::IndexOutOfBounds, "lookup"), unknown())];
        let checks = inserter.generate_checks(&results);
        assert_eq!(checks.len(), 1);
    }

    #[test]
    fn test_force_runtime_skips_failed_results() {
        let inserter = RuntimeCheckInserter::new(RuntimeCheckPolicy::ForceRuntime, true);
        let results = vec![(vc(VcKind::IndexOutOfBounds, "lookup"), failed())];
        let checks = inserter.generate_checks(&results);
        assert!(checks.is_empty());
    }

    #[test]
    fn test_force_runtime_skips_vc_kinds_without_mapping() {
        let inserter = RuntimeCheckInserter::new(RuntimeCheckPolicy::ForceRuntime, true);
        let results = vec![(vc(VcKind::Postcondition, "f"), unknown())];
        let checks = inserter.generate_checks(&results);
        // Postcondition has no runtime check mapping
        assert!(checks.is_empty());
    }

    // -----------------------------------------------------------------------
    // Mixed results
    // -----------------------------------------------------------------------

    #[test]
    fn test_mixed_results_auto_policy() {
        let inserter = RuntimeCheckInserter::new(RuntimeCheckPolicy::Auto, true);
        let results = vec![
            // Proved: no check
            (vc(VcKind::DivisionByZero, "safe_div"), proved()),
            // Failed: no check
            (vc(VcKind::IndexOutOfBounds, "bad_lookup"), failed()),
            // Unknown with fallback: generates check
            (
                vc(
                    VcKind::ArithmeticOverflow {
                        op: BinOp::Add,
                        operand_tys: (Ty::u32(), Ty::u32()),
                    },
                    "maybe_overflow",
                ),
                unknown(),
            ),
            // Timeout with fallback: generates check
            (vc(VcKind::SliceBoundsCheck, "slice_op"), timeout()),
            // Unknown without fallback: no check
            (vc(VcKind::Postcondition, "contract_fn"), unknown()),
        ];

        let checks = inserter.generate_checks(&results);
        assert_eq!(checks.len(), 2);
        assert_eq!(checks[0].function, "maybe_overflow");
        assert_eq!(checks[0].kind, CheckKind::ArithmeticOverflow);
        assert_eq!(checks[1].function, "slice_op");
        assert_eq!(checks[1].kind, CheckKind::SliceBoundsCheck);
    }

    #[test]
    fn test_empty_results_produces_no_checks() {
        let inserter = RuntimeCheckInserter::new(RuntimeCheckPolicy::Auto, true);
        let checks = inserter.generate_checks(&[]);
        assert!(checks.is_empty());
    }

    // -----------------------------------------------------------------------
    // RuntimeCheck fields
    // -----------------------------------------------------------------------

    #[test]
    fn test_runtime_check_has_correct_location() {
        let inserter = RuntimeCheckInserter::new(RuntimeCheckPolicy::Auto, true);
        let results = vec![(vc(VcKind::DivisionByZero, "f"), unknown())];
        let checks = inserter.generate_checks(&results);
        assert_eq!(checks[0].location.file, "src/lib.rs");
        assert_eq!(checks[0].location.line_start, 10);
        assert_eq!(checks[0].location.col_start, 5);
    }

    #[test]
    fn test_runtime_check_description_includes_strategy() {
        let inserter = RuntimeCheckInserter::new(RuntimeCheckPolicy::Auto, true);
        let results = vec![(vc(VcKind::IndexOutOfBounds, "lookup"), unknown())];
        let checks = inserter.generate_checks(&results);
        assert!(checks[0].description.contains("index out of bounds"));
        assert!(checks[0].description.contains("index bounds assertion"));
    }

    // -----------------------------------------------------------------------
    // CheckStrategy::description
    // -----------------------------------------------------------------------

    #[test]
    fn test_check_strategy_descriptions() {
        assert_eq!(CheckStrategy::OverflowCheck { op: BinOp::Add }.description(), "overflow-checked arithmetic");
        assert_eq!(CheckStrategy::BoundsCheck.description(), "index bounds assertion");
        assert_eq!(CheckStrategy::DivisorNonZero.description(), "divisor != 0 assertion");
        assert_eq!(CheckStrategy::SliceRangeCheck.description(), "slice range assertion");
        assert_eq!(CheckStrategy::UnreachablePanic.description(), "unreachable!() panic");
        assert_eq!(CheckStrategy::ShiftCheck.description(), "shift distance check");
        assert_eq!(CheckStrategy::NegationCheck.description(), "negation overflow check");
        assert_eq!(
            CheckStrategy::PreserveAssertion { message: "x".to_string() }.description(),
            "preserved source assertion"
        );
    }

    // -----------------------------------------------------------------------
    // Serialization roundtrip
    // -----------------------------------------------------------------------

    #[test]
    fn test_runtime_check_serialization_roundtrip() {
        let inserter = RuntimeCheckInserter::new(RuntimeCheckPolicy::Auto, true);
        let results = vec![
            (vc(VcKind::IndexOutOfBounds, "lookup"), unknown()),
            (vc(VcKind::DivisionByZero, "divide"), timeout()),
        ];
        let checks = inserter.generate_checks(&results);
        assert_eq!(checks.len(), 2);

        let json = serde_json::to_string(&checks).expect("serialize");
        let roundtrip: Vec<RuntimeCheck> = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(roundtrip.len(), 2);
        assert_eq!(roundtrip[0].kind, CheckKind::IndexOutOfBounds);
        assert_eq!(roundtrip[1].kind, CheckKind::DivisionByZero);
    }
}
