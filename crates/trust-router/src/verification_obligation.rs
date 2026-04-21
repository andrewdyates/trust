// trust-router/verification_obligation.rs: Pipeline v2 obligation adapter
//
// tRust #791: Maps external tool results (zani-lib, sunder-lib) back to
// per-obligation identities so the tRust report pipeline can attribute
// verification outcomes to specific source spans, VcKinds, and functions.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

//! Verification obligation adapter for Pipeline v2.
//!
//! The v1 pipeline produces `VerificationCondition` objects (with a `Formula`)
//! that flow through the `Router`. The v2 pipeline operates at the MIR level,
//! dispatching whole functions to zani-lib or sunder-lib. These external tools
//! return their own result types (`ZaniResult`, `SunderResult`), which need to
//! be mapped back to per-obligation identities for the report pipeline.
//!
//! `VerificationObligation` is the bridge: it captures the function identity,
//! source span, strategy used, and the resulting `VerificationResult` in a
//! single struct that the report pipeline can consume uniformly regardless
//! of which pipeline (v1 or v2) produced it.

use trust_types::{SourceSpan, VcKind, VerificationResult};

use crate::mir_router::MirStrategy;
use trust_types::fx::FxHashMap;

/// A verification obligation with its result, produced by the v2 pipeline.
///
/// Unlike the v1 `VerificationCondition` (which carries a `Formula` for the
/// solver), this type is result-oriented: it records what was verified, how,
/// and what the outcome was. It serves as the common output type for both
/// pipelines, enabling unified reporting and comparison.
#[derive(Debug, Clone)]
pub struct VerificationObligation {
    /// Fully qualified function path (e.g., `my_crate::my_module::my_fn`).
    pub def_path: String,

    /// Short function name for display.
    pub function_name: String,

    /// Source location of the function or obligation.
    pub span: SourceSpan,

    /// The kind of verification obligation (safety, contract, overflow, etc.).
    pub kind: VcKind,

    /// The MIR-level strategy that was used to verify this obligation.
    /// `None` if this obligation came from the v1 pipeline.
    pub strategy: Option<MirStrategy>,

    /// The verification result.
    result: VerificationResult,
}

impl VerificationObligation {
    /// Create a new obligation without a result (defaults to Unknown).
    #[must_use]
    pub fn new(
        def_path: String,
        function_name: String,
        span: SourceSpan,
        kind: VcKind,
    ) -> Self {
        Self {
            def_path,
            function_name,
            span,
            kind,
            strategy: None,
            result: VerificationResult::Unknown {
                solver: "pending".to_string(),
                time_ms: 0,
                reason: "not yet dispatched".to_string(),
            },
        }
    }

    /// Attach a verification result to this obligation.
    #[must_use]
    pub fn with_result(mut self, result: VerificationResult) -> Self {
        self.result = result;
        self
    }

    /// Attach a MIR strategy to this obligation.
    #[must_use]
    pub fn with_strategy(mut self, strategy: MirStrategy) -> Self {
        self.strategy = Some(strategy);
        self
    }

    /// Get the verification result.
    #[must_use]
    pub fn result(&self) -> &VerificationResult {
        &self.result
    }

    /// Returns `true` if this obligation was proved.
    #[must_use]
    pub fn is_proved(&self) -> bool {
        self.result.is_proved()
    }

    /// Returns `true` if this obligation failed (counterexample found).
    #[must_use]
    pub fn is_failed(&self) -> bool {
        self.result.is_failed()
    }

    /// Returns the solver name from the result, if available.
    #[must_use]
    pub fn solver_name(&self) -> &str {
        match &self.result {
            VerificationResult::Proved { solver, .. }
            | VerificationResult::Failed { solver, .. }
            | VerificationResult::Unknown { solver, .. }
            | VerificationResult::Timeout { solver, .. } => solver.as_str(),
            _ => "unknown",
        }
    }

    /// Convert a batch of v2 MirRouter results into `VerificationObligation`s.
    ///
    /// Each tuple from `MirRouter::verify_all` is mapped to an obligation
    /// with the appropriate VcKind inferred from the MirStrategy.
    pub fn from_mir_results(
        results: Vec<(String, MirStrategy, VerificationResult)>,
        spans: &FxHashMap<String, SourceSpan>,
    ) -> Vec<Self> {
        results
            .into_iter()
            .map(|(name, strategy, result)| {
                let span = spans.get(&name).cloned().unwrap_or_default();
                let kind = vc_kind_for_strategy(&strategy);
                Self {
                    def_path: name.clone(),
                    function_name: short_name(&name),
                    span,
                    kind,
                    strategy: Some(strategy),
                    result,
                }
            })
            .collect()
    }

    /// Convert a batch of v1 Router results into `VerificationObligation`s.
    ///
    /// Each `(VerificationCondition, VerificationResult)` pair from
    /// `Router::verify_all` is mapped to an obligation with no MirStrategy.
    pub fn from_v1_results(
        results: Vec<(trust_types::VerificationCondition, VerificationResult)>,
    ) -> Vec<Self> {
        results
            .into_iter()
            .map(|(vc, result)| Self {
                def_path: vc.function.clone(),
                function_name: short_name(&vc.function),
                span: vc.location.clone(),
                kind: vc.kind.clone(),
                strategy: None,
                result,
            })
            .collect()
    }
}

/// Infer a VcKind from a MirStrategy (crate-internal).
///
/// Used by `Router::verify_function_v2` to map MirStrategy to VcKind.
pub(crate) fn vc_kind_for_mir_strategy(strategy: &MirStrategy) -> VcKind {
    vc_kind_for_strategy(strategy)
}

/// Internal helper: infer a VcKind from a MirStrategy.
///
/// Since v2 strategies operate at the function level rather than the formula
/// level, we map each strategy to the broadest applicable VcKind.
fn vc_kind_for_strategy(strategy: &MirStrategy) -> VcKind {
    match strategy {
        MirStrategy::BoundedModelCheck => VcKind::Assertion {
            message: "bounded model check (zani-lib)".to_string(),
        },
        MirStrategy::ContractVerification => VcKind::Postcondition,
        MirStrategy::UnsafeAudit => VcKind::UnsafeOperation {
            desc: "unsafe audit (zani-lib + sunder-lib)".to_string(),
        },
        MirStrategy::SeparationLogic => VcKind::Assertion {
            message: "separation logic safety".to_string(),
        },
        MirStrategy::DataRace => VcKind::DataRace {
            variable: String::new(),
            thread_a: String::new(),
            thread_b: String::new(),
        },
        MirStrategy::FFIBoundary => VcKind::FfiBoundaryViolation {
            callee: String::new(),
            desc: "FFI boundary verification".to_string(),
        },
        MirStrategy::Portfolio(_) => VcKind::Assertion {
            message: "portfolio strategy".to_string(),
        },
        MirStrategy::V1Fallback => VcKind::Assertion {
            message: "v1 pipeline fallback".to_string(),
        },
    }
}

/// Extract a short function name from a fully qualified path.
fn short_name(def_path: &str) -> String {
    def_path
        .rsplit("::")
        .next()
        .unwrap_or(def_path)
        .to_string()
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_types::ProofStrength;

    #[test]
    fn test_obligation_creation() {
        let ob = VerificationObligation::new(
            "test::my_fn".to_string(),
            "my_fn".to_string(),
            SourceSpan::default(),
            VcKind::Assertion { message: "safety check".to_string() },
        );
        assert!(!ob.is_proved());
        assert!(!ob.is_failed());
        assert_eq!(ob.solver_name(), "pending");
        assert!(ob.strategy.is_none());
    }

    #[test]
    fn test_obligation_with_result() {
        let ob = VerificationObligation::new(
            "test::proved_fn".to_string(),
            "proved_fn".to_string(),
            SourceSpan::default(),
            VcKind::DivisionByZero,
        )
        .with_result(VerificationResult::Proved {
            solver: "zani-lib".to_string(),
            time_ms: 42,
            strength: ProofStrength::bounded(100),
            proof_certificate: None,
            solver_warnings: None,
        })
        .with_strategy(MirStrategy::BoundedModelCheck);

        assert!(ob.is_proved());
        assert!(!ob.is_failed());
        assert_eq!(ob.solver_name(), "zani-lib");
        assert_eq!(ob.strategy, Some(MirStrategy::BoundedModelCheck));
    }

    #[test]
    fn test_obligation_failed() {
        let ob = VerificationObligation::new(
            "test::bad_fn".to_string(),
            "bad_fn".to_string(),
            SourceSpan::default(),
            VcKind::Postcondition,
        )
        .with_result(VerificationResult::Failed {
            solver: "sunder-lib".to_string(),
            time_ms: 10,
            counterexample: None,
        });

        assert!(!ob.is_proved());
        assert!(ob.is_failed());
        assert_eq!(ob.solver_name(), "sunder-lib");
    }

    #[test]
    fn test_from_v1_results() {
        let vc = trust_types::VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "v1::div_check".to_string(),
            location: SourceSpan::default(),
            formula: trust_types::Formula::Bool(false),
            contract_metadata: None,
        };
        let result = VerificationResult::Proved {
            solver: "mock".to_string(),
            time_ms: 1,
            strength: ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: None,
        };

        let obligations = VerificationObligation::from_v1_results(vec![(vc, result)]);
        assert_eq!(obligations.len(), 1);
        assert!(obligations[0].is_proved());
        assert_eq!(obligations[0].function_name, "div_check");
        assert!(obligations[0].strategy.is_none());
    }

    #[test]
    fn test_from_mir_results() {
        let results = vec![
            (
                "test::loopy".to_string(),
                MirStrategy::BoundedModelCheck,
                VerificationResult::Proved {
                    solver: "zani-lib".to_string(),
                    time_ms: 50,
                    strength: ProofStrength::bounded(100),
                    proof_certificate: None,
                    solver_warnings: None,
                },
            ),
            (
                "test::contracted".to_string(),
                MirStrategy::ContractVerification,
                VerificationResult::Failed {
                    solver: "sunder-lib".to_string(),
                    time_ms: 30,
                    counterexample: None,
                },
            ),
        ];

        let spans = FxHashMap::default();
        let obligations = VerificationObligation::from_mir_results(results, &spans);
        assert_eq!(obligations.len(), 2);
        assert!(obligations[0].is_proved());
        assert_eq!(obligations[0].strategy, Some(MirStrategy::BoundedModelCheck));
        assert!(obligations[1].is_failed());
        assert_eq!(obligations[1].strategy, Some(MirStrategy::ContractVerification));
    }

    #[test]
    fn test_short_name() {
        assert_eq!(short_name("my_crate::my_mod::my_fn"), "my_fn");
        assert_eq!(short_name("simple"), "simple");
        assert_eq!(short_name("a::b::c::d"), "d");
    }

    #[test]
    fn test_vc_kind_for_strategy() {
        assert!(matches!(
            vc_kind_for_strategy(&MirStrategy::ContractVerification),
            VcKind::Postcondition
        ));
        assert!(matches!(
            vc_kind_for_strategy(&MirStrategy::BoundedModelCheck),
            VcKind::Assertion { .. }
        ));
        assert!(matches!(
            vc_kind_for_strategy(&MirStrategy::UnsafeAudit),
            VcKind::UnsafeOperation { .. }
        ));
        assert!(matches!(
            vc_kind_for_strategy(&MirStrategy::DataRace),
            VcKind::DataRace { .. }
        ));
        assert!(matches!(
            vc_kind_for_strategy(&MirStrategy::FFIBoundary),
            VcKind::FfiBoundaryViolation { .. }
        ));
    }
}
