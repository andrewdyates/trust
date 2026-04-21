// trust-cegar: Adaptive verification portfolio
//
// Consolidates CEGAR, CHC/Spacer, IC3/PDR, and lazy refinement into a single
// adaptive portfolio. Selects the best strategy based on VC characteristics
// (quantifier tier, logic, loop presence, complexity) and runs a fallback chain:
//
//   abstract_interp -> CEGAR -> CHC/Spacer -> IC3/PDR
//
// Inspired by z4-chc's AdaptivePortfolio which races 11 engines in parallel.
// This module provides the trust-cegar-side strategy selection and dispatch.
//
// Reference: designs/2026-03-29-dmath-function-level-integration.md S4.6
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::fmt;
use std::time::{Duration, Instant};

use serde::{Deserialize, Serialize};
use trust_types::{Formula, VcKind, VerificationCondition};

use crate::predicate_discovery::formula_variable_count;
use crate::strategy::formula_nesting_depth;

// ---------------------------------------------------------------------------
// Engine identifier
// ---------------------------------------------------------------------------

/// Identifies which verification engine produced a result.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum EngineId {
    /// Abstract interpretation pre-pass (fast, imprecise).
    AbstractInterp,
    /// CEGAR loop with predicate discovery (refinement.rs).
    Cegar,
    /// CHC/Spacer for loop invariant inference (chc_cegar.rs).
    ChcSpacer,
    /// IC3/PDR for safety properties (ic3.rs).
    Ic3Pdr,
    /// Lazy refinement along counterexample paths (lazy.rs).
    Lazy,
}

impl fmt::Display for EngineId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::AbstractInterp => write!(f, "abstract-interp"),
            Self::Cegar => write!(f, "cegar"),
            Self::ChcSpacer => write!(f, "chc-spacer"),
            Self::Ic3Pdr => write!(f, "ic3-pdr"),
            Self::Lazy => write!(f, "lazy"),
        }
    }
}

// ---------------------------------------------------------------------------
// VC classification
// ---------------------------------------------------------------------------

/// Classification of a VC's characteristics for engine selection.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VcProfile {
    /// Number of distinct variables in the formula.
    pub var_count: usize,
    /// Maximum nesting depth of the formula.
    pub nesting_depth: usize,
    /// Whether the formula contains quantifiers (Forall/Exists).
    pub has_quantifiers: bool,
    /// Whether the VC kind suggests loop-like structure.
    pub has_loop_structure: bool,
    /// Whether the VC is a safety property (reachability).
    pub is_safety: bool,
    /// Whether the VC is a liveness/temporal property.
    pub is_liveness: bool,
}

/// Analyze a VC and produce a classification profile.
#[must_use]
pub(crate) fn classify_vc(vc: &VerificationCondition) -> VcProfile {
    let var_count = formula_variable_count(&vc.formula);
    let nesting_depth = formula_nesting_depth(&vc.formula);
    let has_quantifiers = formula_has_quantifiers(&vc.formula);
    let has_loop_structure = vc_has_loop_structure(&vc.kind);
    let is_safety = vc_is_safety(&vc.kind);
    let is_liveness = vc_is_liveness(&vc.kind);

    VcProfile {
        var_count,
        nesting_depth,
        has_quantifiers,
        has_loop_structure,
        is_safety,
        is_liveness,
    }
}

/// Check whether a formula contains quantifiers using iterative DFS.
fn formula_has_quantifiers(formula: &Formula) -> bool {
    let mut stack = vec![formula];
    while let Some(f) = stack.pop() {
        match f {
            Formula::Forall(..) | Formula::Exists(..) => return true,
            // Unary.
            Formula::Not(a) | Formula::Neg(a) => stack.push(a),
            Formula::BvNot(a, _) | Formula::BvToInt(a, _, _) | Formula::IntToBv(a, _)
            | Formula::BvZeroExt(a, _) | Formula::BvSignExt(a, _) => stack.push(a),
            Formula::BvExtract { inner, .. } => stack.push(inner),
            // Binary.
            Formula::Implies(a, b) | Formula::Eq(a, b) | Formula::Lt(a, b)
            | Formula::Le(a, b) | Formula::Gt(a, b) | Formula::Ge(a, b)
            | Formula::Add(a, b) | Formula::Sub(a, b) | Formula::Mul(a, b)
            | Formula::Div(a, b) | Formula::Rem(a, b) | Formula::Select(a, b) => {
                stack.push(a);
                stack.push(b);
            }
            Formula::BvAdd(a, b, _) | Formula::BvSub(a, b, _) | Formula::BvMul(a, b, _)
            | Formula::BvUDiv(a, b, _) | Formula::BvSDiv(a, b, _)
            | Formula::BvURem(a, b, _) | Formula::BvSRem(a, b, _)
            | Formula::BvAnd(a, b, _) | Formula::BvOr(a, b, _)
            | Formula::BvXor(a, b, _) | Formula::BvShl(a, b, _)
            | Formula::BvLShr(a, b, _) | Formula::BvAShr(a, b, _)
            | Formula::BvULt(a, b, _) | Formula::BvULe(a, b, _)
            | Formula::BvSLt(a, b, _) | Formula::BvSLe(a, b, _)
            | Formula::BvConcat(a, b) => {
                stack.push(a);
                stack.push(b);
            }
            // N-ary.
            Formula::And(cs) | Formula::Or(cs) => stack.extend(cs),
            // Ternary.
            Formula::Ite(a, b, c) | Formula::Store(a, b, c) => {
                stack.push(a);
                stack.push(b);
                stack.push(c);
            }
            // Leaves.
            Formula::Bool(_) | Formula::Int(_) | Formula::UInt(_)
            | Formula::BitVec { .. } | Formula::Var(..) => {}
            _ => {},
        }
    }
    false
}

/// Check if a VcKind suggests loop structure (invariant synthesis needed).
fn vc_has_loop_structure(kind: &VcKind) -> bool {
    matches!(
        kind,
        VcKind::NonTermination { .. }
            | VcKind::Temporal { .. }
            | VcKind::Liveness { .. }
            | VcKind::Fairness { .. }
    )
}

/// Check if a VcKind is a safety property (suitable for IC3/PDR).
fn vc_is_safety(kind: &VcKind) -> bool {
    matches!(
        kind,
        VcKind::ArithmeticOverflow { .. }
            | VcKind::ShiftOverflow { .. }
            | VcKind::DivisionByZero
            | VcKind::RemainderByZero
            | VcKind::IndexOutOfBounds
            | VcKind::SliceBoundsCheck
            | VcKind::Assertion { .. }
            | VcKind::Precondition { .. }
            | VcKind::Postcondition
            | VcKind::CastOverflow { .. }
            | VcKind::NegationOverflow { .. }
            | VcKind::Unreachable
            | VcKind::DeadState { .. }
            | VcKind::Deadlock
    )
}

/// Check if a VcKind is a liveness/temporal property.
fn vc_is_liveness(kind: &VcKind) -> bool {
    matches!(
        kind,
        VcKind::Temporal { .. }
            | VcKind::Liveness { .. }
            | VcKind::Fairness { .. }
            | VcKind::NonTermination { .. }
    )
}

// ---------------------------------------------------------------------------
// Portfolio configuration
// ---------------------------------------------------------------------------

/// Configuration for the adaptive portfolio.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PortfolioConfig {
    /// Total timeout for the entire portfolio run.
    #[serde(with = "crate::strategy::duration_millis")]
    pub total_timeout: Duration,
    /// Per-engine timeout as a fraction of the remaining total time.
    /// E.g., 0.4 means each engine gets at most 40% of remaining time.
    pub per_engine_time_fraction: f64,
    /// Minimum per-engine timeout (floor).
    #[serde(with = "crate::strategy::duration_millis")]
    pub min_engine_timeout: Duration,
    /// Maximum CEGAR iterations when the CEGAR engine is selected.
    pub max_cegar_iterations: usize,
    /// Maximum IC3 frame depth.
    pub max_ic3_depth: usize,
    /// Complexity threshold: VCs with var_count below this use simpler engines.
    pub simple_vc_threshold: usize,
}

impl Default for PortfolioConfig {
    fn default() -> Self {
        Self {
            total_timeout: Duration::from_secs(120),
            per_engine_time_fraction: 0.4,
            min_engine_timeout: Duration::from_secs(5),
            max_cegar_iterations: 100,
            max_ic3_depth: 50,
            simple_vc_threshold: 20,
        }
    }
}

// ---------------------------------------------------------------------------
// Portfolio outcome
// ---------------------------------------------------------------------------

/// Outcome of a portfolio verification run.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum PortfolioOutcome {
    /// Property verified safe by the named engine.
    Safe {
        /// Which engine proved safety.
        engine: EngineId,
        /// Time taken by the successful engine.
        elapsed: Duration,
    },
    /// Property is unsafe; a real counterexample exists.
    Unsafe {
        /// Which engine found the counterexample.
        engine: EngineId,
        /// Time taken.
        elapsed: Duration,
    },
    /// No engine could determine the result within the budget.
    Unknown {
        /// Engines that were attempted and their individual outcomes.
        attempts: Vec<EngineAttempt>,
        /// Total time spent.
        total_elapsed: Duration,
    },
}

/// Record of a single engine attempt within the portfolio.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EngineAttempt {
    /// Which engine was tried.
    pub engine: EngineId,
    /// What happened.
    pub outcome: AttemptOutcome,
    /// Time consumed by this attempt.
    pub elapsed: Duration,
}

/// Outcome of an individual engine attempt.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum AttemptOutcome {
    /// Engine proved safety.
    Safe,
    /// Engine found a counterexample.
    Unsafe,
    /// Engine timed out.
    Timeout,
    /// Engine encountered an error.
    Error { detail: String },
    /// Engine returned unknown / inconclusive.
    Unknown,
}

// ---------------------------------------------------------------------------
// Adaptive portfolio
// ---------------------------------------------------------------------------

/// Adaptive verification portfolio: classifies a VC, selects an ordered engine
/// chain, and runs each engine with a timeout budget. First definitive result
/// (Safe/Unsafe) wins. Liveness skips IC3/PDR; loops prefer CHC/Spacer first.
pub struct AdaptivePortfolio {
    /// The verification condition being checked.
    vc: VerificationCondition,
    /// Configuration.
    config: PortfolioConfig,
    /// Classified VC profile.
    profile: VcProfile,
}

impl AdaptivePortfolio {
    /// Create a new adaptive portfolio for the given VC.
    #[must_use]
    pub fn new(vc: VerificationCondition, config: PortfolioConfig) -> Self {
        let profile = classify_vc(&vc);
        Self { vc, config, profile }
    }

    /// Create with default configuration.
    #[must_use]
    pub fn with_defaults(vc: VerificationCondition) -> Self {
        Self::new(vc, PortfolioConfig::default())
    }

    /// Return the ordered engine chain for this VC's profile.
    #[must_use]
    pub fn engine_chain(&self) -> Vec<EngineId> {
        select_engine_chain(&self.profile, &self.config)
    }

    /// Access the VC profile.
    #[must_use]
    pub fn profile(&self) -> &VcProfile {
        &self.profile
    }

    /// Access the VC.
    #[must_use]
    pub fn vc(&self) -> &VerificationCondition {
        &self.vc
    }

    /// Run the portfolio, trying each engine with per-engine timeout budgets.
    /// First definitive result (Safe/Unsafe) short-circuits the chain.
    pub fn run(&self) -> PortfolioOutcome {
        let start = Instant::now();
        let chain = self.engine_chain();
        let mut attempts = Vec::with_capacity(chain.len());

        for engine in &chain {
            let remaining = self
                .config
                .total_timeout
                .checked_sub(start.elapsed())
                .unwrap_or(Duration::ZERO);

            if remaining.is_zero() {
                break;
            }

            let budget = compute_engine_budget(remaining, &self.config);
            let engine_start = Instant::now();
            let outcome = self.run_engine(*engine, budget);
            let engine_elapsed = engine_start.elapsed();

            match &outcome {
                AttemptOutcome::Safe => {
                    return PortfolioOutcome::Safe {
                        engine: *engine,
                        elapsed: engine_elapsed,
                    };
                }
                AttemptOutcome::Unsafe => {
                    return PortfolioOutcome::Unsafe {
                        engine: *engine,
                        elapsed: engine_elapsed,
                    };
                }
                _ => {
                    attempts.push(EngineAttempt {
                        engine: *engine,
                        outcome,
                        elapsed: engine_elapsed,
                    });
                }
            }
        }

        PortfolioOutcome::Unknown {
            attempts,
            total_elapsed: start.elapsed(),
        }
    }

    /// Run a single engine with the given timeout budget.
    ///
    /// Each engine stub checks the VC and returns a quick classification
    /// result. Full solver integration connects through the existing module
    /// APIs (CegarLoop, Ic3Engine, etc.).
    fn run_engine(&self, engine: EngineId, _budget: Duration) -> AttemptOutcome {
        match engine {
            EngineId::AbstractInterp => self.run_abstract_interp(),
            EngineId::Cegar => self.run_cegar(),
            EngineId::Lazy => self.run_lazy(),
            EngineId::ChcSpacer => self.run_chc_spacer(),
            EngineId::Ic3Pdr => self.run_ic3_pdr(),
        }
    }

    /// Abstract interpretation pre-pass: catch trivially true/false formulas.
    fn run_abstract_interp(&self) -> AttemptOutcome {
        match &self.vc.formula {
            Formula::Bool(true) => AttemptOutcome::Safe,
            Formula::Bool(false) => AttemptOutcome::Unsafe,
            _ => {
                // Simple constant propagation: if the formula is a tautology
                // at the top level (e.g., x >= x), we can sometimes tell.
                if is_trivial_tautology(&self.vc.formula) {
                    AttemptOutcome::Safe
                } else {
                    AttemptOutcome::Unknown
                }
            }
        }
    }

    /// CEGAR engine stub: full predicate-refinement loop.
    fn run_cegar(&self) -> AttemptOutcome {
        // The actual CEGAR loop lives in refinement.rs (CegarLoop).
        // This stub represents the portfolio's dispatch point.
        // In production, this would create a CegarLoop, run iterations,
        // and translate CegarOutcome to AttemptOutcome.
        AttemptOutcome::Unknown
    }

    /// Lazy refinement engine stub.
    fn run_lazy(&self) -> AttemptOutcome {
        // Dispatches to lazy.rs (LazyRefiner).
        AttemptOutcome::Unknown
    }

    /// CHC/Spacer engine stub: loop invariant inference.
    fn run_chc_spacer(&self) -> AttemptOutcome {
        // Dispatches to chc_cegar.rs (refine_with_chc).
        AttemptOutcome::Unknown
    }

    /// IC3/PDR engine stub: safety property checking.
    fn run_ic3_pdr(&self) -> AttemptOutcome {
        // Dispatches to ic3.rs (Ic3Engine).
        // Only valid for safety properties.
        if !self.profile.is_safety {
            return AttemptOutcome::Error {
                detail: "IC3/PDR only handles safety properties".into(),
            };
        }
        AttemptOutcome::Unknown
    }
}

// ---------------------------------------------------------------------------
// Engine selection logic
// ---------------------------------------------------------------------------

/// Select the ordered engine chain based on the VC profile.
///
/// The chain determines which engines to try and in what order. The first
/// engine to return Safe/Unsafe wins.
#[must_use]
pub(crate) fn select_engine_chain(
    profile: &VcProfile,
    config: &PortfolioConfig,
) -> Vec<EngineId> {
    let mut chain = Vec::with_capacity(4);

    // 1. Always start with abstract interpretation (cheap pre-pass).
    chain.push(EngineId::AbstractInterp);

    // 2. Select primary engine based on VC characteristics.
    if profile.is_liveness {
        // Liveness properties: CHC/Spacer is the primary engine.
        // IC3/PDR cannot handle liveness. CEGAR is a fallback.
        chain.push(EngineId::ChcSpacer);
        chain.push(EngineId::Cegar);
    } else if profile.has_loop_structure || profile.has_quantifiers {
        // Loops or quantifiers: CHC/Spacer first (invariant synthesis),
        // then CEGAR for refinement, then IC3 for safety.
        chain.push(EngineId::ChcSpacer);
        chain.push(EngineId::Cegar);
        if profile.is_safety {
            chain.push(EngineId::Ic3Pdr);
        }
    } else if profile.var_count <= config.simple_vc_threshold
        && profile.nesting_depth <= 5
    {
        // Simple VCs: lazy refinement is fast and sufficient.
        chain.push(EngineId::Lazy);
        chain.push(EngineId::Cegar);
        if profile.is_safety {
            chain.push(EngineId::Ic3Pdr);
        }
    } else {
        // Medium/complex VCs: full CEGAR, then CHC, then IC3.
        chain.push(EngineId::Cegar);
        chain.push(EngineId::ChcSpacer);
        if profile.is_safety {
            chain.push(EngineId::Ic3Pdr);
        }
    }

    chain
}

/// Compute the timeout budget for the next engine given the remaining time.
fn compute_engine_budget(remaining: Duration, config: &PortfolioConfig) -> Duration {
    let fraction_budget = remaining.mul_f64(config.per_engine_time_fraction);
    fraction_budget.max(config.min_engine_timeout).min(remaining)
}

// ---------------------------------------------------------------------------
// Trivial formula detection
// ---------------------------------------------------------------------------

/// Check if a formula is a trivial tautology that abstract interpretation
/// can resolve without a full solver.
fn is_trivial_tautology(formula: &Formula) -> bool {
    match formula {
        Formula::Bool(true) => true,
        // x >= x, x <= x, x == x patterns.
        Formula::Ge(a, b) | Formula::Le(a, b) | Formula::Eq(a, b) => a == b,
        // not(false) = true.
        Formula::Not(inner) => matches!(inner.as_ref(), Formula::Bool(false)),
        // AND of tautologies.
        Formula::And(children) => children.iter().all(is_trivial_tautology),
        // Implies(false, _) = true, Implies(_, true) = true.
        Formula::Implies(a, b) => {
            matches!(a.as_ref(), Formula::Bool(false))
                || matches!(b.as_ref(), Formula::Bool(true))
        }
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use trust_types::{LivenessProperty, Sort, SourceSpan, TemporalOperator};

    use super::*;

    fn make_vc(kind: VcKind, formula: Formula) -> VerificationCondition {
        VerificationCondition {
            kind,
            function: "test_fn".into(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
        }
    }

    fn simple_formula() -> Formula {
        Formula::Ge(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        )
    }

    fn quantified_formula() -> Formula {
        Formula::Forall(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::Ge(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            )),
        )
    }

    fn medium_formula() -> Formula {
        let mut conjuncts = Vec::new();
        for i in 0..25 {
            conjuncts.push(Formula::Lt(
                Box::new(Formula::Var(format!("v{i}"), Sort::Int)),
                Box::new(Formula::Var(format!("v{}", i + 1), Sort::Int)),
            ));
        }
        Formula::And(conjuncts)
    }

    // -- classify_vc tests --

    #[test]
    fn test_classify_simple_safety() {
        let vc = make_vc(VcKind::DivisionByZero, simple_formula());
        let profile = classify_vc(&vc);
        assert_eq!(profile.var_count, 1);
        assert!(!profile.has_quantifiers);
        assert!(!profile.has_loop_structure);
        assert!(profile.is_safety);
        assert!(!profile.is_liveness);
    }

    #[test]
    fn test_classify_quantified() {
        let vc = make_vc(VcKind::Postcondition, quantified_formula());
        let profile = classify_vc(&vc);
        assert!(profile.has_quantifiers);
    }

    #[test]
    fn test_classify_liveness() {
        let vc = make_vc(
            VcKind::Liveness {
                property: LivenessProperty {
                    name: "termination".into(),
                    operator: TemporalOperator::Eventually,
                    predicate: "done".into(),
                    consequent: None,
                    fairness: vec![],
                },
            },
            simple_formula(),
        );
        let profile = classify_vc(&vc);
        assert!(profile.is_liveness);
        assert!(profile.has_loop_structure);
        assert!(!profile.is_safety);
    }

    #[test]
    fn test_classify_non_termination() {
        let vc = make_vc(
            VcKind::NonTermination {
                context: "loop".into(),
                measure: "n".into(),
            },
            simple_formula(),
        );
        let profile = classify_vc(&vc);
        assert!(profile.has_loop_structure);
        assert!(profile.is_liveness);
    }

    // -- engine chain tests --

    #[test]
    fn test_chain_simple_safety() {
        let vc = make_vc(VcKind::DivisionByZero, simple_formula());
        let portfolio = AdaptivePortfolio::with_defaults(vc);
        let chain = portfolio.engine_chain();
        // Simple + safety -> AbstractInterp, Lazy, Cegar, Ic3Pdr
        assert_eq!(chain[0], EngineId::AbstractInterp);
        assert_eq!(chain[1], EngineId::Lazy);
        assert_eq!(chain[2], EngineId::Cegar);
        assert_eq!(chain[3], EngineId::Ic3Pdr);
    }

    #[test]
    fn test_chain_liveness_no_ic3() {
        let vc = make_vc(
            VcKind::Liveness {
                property: LivenessProperty {
                    name: "term".into(),
                    operator: TemporalOperator::Eventually,
                    predicate: "done".into(),
                    consequent: None,
                    fairness: vec![],
                },
            },
            simple_formula(),
        );
        let portfolio = AdaptivePortfolio::with_defaults(vc);
        let chain = portfolio.engine_chain();
        // Liveness -> no IC3/PDR
        assert_eq!(chain[0], EngineId::AbstractInterp);
        assert_eq!(chain[1], EngineId::ChcSpacer);
        assert_eq!(chain[2], EngineId::Cegar);
        assert!(!chain.contains(&EngineId::Ic3Pdr));
    }

    #[test]
    fn test_chain_quantified_safety() {
        let vc = make_vc(VcKind::Postcondition, quantified_formula());
        let portfolio = AdaptivePortfolio::with_defaults(vc);
        let chain = portfolio.engine_chain();
        // Quantified -> ChcSpacer first, then Cegar, then Ic3 (safety)
        assert_eq!(chain[0], EngineId::AbstractInterp);
        assert_eq!(chain[1], EngineId::ChcSpacer);
        assert_eq!(chain[2], EngineId::Cegar);
        assert!(chain.contains(&EngineId::Ic3Pdr));
    }

    #[test]
    fn test_chain_medium_complexity() {
        let vc = make_vc(VcKind::Postcondition, medium_formula());
        let portfolio = AdaptivePortfolio::with_defaults(vc);
        let chain = portfolio.engine_chain();
        // Medium complexity, safety -> Cegar, ChcSpacer, Ic3Pdr
        assert_eq!(chain[0], EngineId::AbstractInterp);
        assert_eq!(chain[1], EngineId::Cegar);
        assert_eq!(chain[2], EngineId::ChcSpacer);
        assert!(chain.contains(&EngineId::Ic3Pdr));
    }

    // -- portfolio run tests --

    #[test]
    fn test_portfolio_trivially_safe() {
        let vc = make_vc(VcKind::Postcondition, Formula::Bool(true));
        let portfolio = AdaptivePortfolio::with_defaults(vc);
        let result = portfolio.run();
        match result {
            PortfolioOutcome::Safe { engine, .. } => {
                assert_eq!(engine, EngineId::AbstractInterp);
            }
            other => panic!("expected Safe, got: {other:?}"),
        }
    }

    #[test]
    fn test_portfolio_trivially_unsafe() {
        let vc = make_vc(VcKind::Postcondition, Formula::Bool(false));
        let portfolio = AdaptivePortfolio::with_defaults(vc);
        let result = portfolio.run();
        match result {
            PortfolioOutcome::Unsafe { engine, .. } => {
                assert_eq!(engine, EngineId::AbstractInterp);
            }
            other => panic!("expected Unsafe, got: {other:?}"),
        }
    }

    #[test]
    fn test_portfolio_tautology_eq_self() {
        // x == x is a tautology
        let f = Formula::Eq(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Var("x".into(), Sort::Int)),
        );
        let vc = make_vc(VcKind::Postcondition, f);
        let portfolio = AdaptivePortfolio::with_defaults(vc);
        let result = portfolio.run();
        match result {
            PortfolioOutcome::Safe { engine, .. } => {
                assert_eq!(engine, EngineId::AbstractInterp);
            }
            other => panic!("expected Safe from tautology, got: {other:?}"),
        }
    }

    #[test]
    fn test_portfolio_unknown_fallthrough() {
        // A non-trivial formula: all engine stubs return Unknown.
        let vc = make_vc(VcKind::DivisionByZero, simple_formula());
        let config = PortfolioConfig {
            total_timeout: Duration::from_secs(1),
            ..PortfolioConfig::default()
        };
        let portfolio = AdaptivePortfolio::new(vc, config);
        let result = portfolio.run();
        match result {
            PortfolioOutcome::Unknown { attempts, .. } => {
                // Should have attempted all engines in the chain.
                assert!(!attempts.is_empty());
                // First attempt is AbstractInterp (returned Unknown since
                // simple_formula() is not trivially true/false).
                assert_eq!(attempts[0].engine, EngineId::AbstractInterp);
            }
            other => panic!("expected Unknown, got: {other:?}"),
        }
    }

    // -- trivial tautology tests --

    #[test]
    fn test_trivial_tautology_bool() {
        assert!(is_trivial_tautology(&Formula::Bool(true)));
        assert!(!is_trivial_tautology(&Formula::Bool(false)));
    }

    #[test]
    fn test_trivial_tautology_eq_self() {
        let f = Formula::Eq(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Var("x".into(), Sort::Int)),
        );
        assert!(is_trivial_tautology(&f));
    }

    #[test]
    fn test_trivial_tautology_and_of_tautologies() {
        let f = Formula::And(vec![
            Formula::Bool(true),
            Formula::Ge(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Var("x".into(), Sort::Int)),
            ),
        ]);
        assert!(is_trivial_tautology(&f));
    }

    #[test]
    fn test_trivial_tautology_implies_false() {
        let f = Formula::Implies(
            Box::new(Formula::Bool(false)),
            Box::new(Formula::Var("x".into(), Sort::Int)),
        );
        assert!(is_trivial_tautology(&f));
    }

    #[test]
    fn test_not_trivial_tautology() {
        assert!(!is_trivial_tautology(&simple_formula()));
    }

    // -- engine budget tests --

    #[test]
    fn test_compute_engine_budget_normal() {
        let config = PortfolioConfig::default();
        let remaining = Duration::from_secs(100);
        let budget = compute_engine_budget(remaining, &config);
        // 40% of 100s = 40s, which is > min_engine_timeout (5s)
        assert_eq!(budget, Duration::from_secs(40));
    }

    #[test]
    fn test_compute_engine_budget_floor() {
        let config = PortfolioConfig {
            min_engine_timeout: Duration::from_secs(10),
            per_engine_time_fraction: 0.01,
            ..PortfolioConfig::default()
        };
        let remaining = Duration::from_secs(100);
        let budget = compute_engine_budget(remaining, &config);
        // 1% of 100s = 1s, but floor is 10s
        assert_eq!(budget, Duration::from_secs(10));
    }

    #[test]
    fn test_compute_engine_budget_cap_at_remaining() {
        let config = PortfolioConfig {
            min_engine_timeout: Duration::from_secs(30),
            per_engine_time_fraction: 0.5,
            ..PortfolioConfig::default()
        };
        let remaining = Duration::from_secs(10);
        let budget = compute_engine_budget(remaining, &config);
        // max(0.5 * 10, 30) = 30, but capped at remaining = 10
        assert_eq!(budget, Duration::from_secs(10));
    }

    // -- formula_has_quantifiers tests --

    #[test]
    fn test_has_quantifiers_forall() {
        assert!(formula_has_quantifiers(&quantified_formula()));
    }

    #[test]
    fn test_has_quantifiers_none() {
        assert!(!formula_has_quantifiers(&simple_formula()));
    }

    #[test]
    fn test_has_quantifiers_nested() {
        let f = Formula::And(vec![
            simple_formula(),
            Formula::Exists(
                vec![("y".into(), Sort::Int)],
                Box::new(Formula::Bool(true)),
            ),
        ]);
        assert!(formula_has_quantifiers(&f));
    }

    // -- EngineId display --

    #[test]
    fn test_engine_id_display() {
        assert_eq!(format!("{}", EngineId::AbstractInterp), "abstract-interp");
        assert_eq!(format!("{}", EngineId::Cegar), "cegar");
        assert_eq!(format!("{}", EngineId::ChcSpacer), "chc-spacer");
        assert_eq!(format!("{}", EngineId::Ic3Pdr), "ic3-pdr");
        assert_eq!(format!("{}", EngineId::Lazy), "lazy");
    }

    // -- PortfolioConfig serde --

    #[test]
    fn test_portfolio_config_serde_roundtrip() {
        let config = PortfolioConfig::default();
        let json = serde_json::to_string(&config).expect("serialize");
        let deserialized: PortfolioConfig =
            serde_json::from_str(&json).expect("deserialize");
        assert_eq!(deserialized.total_timeout, config.total_timeout);
        assert_eq!(deserialized.max_cegar_iterations, config.max_cegar_iterations);
    }

    // -- IC3/PDR rejects liveness --

    #[test]
    fn test_ic3_rejects_liveness() {
        let vc = make_vc(
            VcKind::Liveness {
                property: LivenessProperty {
                    name: "term".into(),
                    operator: TemporalOperator::Eventually,
                    predicate: "done".into(),
                    consequent: None,
                    fairness: vec![],
                },
            },
            simple_formula(),
        );
        let portfolio = AdaptivePortfolio::with_defaults(vc);
        let outcome = portfolio.run_ic3_pdr();
        assert!(matches!(outcome, AttemptOutcome::Error { .. }));
    }
}
