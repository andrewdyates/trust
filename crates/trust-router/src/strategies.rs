// trust-router/strategies.rs: Strategy catalog for portfolio solver
//
// tRust: Defines the available verification strategies that can be combined
// in a portfolio. Each strategy wraps a solver approach with its configuration
// (timeout, depth bounds, refinement limits). The `Combined` variant enables
// composing multiple strategies into a single portfolio entry.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::sync::Arc;
use std::time::Duration;

use trust_types::{ProofStrength, VerificationCondition, VerificationResult};

use crate::VerificationBackend;

/// tRust: A verification strategy with its configuration parameters.
///
/// Each variant represents a different approach to proving or disproving
/// a verification condition. Strategies are dispatched by the portfolio
/// scheduler and can be composed via `Combined`.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub enum Strategy {
    /// Direct SMT solving (z4). Best for simple safety properties.
    DirectSmt {
        /// Per-query timeout.
        timeout: Duration,
    },
    /// CEGAR predicate abstraction + refinement. Best for loops and recursion.
    Cegar {
        /// Maximum refinement iterations before giving up.
        max_refinements: usize,
        /// Whether to fall back to IC3/PDR on stall.
        ic3_fallback: bool,
    },
    /// Bounded model checking. Best for finding counterexamples quickly.
    BoundedMc {
        /// Maximum unrolling depth.
        depth: u64,
    },
    /// Compose multiple strategies into a portfolio entry.
    Combined {
        /// Sub-strategies to run (in parallel or cascade).
        strategies: Vec<Strategy>,
    },
}

impl Strategy {
    /// Create a `DirectSmt` strategy with the given timeout in milliseconds.
    #[must_use]
    pub fn direct_smt(timeout_ms: u64) -> Self {
        Strategy::DirectSmt { timeout: Duration::from_millis(timeout_ms) }
    }

    /// Create a `Cegar` strategy with defaults.
    #[must_use]
    pub fn cegar(max_refinements: usize) -> Self {
        Strategy::Cegar { max_refinements, ic3_fallback: true }
    }

    /// Create a `BoundedMc` strategy with the given depth.
    #[must_use]
    pub fn bounded_mc(depth: u64) -> Self {
        Strategy::BoundedMc { depth }
    }

    /// Create a `Combined` strategy from a list of sub-strategies.
    #[must_use]
    pub fn combined(strategies: Vec<Strategy>) -> Self {
        Strategy::Combined { strategies }
    }

    /// Human-readable name for this strategy.
    #[must_use]
    pub fn name(&self) -> &'static str {
        match self {
            Strategy::DirectSmt { .. } => "direct-smt",
            Strategy::Cegar { .. } => "cegar",
            Strategy::BoundedMc { .. } => "bounded-mc",
            Strategy::Combined { .. } => "combined",
        }
    }

    /// The proof strength this strategy can produce on success.
    #[must_use]
    pub fn proof_strength(&self) -> ProofStrength {
        match self {
            Strategy::DirectSmt { .. } => ProofStrength::smt_unsat(),
            Strategy::Cegar { .. } => ProofStrength::inductive(),
            Strategy::BoundedMc { depth } => ProofStrength::bounded(*depth),
            Strategy::Combined { strategies } => {
                // Return the strongest proof strength among sub-strategies.
                strategies
                    .iter()
                    .map(|s| strength_rank(s.proof_strength()))
                    .max()
                    .map(rank_to_strength)
                    .unwrap_or(ProofStrength::smt_unsat())
            }
        }
    }

    /// Whether this strategy is likely suitable for the given VC.
    ///
    /// Uses the CEGAR classifier score and VC kind to make a quick
    /// suitability determination without running the solver.
    #[must_use]
    pub fn is_suitable_for(&self, vc: &VerificationCondition) -> bool {
        let classification = crate::cegar_classifier::classify(vc);
        let level = vc.kind.proof_level();

        match self {
            Strategy::DirectSmt { .. } => {
                // SMT is suitable for everything but especially good when
                // CEGAR score is low (simple formulas).
                classification.score < 40
            }
            Strategy::Cegar { .. } => {
                // CEGAR is suitable when the classifier says so.
                classification.should_use_cegar
            }
            Strategy::BoundedMc { .. } => {
                // BMC is good for safety properties and counterexample finding.
                matches!(level, trust_types::ProofLevel::L0Safety) || classification.score < 50
            }
            Strategy::Combined { strategies } => {
                // Combined is suitable if any sub-strategy is suitable.
                strategies.iter().any(|s| s.is_suitable_for(vc))
            }
        }
    }

    /// Flatten a Combined strategy into its leaf strategies.
    /// Non-Combined strategies return themselves in a single-element vec.
    #[must_use]
    pub fn flatten(&self) -> Vec<&Strategy> {
        match self {
            Strategy::Combined { strategies } => {
                strategies.iter().flat_map(|s| s.flatten()).collect()
            }
            other => vec![other],
        }
    }

    /// Count the total number of leaf strategies.
    #[must_use]
    pub fn leaf_count(&self) -> usize {
        self.flatten().len()
    }
}

/// tRust: A strategy bound to a concrete backend, ready for execution.
#[derive(Clone)]
pub struct BoundStrategy {
    /// The strategy configuration.
    pub strategy: Strategy,
    /// The backend that will execute this strategy.
    pub backend: Arc<dyn VerificationBackend>,
}

impl BoundStrategy {
    /// Create a new bound strategy.
    #[must_use]
    pub fn new(strategy: Strategy, backend: Arc<dyn VerificationBackend>) -> Self {
        Self { strategy, backend }
    }

    /// Execute this strategy on a VC.
    #[must_use]
    pub fn execute(&self, vc: &VerificationCondition) -> VerificationResult {
        self.backend.verify(vc)
    }
}

impl std::fmt::Debug for BoundStrategy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("BoundStrategy")
            .field("strategy", &self.strategy)
            .field("backend", &self.backend.name())
            .finish()
    }
}

/// tRust: Pre-built strategy catalogs for common verification scenarios.
pub struct StrategyCatalog;

impl StrategyCatalog {
    /// Default strategy set for L0 Safety properties.
    #[must_use]
    pub fn safety_default() -> Vec<Strategy> {
        vec![Strategy::direct_smt(5_000), Strategy::bounded_mc(100), Strategy::cegar(50)]
    }

    /// Default strategy set for L1 Functional properties.
    #[must_use]
    pub fn functional_default() -> Vec<Strategy> {
        vec![Strategy::cegar(100), Strategy::direct_smt(10_000), Strategy::bounded_mc(50)]
    }

    /// Default strategy set for L2 Domain properties.
    #[must_use]
    pub fn domain_default() -> Vec<Strategy> {
        vec![Strategy::cegar(200), Strategy::direct_smt(30_000)]
    }

    /// Aggressive strategy set: all strategies with high limits.
    #[must_use]
    pub fn aggressive() -> Vec<Strategy> {
        vec![Strategy::direct_smt(60_000), Strategy::cegar(500), Strategy::bounded_mc(1000)]
    }

    /// Quick strategy set: short timeouts for fast feedback.
    #[must_use]
    pub fn quick() -> Vec<Strategy> {
        vec![Strategy::direct_smt(1_000), Strategy::bounded_mc(10)]
    }

    /// Select the appropriate catalog based on proof level.
    #[must_use]
    pub fn for_level(level: trust_types::ProofLevel) -> Vec<Strategy> {
        match level {
            trust_types::ProofLevel::L0Safety => Self::safety_default(),
            trust_types::ProofLevel::L1Functional => Self::functional_default(),
            trust_types::ProofLevel::L2Domain => Self::domain_default(),
            // tRust #734: non-panicking fallback for #[non_exhaustive] forward compat
            _ => vec![],
        }
    }
}

/// Rank proof strengths for comparison (higher = stronger).
fn strength_rank(s: ProofStrength) -> u8 {
    use trust_types::ReasoningKind;
    match &s.reasoning {
        ReasoningKind::BoundedModelCheck { .. } => 1,
        ReasoningKind::Smt => 2,
        ReasoningKind::Inductive | ReasoningKind::Pdr | ReasoningKind::ChcSpacer => 3,
        ReasoningKind::Deductive => 4,
        ReasoningKind::Constructive => 5,
        _ => 2, // default to SMT-level for unknown future variants
    }
}

/// Convert a rank back to a representative proof strength.
fn rank_to_strength(rank: u8) -> ProofStrength {
    match rank {
        1 => ProofStrength::bounded(0),
        2 => ProofStrength::smt_unsat(),
        3 => ProofStrength::inductive(),
        4 => ProofStrength::deductive(),
        5 => ProofStrength::constructive(),
        _ => ProofStrength::smt_unsat(),
    }
}

#[cfg(test)]
mod tests {
    use trust_types::*;

    use super::*;

    fn test_vc(kind: VcKind) -> VerificationCondition {
        VerificationCondition {
            kind,
            function: "test".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
        }
    }

    #[test]
    fn test_strategy_constructors() {
        let smt = Strategy::direct_smt(5000);
        assert_eq!(smt.name(), "direct-smt");
        assert!(
            matches!(smt, Strategy::DirectSmt { timeout } if timeout == Duration::from_millis(5000))
        );

        let cegar = Strategy::cegar(100);
        assert_eq!(cegar.name(), "cegar");
        assert!(matches!(cegar, Strategy::Cegar { max_refinements: 100, ic3_fallback: true }));

        let bmc = Strategy::bounded_mc(50);
        assert_eq!(bmc.name(), "bounded-mc");
        assert!(matches!(bmc, Strategy::BoundedMc { depth: 50 }));
    }

    #[test]
    fn test_combined_strategy() {
        let combined = Strategy::combined(vec![Strategy::direct_smt(1000), Strategy::cegar(50)]);
        assert_eq!(combined.name(), "combined");
        assert_eq!(combined.leaf_count(), 2);
    }

    #[test]
    fn test_flatten_nested_combined() {
        let inner = Strategy::combined(vec![Strategy::direct_smt(1000), Strategy::bounded_mc(10)]);
        let outer = Strategy::combined(vec![inner, Strategy::cegar(50)]);
        assert_eq!(outer.leaf_count(), 3);

        let leaves = outer.flatten();
        assert_eq!(leaves[0].name(), "direct-smt");
        assert_eq!(leaves[1].name(), "bounded-mc");
        assert_eq!(leaves[2].name(), "cegar");
    }

    #[test]
    fn test_proof_strengths() {
        assert_eq!(Strategy::direct_smt(1000).proof_strength(), ProofStrength::smt_unsat());
        assert_eq!(Strategy::cegar(100).proof_strength(), ProofStrength::inductive());
        assert_eq!(Strategy::bounded_mc(50).proof_strength(), ProofStrength::bounded(50));
    }

    #[test]
    fn test_combined_proof_strength_picks_strongest() {
        let combined = Strategy::combined(vec![
            Strategy::direct_smt(1000), // SmtUnsat (rank 2)
            Strategy::cegar(50),        // Inductive (rank 3)
            Strategy::bounded_mc(10),   // Bounded (rank 1)
        ]);
        assert_eq!(combined.proof_strength(), ProofStrength::inductive());
    }

    #[test]
    fn test_suitability_smt_for_simple_safety() {
        let smt = Strategy::direct_smt(5000);
        let vc = test_vc(VcKind::DivisionByZero);
        assert!(smt.is_suitable_for(&vc));
    }

    #[test]
    fn test_suitability_cegar_not_for_non_termination() {
        // tRust #194: CEGAR/IC3/PDR prove safety, not termination.
        // NonTermination VCs must NOT be suitable for CEGAR.
        let cegar = Strategy::cegar(100);
        let vc = test_vc(VcKind::NonTermination {
            context: "loop".to_string(),
            measure: "n".to_string(),
        });
        assert!(!cegar.is_suitable_for(&vc), "NonTermination must NOT be suitable for CEGAR");
    }

    #[test]
    fn test_suitability_cegar_for_loop_invariant() {
        // tRust #194: CEGAR is suitable for loop-invariant assertions (safety properties).
        // Score: loop-invariant assertion (25) + loop pattern via primed var (20) = 45 > 30.
        let cegar = Strategy::cegar(100);
        let x = Formula::Var("x".into(), Sort::Int);
        let x_next = Formula::Var("x_next_step".into(), Sort::Int);
        let formula = Formula::Lt(Box::new(x_next), Box::new(x));
        let vc = VerificationCondition {
            kind: VcKind::Assertion { message: "loop invariant: counter decreases".to_string() },
            function: "test".into(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
        };
        assert!(cegar.is_suitable_for(&vc));
    }

    #[test]
    fn test_suitability_bmc_for_safety() {
        let bmc = Strategy::bounded_mc(100);
        let vc = test_vc(VcKind::DivisionByZero);
        assert!(bmc.is_suitable_for(&vc));
    }

    #[test]
    fn test_catalog_safety_default() {
        let strategies = StrategyCatalog::safety_default();
        assert_eq!(strategies.len(), 3);
        assert_eq!(strategies[0].name(), "direct-smt");
        assert_eq!(strategies[1].name(), "bounded-mc");
        assert_eq!(strategies[2].name(), "cegar");
    }

    #[test]
    fn test_catalog_functional_default() {
        let strategies = StrategyCatalog::functional_default();
        assert_eq!(strategies.len(), 3);
        assert_eq!(strategies[0].name(), "cegar");
    }

    #[test]
    fn test_catalog_for_level() {
        let l0 = StrategyCatalog::for_level(ProofLevel::L0Safety);
        assert_eq!(l0.len(), 3);

        let l1 = StrategyCatalog::for_level(ProofLevel::L1Functional);
        assert_eq!(l1.len(), 3);

        let l2 = StrategyCatalog::for_level(ProofLevel::L2Domain);
        assert_eq!(l2.len(), 2);
    }

    #[test]
    fn test_catalog_quick() {
        let strategies = StrategyCatalog::quick();
        assert_eq!(strategies.len(), 2);
    }

    #[test]
    fn test_catalog_aggressive() {
        let strategies = StrategyCatalog::aggressive();
        assert_eq!(strategies.len(), 3);
    }

    #[test]
    fn test_bound_strategy_debug() {
        let backend: Arc<dyn VerificationBackend> = Arc::new(crate::mock_backend::MockBackend);
        let bound = BoundStrategy::new(Strategy::direct_smt(1000), backend);
        let debug = format!("{:?}", bound);
        assert!(debug.contains("DirectSmt"));
        assert!(debug.contains("mock"));
    }

    #[test]
    fn test_bound_strategy_execute() {
        let backend: Arc<dyn VerificationBackend> = Arc::new(crate::mock_backend::MockBackend);
        let bound = BoundStrategy::new(Strategy::direct_smt(1000), backend);
        let vc = test_vc(VcKind::DivisionByZero);
        let result = bound.execute(&vc);
        assert!(result.is_proved());
    }
}
