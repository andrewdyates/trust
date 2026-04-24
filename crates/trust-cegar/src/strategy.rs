// trust-cegar: Refinement strategy selection for CEGAR
//
// Automatic selection of refinement strategies based on VC complexity.
// Supports eager, lazy, interpolation-based, and mixed strategies with
// configurable thresholds.
//
// Reference: CPAchecker's configurable refinement strategies
//   refs/cpachecker/src/org/sosy_lab/cpachecker/core/algorithm/CEGARAlgorithm.java
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::time::Duration;

use serde::{Deserialize, Serialize};
use trust_types::{Formula, VcKind, VerificationCondition};

use crate::predicate_discovery::formula_variable_count;

/// Refinement strategy for the CEGAR loop.
///
/// Each strategy trades off precision vs. performance:
/// - Eager: re-abstracts the entire program on each refinement.
/// - Lazy: only refines along the counterexample path.
/// - Interpolation: uses Craig interpolation for targeted predicate discovery.
/// - Mixed: starts lazy, switches to interpolation when lazy stalls.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum RefinementStrategy {
    /// Eager refinement: re-abstract everything after each counterexample.
    ///
    /// Most precise but most expensive. Good for small programs or when
    /// precision is critical.
    Eager,

    /// Lazy refinement: only refine along the counterexample path.
    ///
    /// CPAchecker's default. Cheapest per iteration but may require more
    /// iterations to converge.
    Lazy,

    /// Interpolation-based refinement: use Craig interpolation from
    /// unsat cores to discover predicates.
    ///
    /// Most targeted predicate discovery. Requires SMT solver support
    /// for unsat core extraction (z4).
    Interpolation,

    /// Mixed strategy: start with lazy refinement, switch to interpolation
    /// after a configurable number of stalled iterations.
    ///
    /// Best default: fast start, precise recovery when stalling.
    Mixed,
}

impl std::fmt::Display for RefinementStrategy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Eager => write!(f, "eager"),
            Self::Lazy => write!(f, "lazy"),
            Self::Interpolation => write!(f, "interpolation"),
            Self::Mixed => write!(f, "mixed"),
        }
    }
}

/// Configuration for refinement strategy behavior.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StrategyConfig {
    /// Maximum number of tracked predicates before pruning.
    pub max_predicates: usize,
    /// Maximum refinement iterations before giving up.
    pub max_refinements: usize,
    /// Timeout for the entire CEGAR loop.
    #[serde(with = "duration_millis")]
    pub timeout: Duration,
    /// For Mixed strategy: switch from lazy to interpolation after this
    /// many iterations without progress (new predicates that eliminate
    /// counterexamples).
    pub stall_threshold: usize,
    /// Complexity threshold (variable count) for choosing eager vs. lazy.
    pub eager_complexity_threshold: usize,
}

impl Default for StrategyConfig {
    fn default() -> Self {
        Self {
            max_predicates: 500,
            max_refinements: 100,
            timeout: Duration::from_secs(60),
            stall_threshold: 5,
            eager_complexity_threshold: 20,
        }
    }
}

/// Select a refinement strategy based on VC complexity.
///
/// Heuristics:
/// 1. Simple VCs (few variables, no loops) -> Eager.
/// 2. Medium VCs with loop-like patterns -> Lazy.
/// 3. Complex VCs or temporal properties -> Interpolation.
/// 4. Default for uncertain complexity -> Mixed.
///
/// # Arguments
/// * `vc` - The verification condition to analyze.
///
/// # Returns
/// The recommended refinement strategy.
#[must_use]
pub fn select_strategy(vc: &VerificationCondition) -> RefinementStrategy {
    select_strategy_with_config(vc, &StrategyConfig::default())
}

/// Select a refinement strategy with custom configuration.
#[must_use]
pub fn select_strategy_with_config(
    vc: &VerificationCondition,
    config: &StrategyConfig,
) -> RefinementStrategy {
    let var_count = formula_variable_count(&vc.formula);
    let formula_depth = formula_nesting_depth(&vc.formula);

    // Check the VC kind for domain-specific hints.
    match &vc.kind {
        // Temporal/liveness properties are complex: use interpolation.
        VcKind::Temporal { .. }
        | VcKind::Liveness { .. }
        | VcKind::Fairness { .. }
        | VcKind::NonTermination { .. } => {
            return RefinementStrategy::Interpolation;
        }
        // Simple arithmetic checks: eager if small, lazy otherwise.
        VcKind::ArithmeticOverflow { .. }
        | VcKind::DivisionByZero
        | VcKind::RemainderByZero
        | VcKind::NegationOverflow { .. } => {
            if var_count <= config.eager_complexity_threshold {
                return RefinementStrategy::Eager;
            }
            return RefinementStrategy::Lazy;
        }
        _ => {}
    }

    // General complexity-based selection.
    if var_count <= config.eager_complexity_threshold && formula_depth <= 5 {
        // Small, shallow formulas: eager is affordable and precise.
        RefinementStrategy::Eager
    } else if var_count > config.eager_complexity_threshold * 3 || formula_depth > 15 {
        // Very complex formulas: interpolation for targeted refinement.
        RefinementStrategy::Interpolation
    } else {
        // Medium complexity: mixed strategy for best trade-off.
        RefinementStrategy::Mixed
    }
}

/// Estimate the formula nesting depth (proxy for structural complexity).
#[must_use]
pub fn formula_nesting_depth(formula: &Formula) -> usize {
    match formula {
        // Leaves.
        Formula::Bool(_)
        | Formula::Int(_)
        | Formula::UInt(_)
        | Formula::BitVec { .. }
        | Formula::Var(_, _) => 0,
        // Unary.
        Formula::Not(inner) | Formula::Neg(inner) => 1 + formula_nesting_depth(inner),
        // Binary.
        Formula::Implies(a, b)
        | Formula::Eq(a, b)
        | Formula::Lt(a, b)
        | Formula::Le(a, b)
        | Formula::Gt(a, b)
        | Formula::Ge(a, b)
        | Formula::Add(a, b)
        | Formula::Sub(a, b)
        | Formula::Mul(a, b)
        | Formula::Div(a, b)
        | Formula::Rem(a, b)
        | Formula::Select(a, b) => 1 + formula_nesting_depth(a).max(formula_nesting_depth(b)),
        // N-ary.
        Formula::And(children) | Formula::Or(children) => {
            1 + children.iter().map(formula_nesting_depth).max().unwrap_or(0)
        }
        // Ternary.
        Formula::Ite(c, t, e) | Formula::Store(c, t, e) => {
            1 + formula_nesting_depth(c).max(formula_nesting_depth(t)).max(formula_nesting_depth(e))
        }
        // Quantifiers.
        Formula::Forall(_, body) | Formula::Exists(_, body) => {
            2 + formula_nesting_depth(body) // Quantifiers add extra depth.
        }
        // Bitvector operations: treat as binary depth.
        Formula::BvAdd(a, b, _)
        | Formula::BvSub(a, b, _)
        | Formula::BvMul(a, b, _)
        | Formula::BvUDiv(a, b, _)
        | Formula::BvSDiv(a, b, _)
        | Formula::BvURem(a, b, _)
        | Formula::BvSRem(a, b, _)
        | Formula::BvAnd(a, b, _)
        | Formula::BvOr(a, b, _)
        | Formula::BvXor(a, b, _)
        | Formula::BvShl(a, b, _)
        | Formula::BvLShr(a, b, _)
        | Formula::BvAShr(a, b, _)
        | Formula::BvULt(a, b, _)
        | Formula::BvULe(a, b, _)
        | Formula::BvSLt(a, b, _)
        | Formula::BvSLe(a, b, _)
        | Formula::BvConcat(a, b) => 1 + formula_nesting_depth(a).max(formula_nesting_depth(b)),
        Formula::BvNot(inner, _)
        | Formula::BvToInt(inner, _, _)
        | Formula::IntToBv(inner, _)
        | Formula::BvZeroExt(inner, _)
        | Formula::BvSignExt(inner, _) => 1 + formula_nesting_depth(inner),
        Formula::BvExtract { inner, .. } => 1 + formula_nesting_depth(inner),
        _ => 0,
    }
}

/// Serde helper for Duration as milliseconds.
pub(crate) mod duration_millis {
    use std::time::Duration;

    use serde::{self, Deserialize, Deserializer, Serializer};

    pub(crate) fn serialize<S>(duration: &Duration, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_u64(duration.as_millis() as u64)
    }

    pub(crate) fn deserialize<'de, D>(deserializer: D) -> Result<Duration, D::Error>
    where
        D: Deserializer<'de>,
    {
        let millis = u64::deserialize(deserializer)?;
        Ok(Duration::from_millis(millis))
    }
}

#[cfg(test)]
mod tests {
    use trust_types::{BinOp, Sort, SourceSpan, TemporalOperator, Ty};

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
        // x >= 0 -- 1 variable, depth 1
        Formula::Ge(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(0)))
    }

    fn medium_formula() -> Formula {
        // (a < b) AND (b < c) AND ... with ~25 variables
        let mut conjuncts = Vec::new();
        for i in 0..25 {
            conjuncts.push(Formula::Lt(
                Box::new(Formula::Var(format!("v{i}"), Sort::Int)),
                Box::new(Formula::Var(format!("v{}", i + 1), Sort::Int)),
            ));
        }
        Formula::And(conjuncts)
    }

    fn complex_formula() -> Formula {
        // Deep nested formula with >60 variables
        let mut conjuncts = Vec::new();
        for i in 0..65 {
            conjuncts.push(Formula::Lt(
                Box::new(Formula::Var(format!("x{i}"), Sort::Int)),
                Box::new(Formula::Var(format!("y{i}"), Sort::Int)),
            ));
        }
        // Add nesting.
        let inner = Formula::And(conjuncts);
        Formula::Implies(
            Box::new(inner.clone()),
            Box::new(Formula::And(vec![
                inner,
                Formula::Ge(
                    Box::new(Formula::Var("z".into(), Sort::Int)),
                    Box::new(Formula::Int(0)),
                ),
            ])),
        )
    }

    #[test]
    fn test_select_strategy_simple_arithmetic() {
        let vc = make_vc(VcKind::DivisionByZero, simple_formula());
        assert_eq!(select_strategy(&vc), RefinementStrategy::Eager);
    }

    #[test]
    fn test_select_strategy_temporal() {
        let vc = make_vc(VcKind::Temporal { property: "always_safe".into() }, simple_formula());
        assert_eq!(select_strategy(&vc), RefinementStrategy::Interpolation);
    }

    #[test]
    fn test_select_strategy_medium_general() {
        let vc = make_vc(VcKind::Postcondition, medium_formula());
        let strategy = select_strategy(&vc);
        assert_eq!(strategy, RefinementStrategy::Mixed);
    }

    #[test]
    fn test_select_strategy_complex() {
        let vc = make_vc(VcKind::Postcondition, complex_formula());
        let strategy = select_strategy(&vc);
        assert_eq!(strategy, RefinementStrategy::Interpolation);
    }

    #[test]
    fn test_select_strategy_large_arithmetic() {
        let vc = make_vc(
            VcKind::ArithmeticOverflow {
                op: BinOp::Add,
                operand_tys: (
                    Ty::Int { width: 32, signed: true },
                    Ty::Int { width: 32, signed: true },
                ),
            },
            medium_formula(),
        );
        assert_eq!(select_strategy(&vc), RefinementStrategy::Lazy);
    }

    #[test]
    fn test_select_strategy_with_custom_config() {
        let config = StrategyConfig { eager_complexity_threshold: 50, ..StrategyConfig::default() };
        let vc = make_vc(VcKind::Postcondition, medium_formula());
        let strategy = select_strategy_with_config(&vc, &config);
        // With threshold raised to 50, 26 vars should be eager.
        assert_eq!(strategy, RefinementStrategy::Eager);
    }

    #[test]
    fn test_strategy_config_default() {
        let config = StrategyConfig::default();
        assert_eq!(config.max_predicates, 500);
        assert_eq!(config.max_refinements, 100);
        assert_eq!(config.timeout, Duration::from_secs(60));
        assert_eq!(config.stall_threshold, 5);
    }

    #[test]
    fn test_strategy_display() {
        assert_eq!(format!("{}", RefinementStrategy::Eager), "eager");
        assert_eq!(format!("{}", RefinementStrategy::Lazy), "lazy");
        assert_eq!(format!("{}", RefinementStrategy::Interpolation), "interpolation");
        assert_eq!(format!("{}", RefinementStrategy::Mixed), "mixed");
    }

    #[test]
    fn test_formula_nesting_depth_leaf() {
        assert_eq!(formula_nesting_depth(&Formula::Bool(true)), 0);
        assert_eq!(formula_nesting_depth(&Formula::Int(42)), 0);
    }

    #[test]
    fn test_formula_nesting_depth_comparison() {
        let f =
            Formula::Lt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(10)));
        assert_eq!(formula_nesting_depth(&f), 1);
    }

    #[test]
    fn test_formula_nesting_depth_nested() {
        let f = Formula::And(vec![
            Formula::Not(Box::new(Formula::Lt(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ))),
            Formula::Ge(Box::new(Formula::Var("y".into(), Sort::Int)), Box::new(Formula::Int(0))),
        ]);
        // And(1 + max(Not(1 + Lt(1)) = 3, Ge(1) = 1)) = 1 + 3 = 4
        // Actually: And depth 1 + max(Not depth 1 + Lt depth 1 = 2, Ge depth 1) = 1 + 2 = 3
        assert_eq!(formula_nesting_depth(&f), 3);
    }

    #[test]
    fn test_formula_nesting_depth_quantifier() {
        let f = Formula::Forall(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::Ge(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            )),
        );
        // Forall adds 2 + Ge depth 1 = 3
        assert_eq!(formula_nesting_depth(&f), 3);
    }

    #[test]
    fn test_strategy_config_serde_roundtrip() {
        let config = StrategyConfig::default();
        let json = serde_json::to_string(&config).expect("serialize");
        let deserialized: StrategyConfig = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(deserialized.max_predicates, config.max_predicates);
        assert_eq!(deserialized.max_refinements, config.max_refinements);
        assert_eq!(deserialized.timeout, config.timeout);
    }

    #[test]
    fn test_liveness_uses_interpolation() {
        use trust_types::LivenessProperty;
        let vc = make_vc(
            VcKind::Liveness {
                property: LivenessProperty {
                    name: "termination".into(),
                    operator: TemporalOperator::Eventually,
                    predicate: "state == done".into(),
                    consequent: None,
                    fairness: vec![],
                },
            },
            simple_formula(),
        );
        assert_eq!(select_strategy(&vc), RefinementStrategy::Interpolation);
    }

    #[test]
    fn test_non_termination_uses_interpolation() {
        let vc = make_vc(
            VcKind::NonTermination { context: "loop".into(), measure: "n".into() },
            simple_formula(),
        );
        assert_eq!(select_strategy(&vc), RefinementStrategy::Interpolation);
    }
}
