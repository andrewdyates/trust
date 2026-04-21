// trust-router/timeout.rs: Solver timeout strategies for verification conditions
//
// tRust: Manages per-VC timeouts using multiple strategies: fixed, adaptive
// (learned from historical solve times), progressive (exponential backoff on
// Unknown), and complexity-based (estimated from formula structure).
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;
use std::time::Duration;

use trust_types::{Formula, VcKind, VerificationCondition};
use trust_types::fx::FxHashSet;

/// tRust: Strategy for computing solver timeouts.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub enum TimeoutStrategy {
    /// Fixed timeout for all VCs.
    Fixed(Duration),
    /// Adaptive timeout learned from historical solve times per VcKind.
    Adaptive,
    /// Progressive timeout: starts low, doubles on Unknown, capped at max.
    Progressive,
    /// Timeout scaled by estimated VC complexity.
    VcComplexityBased,
}

/// tRust: Configuration for progressive timeout escalation.
#[derive(Debug, Clone)]
pub struct ProgressiveConfig {
    /// Initial timeout for the first attempt (default: 1s).
    pub initial: Duration,
    /// Multiplier applied on each Unknown result (default: 2.0).
    pub multiplier: f64,
    /// Maximum timeout cap (default: 120s).
    pub max: Duration,
}

impl Default for ProgressiveConfig {
    fn default() -> Self {
        Self {
            initial: Duration::from_secs(1),
            multiplier: 2.0,
            max: Duration::from_secs(120),
        }
    }
}

/// tRust: Configuration for complexity-based timeouts.
#[derive(Debug, Clone)]
pub struct ComplexityConfig {
    /// Base timeout for the simplest VCs (default: 500ms).
    pub base: Duration,
    /// Milliseconds added per unit of complexity score (default: 100ms).
    pub ms_per_complexity_unit: u64,
    /// Maximum timeout cap (default: 300s).
    pub max: Duration,
}

impl Default for ComplexityConfig {
    fn default() -> Self {
        Self {
            base: Duration::from_millis(500),
            ms_per_complexity_unit: 100,
            max: Duration::from_secs(300),
        }
    }
}

/// tRust: Manages per-VC timeouts across verification runs.
///
/// Tracks historical solve times for adaptive mode and attempt counts for
/// progressive mode. Thread-safe usage requires external synchronization.
pub struct TimeoutManager {
    strategy: TimeoutStrategy,
    progressive_config: ProgressiveConfig,
    complexity_config: ComplexityConfig,
    /// Adaptive mode: historical solve times per VcKind description.
    history: FxHashMap<String, Vec<u64>>,
    /// Progressive mode: attempt count per VC (keyed by function + kind).
    attempts: FxHashMap<String, u32>,
}

impl TimeoutManager {
    /// Create a timeout manager with the given strategy.
    #[must_use]
    pub fn new(strategy: TimeoutStrategy) -> Self {
        Self {
            strategy,
            progressive_config: ProgressiveConfig::default(),
            complexity_config: ComplexityConfig::default(),
            history: FxHashMap::default(),
            attempts: FxHashMap::default(),
        }
    }

    /// Set custom progressive config (builder pattern).
    #[must_use]
    pub fn with_progressive_config(mut self, config: ProgressiveConfig) -> Self {
        self.progressive_config = config;
        self
    }

    /// Set custom complexity config (builder pattern).
    #[must_use]
    pub fn with_complexity_config(mut self, config: ComplexityConfig) -> Self {
        self.complexity_config = config;
        self
    }

    /// Compute the timeout for a VC using the configured strategy.
    #[must_use]
    pub fn compute_timeout(&self, vc: &VerificationCondition) -> Duration {
        compute_timeout(vc, &self.strategy, self)
    }

    /// Record a solve time for adaptive learning.
    pub fn record_solve_time(&mut self, vc: &VerificationCondition, time_ms: u64) {
        let key = vc_kind_key(&vc.kind);
        let times = self.history.entry(key).or_default();
        times.push(time_ms);
        if times.len() > 1000 {
            times.remove(0);
        }
    }

    /// Record an Unknown result to escalate progressive timeout.
    pub fn record_unknown(&mut self, vc: &VerificationCondition) {
        let key = vc_attempt_key(vc);
        let count = self.attempts.entry(key).or_insert(0);
        *count += 1;
    }

    /// Reset the progressive attempt counter for a VC.
    pub fn reset_attempts(&mut self, vc: &VerificationCondition) {
        let key = vc_attempt_key(vc);
        self.attempts.remove(&key);
    }

    /// Get the current strategy.
    #[must_use]
    pub fn strategy(&self) -> &TimeoutStrategy {
        &self.strategy
    }

    /// Get the adaptive historical average for a VcKind, in ms.
    #[must_use]
    pub fn adaptive_avg_ms(&self, kind: &VcKind) -> Option<f64> {
        let key = vc_kind_key(kind);
        let times = self.history.get(&key)?;
        if times.is_empty() {
            return None;
        }
        let sum: u64 = times.iter().sum();
        Some(sum as f64 / times.len() as f64)
    }
}

/// tRust: Compute the timeout for a VC given a strategy and manager state.
#[must_use]
pub fn compute_timeout(
    vc: &VerificationCondition,
    strategy: &TimeoutStrategy,
    manager: &TimeoutManager,
) -> Duration {
    match strategy {
        TimeoutStrategy::Fixed(duration) => *duration,
        TimeoutStrategy::Adaptive => compute_adaptive_timeout(vc, manager),
        TimeoutStrategy::Progressive => compute_progressive_timeout(vc, manager),
        TimeoutStrategy::VcComplexityBased => compute_complexity_timeout(vc, manager),
    }
}

/// tRust: Estimate VC difficulty from formula structure.
///
/// Returns a score >= 1.0. Higher scores indicate harder VCs.
#[must_use]
pub fn vc_complexity_score(vc: &VerificationCondition) -> f64 {
    let depth = formula_depth(&vc.formula) as f64;
    let quantifiers = quantifier_count(&vc.formula) as f64;
    let variables = variable_count(&vc.formula) as f64;
    let array_ops = array_op_count(&vc.formula) as f64;

    let score = 1.0
        + (depth * 0.5)
        + (quantifiers * 5.0)
        + (variables * 0.3)
        + (array_ops * 2.0);

    score.max(1.0)
}

/// Compute the depth of a formula tree (max nesting level).
#[must_use]
pub fn formula_depth(formula: &Formula) -> usize {
    formula_fold(formula, |children_depths| {
        1 + children_depths.into_iter().max().unwrap_or(0)
    })
}

/// Count the total number of quantifiers in a formula.
#[must_use]
pub fn quantifier_count(formula: &Formula) -> usize {
    match formula {
        Formula::Forall(_, body) | Formula::Exists(_, body) => 1 + quantifier_count(body),
        _ => formula_children(formula)
            .iter()
            .map(|c| quantifier_count(c))
            .sum(),
    }
}

/// Count unique variables referenced in a formula.
#[must_use]
pub fn variable_count(formula: &Formula) -> usize {
    let mut vars = FxHashSet::default();
    collect_variables(formula, &mut vars);
    vars.len()
}

// -- Formula traversal helpers --

/// Get the immediate child sub-formulas of a formula node.
///
/// Delegates to `Formula::children()` from trust-types.
fn formula_children(formula: &Formula) -> Vec<&Formula> {
    formula.children()
}

/// Generic fold over formula tree depth. Returns 0 for leaves.
fn formula_fold<F>(formula: &Formula, combine: F) -> usize
where
    F: Fn(Vec<usize>) -> usize + Copy,
{
    let children = formula_children(formula);
    if children.is_empty() {
        return 0;
    }
    let child_values: Vec<usize> = children
        .into_iter()
        .map(|c| formula_fold(c, combine))
        .collect();
    combine(child_values)
}

fn collect_variables<'a>(
    formula: &'a Formula,
    vars: &mut FxHashSet<&'a str>,
) {
    match formula {
        Formula::Var(name, _) => {
            vars.insert(name.as_str());
        }
        Formula::Forall(bindings, body) | Formula::Exists(bindings, body) => {
            for (name, _) in bindings {
                vars.insert(name.as_str());
            }
            collect_variables(body, vars);
        }
        _ => {
            for child in formula_children(formula) {
                collect_variables(child, vars);
            }
        }
    }
}

/// Count array operations (Select + Store) in a formula.
fn array_op_count(formula: &Formula) -> usize {
    let base = match formula {
        Formula::Select(..) | Formula::Store(..) => 1,
        _ => 0,
    };
    base + formula_children(formula)
        .iter()
        .map(|c| array_op_count(c))
        .sum::<usize>()
}

// -- Internal helpers --

fn vc_kind_key(kind: &VcKind) -> String {
    kind.description()
        .split(':')
        .next()
        .unwrap_or("unknown")
        .to_string()
}

fn vc_attempt_key(vc: &VerificationCondition) -> String {
    format!("{}:{}", vc.function, vc.kind.description())
}

fn compute_adaptive_timeout(
    vc: &VerificationCondition,
    manager: &TimeoutManager,
) -> Duration {
    let key = vc_kind_key(&vc.kind);
    if let Some(times) = manager.history.get(&key)
        && !times.is_empty() {
            let sum: u64 = times.iter().sum();
            let avg_ms = sum as f64 / times.len() as f64;
            let timeout_ms = (avg_ms * 2.0).max(1000.0) as u64;
            return Duration::from_millis(timeout_ms);
        }
    Duration::from_secs(10)
}

fn compute_progressive_timeout(
    vc: &VerificationCondition,
    manager: &TimeoutManager,
) -> Duration {
    let key = vc_attempt_key(vc);
    let attempts = manager.attempts.get(&key).copied().unwrap_or(0);
    let config = &manager.progressive_config;

    let initial_ms = config.initial.as_millis() as f64;
    let timeout_ms = initial_ms * config.multiplier.powi(attempts as i32);
    let timeout = Duration::from_millis(timeout_ms as u64);

    timeout.min(config.max)
}

fn compute_complexity_timeout(
    vc: &VerificationCondition,
    manager: &TimeoutManager,
) -> Duration {
    let score = vc_complexity_score(vc);
    let config = &manager.complexity_config;

    let base_ms = config.base.as_millis() as u64;
    let extra_ms = (score * config.ms_per_complexity_unit as f64) as u64;
    let timeout = Duration::from_millis(base_ms + extra_ms);

    timeout.min(config.max)
}

#[cfg(test)]
mod tests {
    use trust_types::*;

    use super::*;

    fn simple_vc() -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "test_fn".to_string(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
        }
    }

    fn complex_vc() -> VerificationCondition {
        let x = Formula::Var("x".to_string(), Sort::Int);
        let one = Formula::Int(1);
        let zero = Formula::Int(0);
        let x_gt_0 = Formula::Gt(Box::new(x.clone()), Box::new(zero));
        let x_plus_1 = Formula::Add(Box::new(x.clone()), Box::new(one));
        let sum_gt_x = Formula::Gt(Box::new(x_plus_1), Box::new(x.clone()));
        let body = Formula::Implies(Box::new(x_gt_0), Box::new(sum_gt_x));
        let formula = Formula::Forall(
            vec![("x".to_string(), Sort::Int)],
            Box::new(body),
        );

        VerificationCondition {
            kind: VcKind::Postcondition,
            function: "complex_fn".to_string(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
        }
    }

    fn multi_var_vc() -> VerificationCondition {
        let x = Formula::Var("x".to_string(), Sort::Int);
        let y = Formula::Var("y".to_string(), Sort::Int);
        let z = Formula::Var("z".to_string(), Sort::Int);
        let xy = Formula::Add(Box::new(x), Box::new(y));
        let formula = Formula::Eq(Box::new(xy), Box::new(z));

        VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "multi_var_fn".to_string(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
        }
    }

    #[test]
    fn test_fixed_timeout_returns_exact_duration() {
        let manager = TimeoutManager::new(
            TimeoutStrategy::Fixed(Duration::from_secs(5)),
        );
        let vc = simple_vc();
        assert_eq!(manager.compute_timeout(&vc), Duration::from_secs(5));
    }

    #[test]
    fn test_formula_depth_literal() {
        assert_eq!(formula_depth(&Formula::Bool(true)), 0);
        assert_eq!(formula_depth(&Formula::Int(42)), 0);
    }

    #[test]
    fn test_formula_depth_nested() {
        let a = Formula::Var("a".to_string(), Sort::Bool);
        let b = Formula::Var("b".to_string(), Sort::Bool);
        let and = Formula::And(vec![a, b]);
        assert_eq!(formula_depth(&and), 1);

        let deep = Formula::Not(Box::new(Formula::Not(Box::new(
            Formula::Bool(true),
        ))));
        assert_eq!(formula_depth(&deep), 2);
    }

    #[test]
    fn test_quantifier_count_none() {
        let f = Formula::And(vec![Formula::Bool(true), Formula::Bool(false)]);
        assert_eq!(quantifier_count(&f), 0);
    }

    #[test]
    fn test_quantifier_count_nested() {
        let body = Formula::Bool(true);
        let inner = Formula::Forall(
            vec![("x".to_string(), Sort::Int)],
            Box::new(body),
        );
        let outer = Formula::Exists(
            vec![("y".to_string(), Sort::Int)],
            Box::new(inner),
        );
        assert_eq!(quantifier_count(&outer), 2);
    }

    #[test]
    fn test_variable_count_unique() {
        let vc = multi_var_vc();
        assert_eq!(variable_count(&vc.formula), 3);
    }

    #[test]
    fn test_variable_count_duplicates() {
        let x1 = Formula::Var("x".to_string(), Sort::Int);
        let x2 = Formula::Var("x".to_string(), Sort::Int);
        let f = Formula::Add(Box::new(x1), Box::new(x2));
        assert_eq!(variable_count(&f), 1);
    }

    #[test]
    fn test_vc_complexity_score_simple_is_low() {
        let vc = simple_vc();
        let score = vc_complexity_score(&vc);
        assert!(score >= 1.0);
        assert!(score < 3.0);
    }

    #[test]
    fn test_vc_complexity_score_complex_is_higher() {
        let simple = simple_vc();
        let complex = complex_vc();
        let simple_score = vc_complexity_score(&simple);
        let complex_score = vc_complexity_score(&complex);
        assert!(
            complex_score > simple_score,
            "complex ({complex_score}) should be > simple ({simple_score})"
        );
    }

    #[test]
    fn test_vc_complexity_score_quantifier_weight() {
        let complex = complex_vc();
        let score = vc_complexity_score(&complex);
        assert!(
            score >= 6.0,
            "quantifier should add at least 5.0: got {score}"
        );
    }

    #[test]
    fn test_adaptive_timeout_no_history() {
        let manager = TimeoutManager::new(TimeoutStrategy::Adaptive);
        let vc = simple_vc();
        assert_eq!(manager.compute_timeout(&vc), Duration::from_secs(10));
    }

    #[test]
    fn test_adaptive_timeout_with_history() {
        let mut manager = TimeoutManager::new(TimeoutStrategy::Adaptive);
        let vc = simple_vc();
        manager.record_solve_time(&vc, 100);
        manager.record_solve_time(&vc, 200);
        manager.record_solve_time(&vc, 300);
        let timeout = manager.compute_timeout(&vc);
        assert_eq!(timeout, Duration::from_millis(1000));
    }

    #[test]
    fn test_adaptive_timeout_scales_with_history() {
        let mut manager = TimeoutManager::new(TimeoutStrategy::Adaptive);
        let vc = simple_vc();
        for _ in 0..10 {
            manager.record_solve_time(&vc, 5000);
        }
        let timeout = manager.compute_timeout(&vc);
        assert_eq!(timeout, Duration::from_millis(10000));
    }

    #[test]
    fn test_progressive_timeout_initial() {
        let manager = TimeoutManager::new(TimeoutStrategy::Progressive);
        let vc = simple_vc();
        assert_eq!(manager.compute_timeout(&vc), Duration::from_secs(1));
    }

    #[test]
    fn test_progressive_timeout_doubles_on_unknown() {
        let mut manager = TimeoutManager::new(TimeoutStrategy::Progressive);
        let vc = simple_vc();
        assert_eq!(manager.compute_timeout(&vc), Duration::from_secs(1));
        manager.record_unknown(&vc);
        assert_eq!(manager.compute_timeout(&vc), Duration::from_secs(2));
        manager.record_unknown(&vc);
        assert_eq!(manager.compute_timeout(&vc), Duration::from_secs(4));
        manager.record_unknown(&vc);
        assert_eq!(manager.compute_timeout(&vc), Duration::from_secs(8));
    }

    #[test]
    fn test_progressive_timeout_capped_at_max() {
        let config = ProgressiveConfig {
            initial: Duration::from_secs(1),
            multiplier: 2.0,
            max: Duration::from_secs(10),
        };
        let mut manager = TimeoutManager::new(TimeoutStrategy::Progressive)
            .with_progressive_config(config);
        let vc = simple_vc();
        for _ in 0..20 {
            manager.record_unknown(&vc);
        }
        assert_eq!(manager.compute_timeout(&vc), Duration::from_secs(10));
    }

    #[test]
    fn test_progressive_timeout_resets_on_definitive() {
        let mut manager = TimeoutManager::new(TimeoutStrategy::Progressive);
        let vc = simple_vc();
        manager.record_unknown(&vc);
        manager.record_unknown(&vc);
        assert_eq!(manager.compute_timeout(&vc), Duration::from_secs(4));
        manager.reset_attempts(&vc);
        assert_eq!(manager.compute_timeout(&vc), Duration::from_secs(1));
    }

    #[test]
    fn test_complexity_timeout_simple_vc() {
        let manager =
            TimeoutManager::new(TimeoutStrategy::VcComplexityBased);
        let vc = simple_vc();
        let timeout = manager.compute_timeout(&vc);
        assert!(timeout >= Duration::from_millis(500));
        assert!(timeout <= Duration::from_secs(5));
    }

    #[test]
    fn test_complexity_timeout_complex_vc() {
        let manager =
            TimeoutManager::new(TimeoutStrategy::VcComplexityBased);
        let simple = simple_vc();
        let complex = complex_vc();
        let simple_timeout = manager.compute_timeout(&simple);
        let complex_timeout = manager.compute_timeout(&complex);
        assert!(
            complex_timeout > simple_timeout,
            "complex ({complex_timeout:?}) > simple ({simple_timeout:?})"
        );
    }

    #[test]
    fn test_complexity_timeout_capped() {
        let config = ComplexityConfig {
            base: Duration::from_secs(100),
            ms_per_complexity_unit: 10_000,
            max: Duration::from_secs(5),
        };
        let manager = TimeoutManager::new(TimeoutStrategy::VcComplexityBased)
            .with_complexity_config(config);
        let vc = complex_vc();
        assert!(manager.compute_timeout(&vc) <= Duration::from_secs(5));
    }

    #[test]
    fn test_adaptive_avg_ms_returns_none_without_history() {
        let manager = TimeoutManager::new(TimeoutStrategy::Adaptive);
        assert!(manager.adaptive_avg_ms(&VcKind::DivisionByZero).is_none());
    }

    #[test]
    fn test_adaptive_avg_ms_returns_average() {
        let mut manager = TimeoutManager::new(TimeoutStrategy::Adaptive);
        let vc = simple_vc();
        manager.record_solve_time(&vc, 100);
        manager.record_solve_time(&vc, 300);
        let avg = manager.adaptive_avg_ms(&VcKind::DivisionByZero);
        assert!(avg.is_some());
        assert!((avg.unwrap() - 200.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_timeout_strategy_eq() {
        assert_eq!(
            TimeoutStrategy::Fixed(Duration::from_secs(1)),
            TimeoutStrategy::Fixed(Duration::from_secs(1))
        );
        assert_ne!(
            TimeoutStrategy::Fixed(Duration::from_secs(1)),
            TimeoutStrategy::Adaptive
        );
        assert_eq!(
            TimeoutStrategy::Progressive,
            TimeoutStrategy::Progressive
        );
    }

    #[test]
    fn test_array_op_increases_complexity() {
        let arr = Formula::Var(
            "arr".to_string(),
            Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int)),
        );
        let idx = Formula::Int(0);
        let val = Formula::Int(42);
        let store = Formula::Store(
            Box::new(arr.clone()),
            Box::new(idx.clone()),
            Box::new(val),
        );
        let select = Formula::Select(Box::new(store), Box::new(idx));

        let vc_with_arrays = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "array_fn".to_string(),
            location: SourceSpan::default(),
            formula: select,
            contract_metadata: None,
        };

        let simple = simple_vc();
        assert!(
            vc_complexity_score(&vc_with_arrays) > vc_complexity_score(&simple),
            "array ops should increase complexity"
        );
    }

    #[test]
    fn test_manager_strategy_accessor() {
        let manager = TimeoutManager::new(TimeoutStrategy::Adaptive);
        assert_eq!(*manager.strategy(), TimeoutStrategy::Adaptive);
    }
}
