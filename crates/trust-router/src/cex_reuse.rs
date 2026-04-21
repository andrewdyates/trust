// trust-router/cex_reuse.rs: Counterexample reuse optimization
//
// KLEE-inspired: before invoking the solver on a new query, check if any
// cached counterexample already satisfies the formula. If so, we can
// immediately return Failed without a solver call.
//
// For formulas that are conjunctions, we can also quickly discard
// counterexamples that violate any conjunct under the assignment.
//
// Reference: Cadar, Dunbar, Engler. "KLEE: Unassisted and Automatic Generation
// of High-Coverage Tests for Complex Systems Programs." OSDI 2008, Section 4.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;

use trust_types::{Counterexample, CounterexampleValue, Formula};

/// Pool of cached counterexamples for reuse across queries.
///
/// When a solver returns a counterexample, store it here. Before sending
/// a new query to the solver, evaluate the formula under each cached
/// counterexample. If one satisfies it, return it directly.
pub struct CexPool {
    /// Cached counterexamples, most recent first.
    pool: Vec<Counterexample>,
    /// Maximum pool size.
    max_size: usize,
    /// Metrics.
    reuse_hits: u64,
    reuse_misses: u64,
}

/// Result of attempting counterexample reuse.
pub enum CexReuseResult {
    /// A cached counterexample satisfies the formula.
    Reused(Counterexample),
    /// No cached counterexample works; must call solver.
    NoMatch,
}

/// Pool statistics.
#[derive(Debug, Clone)]
pub struct CexPoolStats {
    pub pool_size: usize,
    pub reuse_hits: u64,
    pub reuse_misses: u64,
    pub reuse_rate: f64,
}

impl CexPool {
    /// Create a new pool with the given maximum size.
    #[must_use]
    pub fn new(max_size: usize) -> Self {
        Self {
            pool: Vec::new(),
            max_size,
            reuse_hits: 0,
            reuse_misses: 0,
        }
    }

    /// Add a counterexample to the pool.
    ///
    /// If the pool is full, the oldest counterexample is evicted.
    pub fn add(&mut self, cex: Counterexample) {
        if self.pool.len() >= self.max_size {
            self.pool.pop(); // remove oldest
        }
        self.pool.insert(0, cex); // most recent first
    }

    /// Try to reuse a cached counterexample for the given formula.
    ///
    /// Convention: the formula is a negated property. SAT means a violation.
    /// We check if any cached assignment makes the formula true.
    pub fn try_reuse(&mut self, formula: &Formula) -> CexReuseResult {
        for cex in &self.pool {
            let env = build_env(cex);
            if evaluate(formula, &env) == EvalResult::True {
                self.reuse_hits += 1;
                return CexReuseResult::Reused(cex.clone());
            }
        }
        self.reuse_misses += 1;
        CexReuseResult::NoMatch
    }

    /// Get pool statistics.
    #[must_use]
    pub fn stats(&self) -> CexPoolStats {
        let total = self.reuse_hits + self.reuse_misses;
        CexPoolStats {
            pool_size: self.pool.len(),
            reuse_hits: self.reuse_hits,
            reuse_misses: self.reuse_misses,
            reuse_rate: if total == 0 {
                0.0
            } else {
                self.reuse_hits as f64 / total as f64
            },
        }
    }

    /// Number of counterexamples in the pool.
    #[must_use]
    pub fn len(&self) -> usize {
        self.pool.len()
    }

    /// Whether the pool is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.pool.is_empty()
    }

    /// Clear the pool.
    pub fn clear(&mut self) {
        self.pool.clear();
        self.reuse_hits = 0;
        self.reuse_misses = 0;
    }
}

// ---------------------------------------------------------------------------
// Formula evaluation under a concrete assignment
// ---------------------------------------------------------------------------

type Env = FxHashMap<String, i128>;

fn build_env(cex: &Counterexample) -> Env {
    let mut env = FxHashMap::default();
    for (name, val) in &cex.assignments {
        let int_val = match val {
            CounterexampleValue::Bool(b) => i128::from(*b),
            CounterexampleValue::Int(n) => *n,
            CounterexampleValue::Uint(n) => *n as i128,
            CounterexampleValue::Float(f) => *f as i128,
            // tRust #734: non-panicking fallback for #[non_exhaustive] forward compat
            _ => continue,
        };
        env.insert(name.clone(), int_val);
    }
    env
}

/// Evaluation result: True, False, or Unknown (when variables are missing).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum EvalResult {
    True,
    False,
    Unknown,
}

impl EvalResult {
    fn from_bool(b: bool) -> Self {
        if b { EvalResult::True } else { EvalResult::False }
    }

    fn not(self) -> Self {
        match self {
            EvalResult::True => EvalResult::False,
            EvalResult::False => EvalResult::True,
            EvalResult::Unknown => EvalResult::Unknown,
        }
    }
}

/// Evaluate a formula under a concrete variable assignment.
///
/// Returns Unknown for formulas with unresolved variables or unsupported
/// constructs (arrays, quantifiers, bitvector ops).
fn evaluate(formula: &Formula, env: &Env) -> EvalResult {
    match formula {
        Formula::Bool(b) => EvalResult::from_bool(*b),
        Formula::Int(n) => {
            // An integer in boolean context: nonzero = true
            EvalResult::from_bool(*n != 0)
        }
        Formula::Var(name, _) => match env.get(name.as_str()) {
            Some(val) => EvalResult::from_bool(*val != 0),
            None => EvalResult::Unknown,
        },
        Formula::Not(inner) => evaluate(inner, env).not(),
        Formula::And(children) => {
            let mut all_true = true;
            for child in children {
                match evaluate(child, env) {
                    EvalResult::False => return EvalResult::False,
                    EvalResult::Unknown => all_true = false,
                    EvalResult::True => {}
                }
            }
            if all_true {
                EvalResult::True
            } else {
                EvalResult::Unknown
            }
        }
        Formula::Or(children) => {
            let mut any_unknown = false;
            for child in children {
                match evaluate(child, env) {
                    EvalResult::True => return EvalResult::True,
                    EvalResult::Unknown => any_unknown = true,
                    EvalResult::False => {}
                }
            }
            if any_unknown {
                EvalResult::Unknown
            } else {
                EvalResult::False
            }
        }
        Formula::Implies(lhs, rhs) => {
            let l = evaluate(lhs, env);
            let r = evaluate(rhs, env);
            match (l, r) {
                (EvalResult::False, _) | (_, EvalResult::True) => EvalResult::True,
                (EvalResult::True, EvalResult::False) => EvalResult::False,
                _ => EvalResult::Unknown,
            }
        }
        // Arithmetic comparisons: evaluate both sides as integers.
        Formula::Eq(lhs, rhs) => eval_cmp(lhs, rhs, env, |a, b| a == b),
        Formula::Lt(lhs, rhs) => eval_cmp(lhs, rhs, env, |a, b| a < b),
        Formula::Le(lhs, rhs) => eval_cmp(lhs, rhs, env, |a, b| a <= b),
        Formula::Gt(lhs, rhs) => eval_cmp(lhs, rhs, env, |a, b| a > b),
        Formula::Ge(lhs, rhs) => eval_cmp(lhs, rhs, env, |a, b| a >= b),
        // Arithmetic: compute integer values.
        Formula::Add(_, _)
        | Formula::Sub(_, _)
        | Formula::Mul(_, _)
        | Formula::Div(_, _)
        | Formula::Rem(_, _)
        | Formula::Neg(_) => {
            // These are integer-valued, not boolean. Evaluate as nonzero = true.
            match eval_int(formula, env) {
                Some(n) => EvalResult::from_bool(n != 0),
                None => EvalResult::Unknown,
            }
        }
        Formula::Ite(cond, then_f, else_f) => {
            match evaluate(cond, env) {
                EvalResult::True => evaluate(then_f, env),
                EvalResult::False => evaluate(else_f, env),
                EvalResult::Unknown => EvalResult::Unknown,
            }
        }
        // Unsupported constructs: bail out conservatively.
        _ => EvalResult::Unknown,
    }
}

/// Evaluate a formula as an integer value.
fn eval_int(formula: &Formula, env: &Env) -> Option<i128> {
    match formula {
        Formula::Int(n) => Some(*n),
        Formula::Bool(b) => Some(i128::from(*b)),
        Formula::Var(name, _) => env.get(name.as_str()).copied(),
        Formula::Add(a, b) => Some(eval_int(a, env)? + eval_int(b, env)?),
        Formula::Sub(a, b) => Some(eval_int(a, env)? - eval_int(b, env)?),
        Formula::Mul(a, b) => Some(eval_int(a, env)? * eval_int(b, env)?),
        Formula::Div(a, b) => {
            let bv = eval_int(b, env)?;
            if bv == 0 {
                None
            } else {
                Some(eval_int(a, env)? / bv)
            }
        }
        Formula::Rem(a, b) => {
            let bv = eval_int(b, env)?;
            if bv == 0 {
                None
            } else {
                Some(eval_int(a, env)? % bv)
            }
        }
        Formula::Neg(inner) => Some(-eval_int(inner, env)?),
        Formula::Ite(cond, then_f, else_f) => {
            match evaluate(cond, env) {
                EvalResult::True => eval_int(then_f, env),
                EvalResult::False => eval_int(else_f, env),
                _ => None,
            }
        }
        Formula::BitVec { value, .. } => Some(*value),
        _ => None,
    }
}

/// Evaluate a comparison by computing both sides as integers.
fn eval_cmp(
    lhs: &Formula,
    rhs: &Formula,
    env: &Env,
    cmp: fn(i128, i128) -> bool,
) -> EvalResult {
    match (eval_int(lhs, env), eval_int(rhs, env)) {
        (Some(a), Some(b)) => EvalResult::from_bool(cmp(a, b)),
        _ => EvalResult::Unknown,
    }
}

#[cfg(test)]
mod tests {
    use trust_types::Sort;

    use super::*;

    fn make_cex(assignments: &[(&str, i128)]) -> Counterexample {
        Counterexample::new(
            assignments
                .iter()
                .map(|(name, val)| (name.to_string(), CounterexampleValue::Int(*val)))
                .collect(),
        )
    }

    #[test]
    fn test_cex_reuse_hit() {
        let mut pool = CexPool::new(10);

        // Store a counterexample: x=5, y=3
        pool.add(make_cex(&[("x", 5), ("y", 3)]));

        // Formula: x > 0 AND y > 0 — the cex satisfies this
        let formula = Formula::And(vec![
            Formula::Gt(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            Formula::Gt(
                Box::new(Formula::Var("y".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
        ]);

        assert!(matches!(pool.try_reuse(&formula), CexReuseResult::Reused(_)));

        let stats = pool.stats();
        assert_eq!(stats.reuse_hits, 1);
        assert_eq!(stats.reuse_misses, 0);
    }

    #[test]
    fn test_cex_reuse_miss() {
        let mut pool = CexPool::new(10);

        // Store a counterexample: x=5, y=-3
        pool.add(make_cex(&[("x", 5), ("y", -3)]));

        // Formula: x > 0 AND y > 0 — cex does NOT satisfy (y=-3 < 0)
        let formula = Formula::And(vec![
            Formula::Gt(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            Formula::Gt(
                Box::new(Formula::Var("y".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
        ]);

        assert!(matches!(pool.try_reuse(&formula), CexReuseResult::NoMatch));

        let stats = pool.stats();
        assert_eq!(stats.reuse_hits, 0);
        assert_eq!(stats.reuse_misses, 1);
    }

    #[test]
    fn test_cex_pool_eviction() {
        let mut pool = CexPool::new(2);

        pool.add(make_cex(&[("x", 1)]));
        pool.add(make_cex(&[("x", 2)]));
        pool.add(make_cex(&[("x", 3)]));

        // Pool should have at most 2 entries
        assert_eq!(pool.len(), 2);
    }

    #[test]
    fn test_cex_pool_clear() {
        let mut pool = CexPool::new(10);
        pool.add(make_cex(&[("x", 1)]));
        pool.add(make_cex(&[("x", 2)]));

        pool.clear();
        assert!(pool.is_empty());
    }

    #[test]
    fn test_evaluate_bool_literal() {
        let env = FxHashMap::default();
        assert_eq!(evaluate(&Formula::Bool(true), &env), EvalResult::True);
        assert_eq!(evaluate(&Formula::Bool(false), &env), EvalResult::False);
    }

    #[test]
    fn test_evaluate_not() {
        let env = FxHashMap::default();
        assert_eq!(
            evaluate(&Formula::Not(Box::new(Formula::Bool(true))), &env),
            EvalResult::False,
        );
    }

    #[test]
    fn test_evaluate_comparison_with_arithmetic() {
        let mut env = FxHashMap::default();
        env.insert("x".into(), 10);
        env.insert("y".into(), 3);

        // x + y > 12 => 10 + 3 > 12 => true
        let formula = Formula::Gt(
            Box::new(Formula::Add(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Var("y".into(), Sort::Int)),
            )),
            Box::new(Formula::Int(12)),
        );
        assert_eq!(evaluate(&formula, &env), EvalResult::True);
    }

    #[test]
    fn test_evaluate_missing_variable_unknown() {
        let env = FxHashMap::default();
        let formula = Formula::Gt(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        );
        assert_eq!(evaluate(&formula, &env), EvalResult::Unknown);
    }

    #[test]
    fn test_evaluate_implies() {
        let env = FxHashMap::default();
        // false => anything = true
        assert_eq!(
            evaluate(
                &Formula::Implies(
                    Box::new(Formula::Bool(false)),
                    Box::new(Formula::Bool(false)),
                ),
                &env,
            ),
            EvalResult::True,
        );
        // true => false = false
        assert_eq!(
            evaluate(
                &Formula::Implies(
                    Box::new(Formula::Bool(true)),
                    Box::new(Formula::Bool(false)),
                ),
                &env,
            ),
            EvalResult::False,
        );
    }

    #[test]
    fn test_evaluate_ite() {
        let mut env = FxHashMap::default();
        env.insert("cond".into(), 1);
        env.insert("a".into(), 5);
        env.insert("b".into(), 10);

        // if cond then a > 3 else b > 3
        let formula = Formula::Ite(
            Box::new(Formula::Var("cond".into(), Sort::Bool)),
            Box::new(Formula::Gt(
                Box::new(Formula::Var("a".into(), Sort::Int)),
                Box::new(Formula::Int(3)),
            )),
            Box::new(Formula::Gt(
                Box::new(Formula::Var("b".into(), Sort::Int)),
                Box::new(Formula::Int(3)),
            )),
        );
        assert_eq!(evaluate(&formula, &env), EvalResult::True);
    }

    #[test]
    fn test_evaluate_or() {
        let env = FxHashMap::default();
        assert_eq!(
            evaluate(
                &Formula::Or(vec![Formula::Bool(false), Formula::Bool(true)]),
                &env,
            ),
            EvalResult::True,
        );
        assert_eq!(
            evaluate(
                &Formula::Or(vec![Formula::Bool(false), Formula::Bool(false)]),
                &env,
            ),
            EvalResult::False,
        );
    }

    #[test]
    fn test_evaluate_eq() {
        let mut env = FxHashMap::default();
        env.insert("x".into(), 5);
        let formula = Formula::Eq(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Int(5)),
        );
        assert_eq!(evaluate(&formula, &env), EvalResult::True);
    }

    #[test]
    fn test_cex_reuse_most_recent_first() {
        let mut pool = CexPool::new(10);

        // Add two cexes: old one doesn't match, new one does.
        pool.add(make_cex(&[("x", -1)])); // old
        pool.add(make_cex(&[("x", 5)])); // new (added second, inserted at front)

        let formula = Formula::Gt(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        );

        if let CexReuseResult::Reused(cex) = pool.try_reuse(&formula) {
            // Should get the matching one (x=5)
            let x_val = &cex.assignments[0].1;
            assert!(matches!(x_val, CounterexampleValue::Int(5)));
        } else {
            panic!("expected reuse hit");
        }
    }

    #[test]
    fn test_empty_pool_stats() {
        let pool = CexPool::new(10);
        let stats = pool.stats();
        assert_eq!(stats.pool_size, 0);
        assert_eq!(stats.reuse_hits, 0);
        assert_eq!(stats.reuse_misses, 0);
        assert_eq!(stats.reuse_rate, 0.0);
    }
}
