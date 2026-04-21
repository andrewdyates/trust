// trust-router/optimizer.rs: Solver optimization pipeline
//
// Chains KLEE-inspired optimizations before dispatching to the solver:
//   1. Counterexample reuse — check if a cached cex satisfies the formula
//   2. Query cache — check if we've seen this exact formula before
//   3. Independence — split into independent subproblems
//   4. Solver dispatch — only for formulas that survive all stages
//
// Each stage can short-circuit, avoiding the solver entirely.
//
// Reference: Cadar, Dunbar, Engler. "KLEE: Unassisted and Automatic Generation
// of High-Coverage Tests for Complex Systems Programs." OSDI 2008.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::*;

use crate::cex_reuse::{CexPool, CexPoolStats, CexReuseResult};
use crate::independence::{self, PartitionResult};
use crate::query_cache::{CacheLookupResult, CacheStats, QueryCache};

/// Configuration for the optimizer pipeline.
#[derive(Debug, Clone)]
pub struct OptimizerConfig {
    /// Maximum number of entries in the query cache.
    pub cache_max_entries: usize,
    /// Maximum number of counterexamples in the reuse pool.
    pub cex_pool_max_size: usize,
    /// Whether to enable counterexample reuse.
    pub enable_cex_reuse: bool,
    /// Whether to enable query caching.
    pub enable_query_cache: bool,
    /// Whether to enable constraint independence splitting.
    pub enable_independence: bool,
}

impl Default for OptimizerConfig {
    fn default() -> Self {
        Self {
            cache_max_entries: 10_000,
            cex_pool_max_size: 1_000,
            enable_cex_reuse: true,
            enable_query_cache: true,
            enable_independence: true,
        }
    }
}

/// Which optimization stage short-circuited.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OptimizationStage {
    /// Counterexample reuse found a matching cached counterexample.
    CexReuse,
    /// Query cache had the result.
    QueryCache,
    /// Solved by the backend (no short-circuit).
    Solver,
}

/// Result from the optimizer pipeline.
#[derive(Debug)]
pub struct OptimizedResult {
    /// The verification result.
    pub result: VerificationResult,
    /// Which stage produced the result.
    pub stage: OptimizationStage,
    /// Whether the formula was split by independence optimization.
    pub was_split: bool,
    /// Number of independent partitions (1 if not split).
    pub partition_count: usize,
}

/// Aggregate optimizer statistics.
#[derive(Debug, Clone)]
pub struct OptimizerStats {
    pub cache_stats: CacheStats,
    pub cex_pool_stats: CexPoolStats,
    pub total_queries: u64,
    pub cex_reuse_short_circuits: u64,
    pub cache_short_circuits: u64,
    pub independence_splits: u64,
    pub solver_calls: u64,
}

/// The solver optimization pipeline.
///
/// Wraps a verification backend with KLEE-inspired optimizations.
/// Use `optimize_and_verify` to run a formula through the pipeline.
pub struct Optimizer {
    cache: QueryCache,
    cex_pool: CexPool,
    config: OptimizerConfig,
    // Metrics
    total_queries: u64,
    cex_reuse_short_circuits: u64,
    cache_short_circuits: u64,
    independence_splits: u64,
    solver_calls: u64,
}

impl Optimizer {
    /// Create a new optimizer with the given configuration.
    #[must_use]
    pub fn new(config: OptimizerConfig) -> Self {
        let cache = QueryCache::new(config.cache_max_entries);
        let cex_pool = CexPool::new(config.cex_pool_max_size);
        Self {
            cache,
            cex_pool,
            config,
            total_queries: 0,
            cex_reuse_short_circuits: 0,
            cache_short_circuits: 0,
            independence_splits: 0,
            solver_calls: 0,
        }
    }

    /// Create a new optimizer with default configuration.
    #[must_use]
    pub fn with_defaults() -> Self {
        Self::new(OptimizerConfig::default())
    }

    /// Run a formula through the optimization pipeline.
    ///
    /// The `solve` callback is called only if the formula cannot be resolved
    /// by cex reuse or query cache. It should call the actual solver backend.
    pub fn optimize_and_verify<F>(&mut self, formula: &Formula, solve: F) -> OptimizedResult
    where
        F: Fn(&Formula) -> VerificationResult,
    {
        self.total_queries += 1;

        // Stage 1: Counterexample reuse
        if self.config.enable_cex_reuse
            && let CexReuseResult::Reused(cex) = self.cex_pool.try_reuse(formula) {
                self.cex_reuse_short_circuits += 1;
                let result = VerificationResult::Failed {
                    solver: "cex-reuse".to_string(),
                    time_ms: 0,
                    counterexample: Some(cex),
                };
                // Also store in query cache for future lookups.
                if self.config.enable_query_cache {
                    self.cache.store(formula, result.clone());
                }
                return OptimizedResult {
                    result,
                    stage: OptimizationStage::CexReuse,
                    was_split: false,
                    partition_count: 1,
                };
            }

        // Stage 2: Query cache
        if self.config.enable_query_cache
            && let CacheLookupResult::Hit(result) = self.cache.lookup(formula) {
                self.cache_short_circuits += 1;
                return OptimizedResult {
                    result,
                    stage: OptimizationStage::QueryCache,
                    was_split: false,
                    partition_count: 1,
                };
            }

        // Stage 3: Independence optimization
        let partition_result = if self.config.enable_independence {
            independence::partition(formula)
        } else {
            PartitionResult {
                partitions: vec![independence::IndependentPartition {
                    conjuncts: vec![formula.clone()],
                    variables: Default::default(),
                }],
                was_split: false,
            }
        };

        if partition_result.was_split {
            self.independence_splits += 1;
        }

        let partition_count = partition_result.partitions.len();

        // Stage 4: Solve each partition
        let result = if partition_result.was_split {
            self.solve_partitions(&partition_result, &solve)
        } else {
            self.solver_calls += 1;
            solve(formula)
        };

        // Store in query cache
        if self.config.enable_query_cache {
            self.cache.store(formula, result.clone());
        }

        // Store counterexamples in the pool
        if let VerificationResult::Failed {
            counterexample: Some(ref cex),
            ..
        } = result
        {
            self.cex_pool.add(cex.clone());
        }

        OptimizedResult {
            result,
            stage: OptimizationStage::Solver,
            was_split: partition_result.was_split,
            partition_count,
        }
    }

    /// Solve each independent partition separately and combine results.
    ///
    /// For the conjunction to be SAT, ALL partitions must be SAT.
    /// For UNSAT (proved), ALL partitions must be UNSAT.
    /// If any partition fails, the whole thing fails.
    fn solve_partitions<F>(
        &mut self,
        partition_result: &PartitionResult,
        solve: &F,
    ) -> VerificationResult
    where
        F: Fn(&Formula) -> VerificationResult,
    {
        let mut total_time_ms: u64 = 0;
        let mut last_solver = String::new();

        for partition in &partition_result.partitions {
            let sub_formula = independence::reconstruct(std::slice::from_ref(partition));

            // Check sub-formula cache first
            if self.config.enable_query_cache
                && let CacheLookupResult::Hit(result) = self.cache.lookup(&sub_formula) {
                    match &result {
                        VerificationResult::Proved { time_ms, solver, .. } => {
                            total_time_ms += time_ms;
                            last_solver.clone_from(solver);
                            continue; // This partition proved, check next
                        }
                        VerificationResult::Failed { .. } => {
                            return result; // Any failure means overall failure
                        }
                        _ => {} // Unknown/timeout: fall through to solver
                    }
                }

            self.solver_calls += 1;
            let result = solve(&sub_formula);

            // Cache sub-result
            if self.config.enable_query_cache {
                self.cache.store(&sub_formula, result.clone());
            }

            match &result {
                VerificationResult::Proved { time_ms, solver, .. } => {
                    total_time_ms += time_ms;
                    last_solver.clone_from(solver);
                }
                VerificationResult::Failed { counterexample, .. } => {
                    // Store counterexample for future reuse
                    if let Some(cex) = counterexample {
                        self.cex_pool.add(cex.clone());
                    }
                    return result;
                }
                VerificationResult::Unknown { .. } | VerificationResult::Timeout { .. } => {
                    return result;
                }
                // tRust #734: non-panicking fallback for #[non_exhaustive] forward compat
                _ => {
                    return VerificationResult::Unknown {
                        solver: "optimizer".to_string(),
                        time_ms: total_time_ms,
                        reason: "unhandled variant".to_string(),
                    };
                }
            }
        }

        // All partitions proved
        VerificationResult::Proved {
            solver: if last_solver.is_empty() {
                "optimizer".to_string()
            } else {
                last_solver
            },
            time_ms: total_time_ms,
            strength: ProofStrength::smt_unsat(),
            proof_certificate: None,
                solver_warnings: None,
        }
    }

    /// Get aggregate optimizer statistics.
    #[must_use]
    pub fn stats(&self) -> OptimizerStats {
        OptimizerStats {
            cache_stats: self.cache.stats(),
            cex_pool_stats: self.cex_pool.stats(),
            total_queries: self.total_queries,
            cex_reuse_short_circuits: self.cex_reuse_short_circuits,
            cache_short_circuits: self.cache_short_circuits,
            independence_splits: self.independence_splits,
            solver_calls: self.solver_calls,
        }
    }

    /// Access the query cache directly.
    #[must_use]
    pub fn cache(&self) -> &QueryCache {
        &self.cache
    }

    /// Access the counterexample pool directly.
    #[must_use]
    pub fn cex_pool(&self) -> &CexPool {
        &self.cex_pool
    }

    /// Clear all caches and reset metrics.
    pub fn clear(&mut self) {
        self.cache.clear();
        self.cex_pool.clear();
        self.total_queries = 0;
        self.cex_reuse_short_circuits = 0;
        self.cache_short_circuits = 0;
        self.independence_splits = 0;
        self.solver_calls = 0;
    }
}

#[cfg(test)]
mod tests {
    use trust_types::Sort;

    use super::*;

    fn mock_prove(_formula: &Formula) -> VerificationResult {
        VerificationResult::Proved {
            solver: "mock".to_string(),
            time_ms: 10,
            strength: ProofStrength::smt_unsat(), proof_certificate: None,
                solver_warnings: None, }
    }

    fn mock_fail(_formula: &Formula) -> VerificationResult {
        // Create a counterexample based on formula variables
        let cex = Counterexample::new(vec![(
            "x".to_string(),
            CounterexampleValue::Int(42),
        )]);
        VerificationResult::Failed {
            solver: "mock".to_string(),
            time_ms: 5,
            counterexample: Some(cex),
        }
    }

    #[test]
    fn test_optimizer_basic_prove() {
        let mut opt = Optimizer::with_defaults();
        let formula = Formula::Bool(true);

        let result = opt.optimize_and_verify(&formula, mock_prove);
        assert!(result.result.is_proved());
        assert_eq!(result.stage, OptimizationStage::Solver);

        let stats = opt.stats();
        assert_eq!(stats.total_queries, 1);
        assert_eq!(stats.solver_calls, 1);
    }

    #[test]
    fn test_optimizer_query_cache_hit() {
        let mut opt = Optimizer::with_defaults();
        let formula = Formula::Bool(true);

        // First call: solver
        let r1 = opt.optimize_and_verify(&formula, mock_prove);
        assert_eq!(r1.stage, OptimizationStage::Solver);

        // Second call: cache hit
        let r2 = opt.optimize_and_verify(&formula, mock_prove);
        assert_eq!(r2.stage, OptimizationStage::QueryCache);
        assert!(r2.result.is_proved());

        let stats = opt.stats();
        assert_eq!(stats.total_queries, 2);
        assert_eq!(stats.cache_short_circuits, 1);
        assert_eq!(stats.solver_calls, 1);
    }

    #[test]
    fn test_optimizer_cex_reuse() {
        let mut opt = Optimizer::with_defaults();

        // First: solve a formula that fails and produces a counterexample
        let f1 = Formula::Gt(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        );
        let _r1 = opt.optimize_and_verify(&f1, mock_fail);

        // The cex (x=42) is now in the pool.
        // A new formula where x=42 satisfies it should reuse the cex.
        let f2 = Formula::Gt(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Int(10)),
        );

        let r2 = opt.optimize_and_verify(&f2, mock_prove);
        assert_eq!(r2.stage, OptimizationStage::CexReuse);
        assert!(r2.result.is_failed());

        let stats = opt.stats();
        assert_eq!(stats.cex_reuse_short_circuits, 1);
    }

    #[test]
    fn test_optimizer_independence_split() {
        let mut opt = Optimizer::with_defaults();

        // (x > 0) AND (y > 0) — two independent partitions
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

        let result = opt.optimize_and_verify(&formula, mock_prove);
        assert!(result.result.is_proved());
        assert!(result.was_split);
        assert_eq!(result.partition_count, 2);

        let stats = opt.stats();
        assert_eq!(stats.independence_splits, 1);
        // Two partitions each need a solver call
        assert_eq!(stats.solver_calls, 2);
    }

    #[test]
    fn test_optimizer_independence_early_fail() {
        let mut opt = Optimizer::with_defaults();

        // (x > 0) AND (y > 0) — two independent partitions
        // If the first partition fails, we stop early.
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

        let result = opt.optimize_and_verify(&formula, mock_fail);
        assert!(result.result.is_failed());
        assert!(result.was_split);

        let stats = opt.stats();
        // Should have stopped after the first partition failed
        assert!(stats.solver_calls <= 2);
    }

    #[test]
    fn test_optimizer_disabled_stages() {
        let config = OptimizerConfig {
            enable_cex_reuse: false,
            enable_query_cache: false,
            enable_independence: false,
            ..OptimizerConfig::default()
        };
        let mut opt = Optimizer::new(config);
        let formula = Formula::Bool(true);

        // First call
        opt.optimize_and_verify(&formula, mock_prove);
        // Second call — should still call solver (no cache)
        let r2 = opt.optimize_and_verify(&formula, mock_prove);
        assert_eq!(r2.stage, OptimizationStage::Solver);

        let stats = opt.stats();
        assert_eq!(stats.solver_calls, 2);
        assert_eq!(stats.cache_short_circuits, 0);
    }

    #[test]
    fn test_optimizer_clear() {
        let mut opt = Optimizer::with_defaults();
        let formula = Formula::Bool(true);

        opt.optimize_and_verify(&formula, mock_prove);
        opt.clear();

        let stats = opt.stats();
        assert_eq!(stats.total_queries, 0);
        assert_eq!(stats.solver_calls, 0);
        assert!(opt.cache().is_empty());
        assert!(opt.cex_pool().is_empty());
    }

    #[test]
    fn test_optimizer_stats_initial() {
        let opt = Optimizer::with_defaults();
        let stats = opt.stats();
        assert_eq!(stats.total_queries, 0);
        assert_eq!(stats.solver_calls, 0);
        assert_eq!(stats.cex_reuse_short_circuits, 0);
        assert_eq!(stats.cache_short_circuits, 0);
        assert_eq!(stats.independence_splits, 0);
    }

    #[test]
    fn test_optimizer_config_default() {
        let config = OptimizerConfig::default();
        assert_eq!(config.cache_max_entries, 10_000);
        assert_eq!(config.cex_pool_max_size, 1_000);
        assert!(config.enable_cex_reuse);
        assert!(config.enable_query_cache);
        assert!(config.enable_independence);
    }

    #[test]
    fn test_optimizer_pipeline_end_to_end() {
        let mut opt = Optimizer::with_defaults();

        // Query 1: (x > 0 AND y > 0) — solver, with independence split
        let f1 = Formula::And(vec![
            Formula::Gt(
                Box::new(Formula::Var("x".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            Formula::Gt(
                Box::new(Formula::Var("y".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
        ]);
        let r1 = opt.optimize_and_verify(&f1, mock_prove);
        assert!(r1.result.is_proved());
        assert!(r1.was_split);

        // Query 2: same formula — cache hit
        let r2 = opt.optimize_and_verify(&f1, mock_prove);
        assert_eq!(r2.stage, OptimizationStage::QueryCache);

        // Query 3: different formula — solver
        let f3 = Formula::Lt(
            Box::new(Formula::Var("z".into(), Sort::Int)),
            Box::new(Formula::Int(100)),
        );
        let r3 = opt.optimize_and_verify(&f3, mock_prove);
        assert_eq!(r3.stage, OptimizationStage::Solver);

        let stats = opt.stats();
        assert_eq!(stats.total_queries, 3);
        assert_eq!(stats.cache_short_circuits, 1);
        assert_eq!(stats.independence_splits, 1);
    }
}
