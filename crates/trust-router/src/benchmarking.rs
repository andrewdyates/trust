// trust-router/benchmarking.rs: Solver benchmarking framework
//
// Framework for comparing solver performance on different VC types.
// Complements solver_benchmark.rs (which benchmarks VerificationBackend
// implementations on full VCs) by providing formula-string-level benchmarks
// for raw solver comparison.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;
use std::time::Instant;

/// Category of benchmark for classifying formula types.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum BenchmarkCategory {
    /// Linear and nonlinear integer/real arithmetic.
    Arithmetic,
    /// Fixed-width bitvector operations.
    BitVector,
    /// Array theory (select/store).
    Array,
    /// Quantified formulas (forall/exists).
    Quantifier,
    /// Combination of multiple theories.
    Combination,
    /// User-defined category.
    Custom(String),
}

impl BenchmarkCategory {
    /// Return a display-friendly label for this category.
    #[must_use]
    pub fn label(&self) -> &str {
        match self {
            Self::Arithmetic => "arithmetic",
            Self::BitVector => "bitvector",
            Self::Array => "array",
            Self::Quantifier => "quantifier",
            Self::Combination => "combination",
            Self::Custom(s) => s.as_str(),
        }
    }
}

/// Expected result for a benchmark formula.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ExpectedResult {
    /// Formula is satisfiable.
    Sat,
    /// Formula is unsatisfiable.
    Unsat,
    /// Result is unknown or undecidable.
    Unknown,
    /// Any result is acceptable (performance-only benchmark).
    Any,
}

/// Outcome from running a solver on a benchmark.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SolverOutcome {
    /// Solver determined satisfiability.
    Sat,
    /// Solver determined unsatisfiability.
    Unsat,
    /// Solver returned unknown.
    Unknown,
    /// Solver exceeded time limit.
    Timeout,
    /// Solver encountered an error.
    Error(String),
}

impl SolverOutcome {
    /// Whether the outcome matches the expected result.
    #[must_use]
    pub fn matches_expected(&self, expected: &ExpectedResult) -> bool {
        match expected {
            ExpectedResult::Any => true,
            ExpectedResult::Sat => *self == SolverOutcome::Sat,
            ExpectedResult::Unsat => *self == SolverOutcome::Unsat,
            ExpectedResult::Unknown => *self == SolverOutcome::Unknown,
        }
    }

    /// Whether this outcome represents a definite answer (not timeout/error).
    #[must_use]
    pub fn is_definite(&self) -> bool {
        matches!(self, SolverOutcome::Sat | SolverOutcome::Unsat)
    }
}

/// A single benchmark: a formula string with metadata.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Benchmark {
    /// Human-readable name for this benchmark.
    pub name: String,
    /// The benchmark category.
    pub category: BenchmarkCategory,
    /// SMT-LIB formula string or equivalent representation.
    pub formula: String,
    /// What result we expect from a correct solver.
    pub expected_result: ExpectedResult,
    /// Maximum time in milliseconds before declaring timeout.
    pub timeout_ms: u64,
}

/// A named collection of benchmarks.
#[derive(Debug, Clone)]
pub struct BenchmarkSuite {
    /// Suite name.
    pub name: String,
    /// Benchmarks in this suite.
    pub benchmarks: Vec<Benchmark>,
}

impl BenchmarkSuite {
    /// Create a new empty suite.
    #[must_use]
    pub fn new(name: impl Into<String>) -> Self {
        Self { name: name.into(), benchmarks: Vec::new() }
    }

    /// Add a benchmark to this suite.
    pub fn add(&mut self, benchmark: Benchmark) {
        self.benchmarks.push(benchmark);
    }

    /// Number of benchmarks.
    #[must_use]
    pub fn len(&self) -> usize {
        self.benchmarks.len()
    }

    /// Whether the suite is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.benchmarks.is_empty()
    }
}

/// Result of running a single benchmark against a specific solver.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BenchmarkResult {
    /// Name of the benchmark that was run.
    pub benchmark_name: String,
    /// Name of the solver that ran it.
    pub solver_name: String,
    /// Outcome from the solver.
    pub result: SolverOutcome,
    /// Wall-clock time in milliseconds.
    pub time_ms: u64,
    /// Memory usage in bytes, if available.
    pub memory_bytes: Option<u64>,
}

/// Aggregated report from running a suite.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BenchmarkReport {
    /// Total benchmarks executed.
    pub total: usize,
    /// Total wall-clock time across all benchmarks.
    pub total_time_ms: u64,
    /// Count of benchmarks per category label.
    pub by_category: FxHashMap<String, usize>,
    /// Solver with the lowest total time, if any.
    pub fastest_solver: Option<String>,
}

/// Comparison of two solvers on the same benchmarks.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ComparisonReport {
    /// Name of the first solver.
    pub solver_a: String,
    /// Name of the second solver.
    pub solver_b: String,
    /// Number of benchmarks where solver A was faster.
    pub a_wins: usize,
    /// Number of benchmarks where solver B was faster.
    pub b_wins: usize,
    /// Number of benchmarks where both had equal time.
    pub ties: usize,
}

/// Runner that manages suites and executes benchmarks.
///
/// In production, `run_benchmark` and `run_suite` simulate solver execution
/// by mapping formula strings to `SolverOutcome` via simple heuristics.
/// Real solver integration replaces these with actual SMT solver calls.
pub struct BenchmarkRunner {
    suites: Vec<BenchmarkSuite>,
}

impl BenchmarkRunner {
    /// Create a new empty runner.
    #[must_use]
    pub fn new() -> Self {
        Self { suites: Vec::new() }
    }

    /// Register a benchmark suite.
    pub fn add_suite(&mut self, suite: BenchmarkSuite) {
        self.suites.push(suite);
    }

    /// Get a reference to all registered suites.
    #[must_use]
    pub fn suites(&self) -> &[BenchmarkSuite] {
        &self.suites
    }

    /// Run a single benchmark against a named solver.
    ///
    /// Uses a built-in heuristic solver stub. In production, this would
    /// dispatch to the actual solver binary/library.
    #[must_use]
    pub fn run_benchmark(&self, benchmark: &Benchmark, solver: &str) -> BenchmarkResult {
        let start = Instant::now();
        let result = simulate_solver(benchmark, solver);
        let elapsed_ms = start.elapsed().as_millis() as u64;

        BenchmarkResult {
            benchmark_name: benchmark.name.clone(),
            solver_name: solver.to_string(),
            result,
            time_ms: elapsed_ms,
            memory_bytes: None,
        }
    }

    /// Run all benchmarks in a named suite.
    ///
    /// Returns an empty vec if the suite name is not found.
    #[must_use]
    pub fn run_suite(&self, suite_name: &str) -> Vec<BenchmarkResult> {
        let suite = match self.suites.iter().find(|s| s.name == suite_name) {
            Some(s) => s,
            None => return Vec::new(),
        };

        // Run each benchmark against a default "stub" solver.
        suite
            .benchmarks
            .iter()
            .map(|b| self.run_benchmark(b, "stub"))
            .collect()
    }

    /// Compare results from two solvers on the same benchmarks.
    ///
    /// Pairs results by benchmark name. Benchmarks present in only one
    /// set are ignored.
    #[must_use]
    pub fn compare_solvers(
        &self,
        results_a: &[BenchmarkResult],
        results_b: &[BenchmarkResult],
    ) -> ComparisonReport {
        let solver_a = results_a
            .first()
            .map(|r| r.solver_name.clone())
            .unwrap_or_default();
        let solver_b = results_b
            .first()
            .map(|r| r.solver_name.clone())
            .unwrap_or_default();

        let map_b: FxHashMap<&str, &BenchmarkResult> =
            results_b.iter().map(|r| (r.benchmark_name.as_str(), r)).collect();

        let mut a_wins = 0usize;
        let mut b_wins = 0usize;
        let mut ties = 0usize;

        for ra in results_a {
            if let Some(rb) = map_b.get(ra.benchmark_name.as_str()) {
                match ra.time_ms.cmp(&rb.time_ms) {
                    std::cmp::Ordering::Less => a_wins += 1,
                    std::cmp::Ordering::Greater => b_wins += 1,
                    std::cmp::Ordering::Equal => ties += 1,
                }
            }
        }

        ComparisonReport { solver_a, solver_b, a_wins, b_wins, ties }
    }

    /// Generate an aggregated report from benchmark results.
    #[must_use]
    pub fn generate_report(&self, results: &[BenchmarkResult]) -> BenchmarkReport {
        let total = results.len();
        let total_time_ms: u64 = results.iter().map(|r| r.time_ms).sum();

        // Build category counts by looking up benchmarks from registered suites.
        let mut by_category: FxHashMap<String, usize> = FxHashMap::default();
        for r in results {
            let cat_label = self.find_category(&r.benchmark_name);
            *by_category.entry(cat_label).or_insert(0) += 1;
        }

        // Find the fastest solver by total time.
        let mut solver_times: FxHashMap<&str, u64> = FxHashMap::default();
        for r in results {
            *solver_times.entry(r.solver_name.as_str()).or_insert(0) += r.time_ms;
        }
        let fastest_solver = solver_times
            .into_iter()
            .min_by_key(|(_, t)| *t)
            .map(|(name, _)| name.to_string());

        BenchmarkReport { total, total_time_ms, by_category, fastest_solver }
    }

    /// Look up the category label for a benchmark by name.
    fn find_category(&self, benchmark_name: &str) -> String {
        for suite in &self.suites {
            for b in &suite.benchmarks {
                if b.name == benchmark_name {
                    return b.category.label().to_string();
                }
            }
        }
        "unknown".to_string()
    }
}

impl Default for BenchmarkRunner {
    fn default() -> Self {
        Self::new()
    }
}

/// Simulate a solver result from a formula string.
///
/// This stub interprets simple formula patterns:
/// - "unsat" in the formula -> Unsat
/// - "sat" in the formula -> Sat
/// - "error" in the formula -> Error
/// - otherwise -> Unknown
///
/// Real integration would call z4, sunder, etc.
fn simulate_solver(benchmark: &Benchmark, _solver: &str) -> SolverOutcome {
    let formula_lower = benchmark.formula.to_lowercase();
    if formula_lower.contains("unsat") {
        SolverOutcome::Unsat
    } else if formula_lower.contains("error") {
        SolverOutcome::Error("simulated error".to_string())
    } else if formula_lower.contains("sat") {
        SolverOutcome::Sat
    } else {
        SolverOutcome::Unknown
    }
}

/// Create a standard arithmetic benchmark suite.
#[must_use]
pub fn standard_arithmetic_suite() -> BenchmarkSuite {
    let mut suite = BenchmarkSuite::new("standard-arithmetic");
    suite.add(Benchmark {
        name: "arith_add_sat".to_string(),
        category: BenchmarkCategory::Arithmetic,
        formula: "(assert (= (+ x 1) 2)) ; sat".to_string(),
        expected_result: ExpectedResult::Sat,
        timeout_ms: 5000,
    });
    suite.add(Benchmark {
        name: "arith_mul_sat".to_string(),
        category: BenchmarkCategory::Arithmetic,
        formula: "(assert (= (* x 3) 9)) ; sat".to_string(),
        expected_result: ExpectedResult::Sat,
        timeout_ms: 5000,
    });
    suite.add(Benchmark {
        name: "arith_contradiction_unsat".to_string(),
        category: BenchmarkCategory::Arithmetic,
        formula: "(assert (and (> x 0) (< x 0))) ; unsat".to_string(),
        expected_result: ExpectedResult::Unsat,
        timeout_ms: 5000,
    });
    suite.add(Benchmark {
        name: "arith_nonlinear_sat".to_string(),
        category: BenchmarkCategory::Arithmetic,
        formula: "(assert (= (* x x) 4)) ; sat".to_string(),
        expected_result: ExpectedResult::Sat,
        timeout_ms: 10000,
    });
    suite.add(Benchmark {
        name: "arith_div_unsat".to_string(),
        category: BenchmarkCategory::Arithmetic,
        formula: "(assert (and (= (div x 2) 3) (= x 5))) ; unsat".to_string(),
        expected_result: ExpectedResult::Unsat,
        timeout_ms: 5000,
    });
    suite
}

/// Create a standard bitvector benchmark suite.
#[must_use]
pub fn standard_bitvector_suite() -> BenchmarkSuite {
    let mut suite = BenchmarkSuite::new("standard-bitvector");
    suite.add(Benchmark {
        name: "bv_and_sat".to_string(),
        category: BenchmarkCategory::BitVector,
        formula: "(assert (= (bvand x #xFF) x)) ; sat".to_string(),
        expected_result: ExpectedResult::Sat,
        timeout_ms: 5000,
    });
    suite.add(Benchmark {
        name: "bv_overflow_unsat".to_string(),
        category: BenchmarkCategory::BitVector,
        formula: "(assert (bvult (bvadd x #x01) x)) ; unsat for 8-bit when x=#xFF, but generally unsat".to_string(),
        expected_result: ExpectedResult::Unsat,
        timeout_ms: 5000,
    });
    suite.add(Benchmark {
        name: "bv_shift_sat".to_string(),
        category: BenchmarkCategory::BitVector,
        formula: "(assert (= (bvshl x #x01) #x02)) ; sat".to_string(),
        expected_result: ExpectedResult::Sat,
        timeout_ms: 5000,
    });
    suite.add(Benchmark {
        name: "bv_xor_identity_sat".to_string(),
        category: BenchmarkCategory::BitVector,
        formula: "(assert (= (bvxor x x) #x00)) ; sat (always true)".to_string(),
        expected_result: ExpectedResult::Sat,
        timeout_ms: 5000,
    });
    suite.add(Benchmark {
        name: "bv_concat_unsat".to_string(),
        category: BenchmarkCategory::BitVector,
        formula: "(assert (and (= (concat a b) #xFFFF) (= a #x00))) ; unsat".to_string(),
        expected_result: ExpectedResult::Unsat,
        timeout_ms: 5000,
    });
    suite
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_benchmark(name: &str, formula: &str, expected: ExpectedResult) -> Benchmark {
        Benchmark {
            name: name.to_string(),
            category: BenchmarkCategory::Arithmetic,
            formula: formula.to_string(),
            expected_result: expected,
            timeout_ms: 1000,
        }
    }

    // --- BenchmarkCategory tests ---

    #[test]
    fn test_benchmark_category_label() {
        assert_eq!(BenchmarkCategory::Arithmetic.label(), "arithmetic");
        assert_eq!(BenchmarkCategory::BitVector.label(), "bitvector");
        assert_eq!(BenchmarkCategory::Array.label(), "array");
        assert_eq!(BenchmarkCategory::Quantifier.label(), "quantifier");
        assert_eq!(BenchmarkCategory::Combination.label(), "combination");
        assert_eq!(BenchmarkCategory::Custom("my-cat".to_string()).label(), "my-cat");
    }

    #[test]
    fn test_benchmark_category_eq() {
        assert_eq!(BenchmarkCategory::Arithmetic, BenchmarkCategory::Arithmetic);
        assert_ne!(BenchmarkCategory::Arithmetic, BenchmarkCategory::BitVector);
        assert_eq!(
            BenchmarkCategory::Custom("x".to_string()),
            BenchmarkCategory::Custom("x".to_string()),
        );
        assert_ne!(
            BenchmarkCategory::Custom("x".to_string()),
            BenchmarkCategory::Custom("y".to_string()),
        );
    }

    // --- SolverOutcome tests ---

    #[test]
    fn test_solver_outcome_matches_expected() {
        assert!(SolverOutcome::Sat.matches_expected(&ExpectedResult::Sat));
        assert!(!SolverOutcome::Sat.matches_expected(&ExpectedResult::Unsat));
        assert!(SolverOutcome::Unsat.matches_expected(&ExpectedResult::Unsat));
        assert!(SolverOutcome::Unknown.matches_expected(&ExpectedResult::Unknown));
        // Any matches everything
        assert!(SolverOutcome::Sat.matches_expected(&ExpectedResult::Any));
        assert!(SolverOutcome::Timeout.matches_expected(&ExpectedResult::Any));
        assert!(SolverOutcome::Error("e".to_string()).matches_expected(&ExpectedResult::Any));
    }

    #[test]
    fn test_solver_outcome_is_definite() {
        assert!(SolverOutcome::Sat.is_definite());
        assert!(SolverOutcome::Unsat.is_definite());
        assert!(!SolverOutcome::Unknown.is_definite());
        assert!(!SolverOutcome::Timeout.is_definite());
        assert!(!SolverOutcome::Error("e".to_string()).is_definite());
    }

    // --- BenchmarkSuite tests ---

    #[test]
    fn test_benchmark_suite_new_empty() {
        let suite = BenchmarkSuite::new("test");
        assert_eq!(suite.name, "test");
        assert!(suite.is_empty());
        assert_eq!(suite.len(), 0);
    }

    #[test]
    fn test_benchmark_suite_add() {
        let mut suite = BenchmarkSuite::new("s");
        suite.add(make_benchmark("b1", "sat formula", ExpectedResult::Sat));
        suite.add(make_benchmark("b2", "unsat formula", ExpectedResult::Unsat));
        assert_eq!(suite.len(), 2);
        assert!(!suite.is_empty());
        assert_eq!(suite.benchmarks[0].name, "b1");
        assert_eq!(suite.benchmarks[1].name, "b2");
    }

    // --- BenchmarkRunner tests ---

    #[test]
    fn test_runner_new_is_empty() {
        let runner = BenchmarkRunner::new();
        assert!(runner.suites().is_empty());
    }

    #[test]
    fn test_runner_default_is_empty() {
        let runner = BenchmarkRunner::default();
        assert!(runner.suites().is_empty());
    }

    #[test]
    fn test_runner_add_suite() {
        let mut runner = BenchmarkRunner::new();
        runner.add_suite(BenchmarkSuite::new("s1"));
        runner.add_suite(BenchmarkSuite::new("s2"));
        assert_eq!(runner.suites().len(), 2);
    }

    #[test]
    fn test_runner_run_benchmark_sat() {
        let runner = BenchmarkRunner::new();
        let b = make_benchmark("test_sat", "x > 0 sat", ExpectedResult::Sat);
        let result = runner.run_benchmark(&b, "z4");

        assert_eq!(result.benchmark_name, "test_sat");
        assert_eq!(result.solver_name, "z4");
        assert_eq!(result.result, SolverOutcome::Sat);
        assert!(result.memory_bytes.is_none());
    }

    #[test]
    fn test_runner_run_benchmark_unsat() {
        let runner = BenchmarkRunner::new();
        let b = make_benchmark("test_unsat", "contradiction unsat", ExpectedResult::Unsat);
        let result = runner.run_benchmark(&b, "sunder");

        assert_eq!(result.result, SolverOutcome::Unsat);
        assert_eq!(result.solver_name, "sunder");
    }

    #[test]
    fn test_runner_run_benchmark_unknown() {
        let runner = BenchmarkRunner::new();
        let b = make_benchmark("test_unknown", "opaque formula", ExpectedResult::Unknown);
        let result = runner.run_benchmark(&b, "z4");

        assert_eq!(result.result, SolverOutcome::Unknown);
    }

    #[test]
    fn test_runner_run_benchmark_error() {
        let runner = BenchmarkRunner::new();
        let b = make_benchmark("test_error", "trigger error", ExpectedResult::Any);
        let result = runner.run_benchmark(&b, "z4");

        assert!(matches!(result.result, SolverOutcome::Error(_)));
    }

    #[test]
    fn test_runner_run_suite() {
        let mut runner = BenchmarkRunner::new();
        let mut suite = BenchmarkSuite::new("my-suite");
        suite.add(make_benchmark("b1", "x sat", ExpectedResult::Sat));
        suite.add(make_benchmark("b2", "y unsat", ExpectedResult::Unsat));
        runner.add_suite(suite);

        let results = runner.run_suite("my-suite");
        assert_eq!(results.len(), 2);
        assert_eq!(results[0].benchmark_name, "b1");
        assert_eq!(results[1].benchmark_name, "b2");
    }

    #[test]
    fn test_runner_run_suite_not_found() {
        let runner = BenchmarkRunner::new();
        let results = runner.run_suite("nonexistent");
        assert!(results.is_empty());
    }

    #[test]
    fn test_runner_compare_solvers() {
        let runner = BenchmarkRunner::new();
        let results_a = vec![
            BenchmarkResult {
                benchmark_name: "b1".to_string(),
                solver_name: "solver_a".to_string(),
                result: SolverOutcome::Sat,
                time_ms: 10,
                memory_bytes: None,
            },
            BenchmarkResult {
                benchmark_name: "b2".to_string(),
                solver_name: "solver_a".to_string(),
                result: SolverOutcome::Unsat,
                time_ms: 50,
                memory_bytes: None,
            },
            BenchmarkResult {
                benchmark_name: "b3".to_string(),
                solver_name: "solver_a".to_string(),
                result: SolverOutcome::Sat,
                time_ms: 20,
                memory_bytes: None,
            },
        ];
        let results_b = vec![
            BenchmarkResult {
                benchmark_name: "b1".to_string(),
                solver_name: "solver_b".to_string(),
                result: SolverOutcome::Sat,
                time_ms: 20,
                memory_bytes: None,
            },
            BenchmarkResult {
                benchmark_name: "b2".to_string(),
                solver_name: "solver_b".to_string(),
                result: SolverOutcome::Unsat,
                time_ms: 30,
                memory_bytes: None,
            },
            BenchmarkResult {
                benchmark_name: "b3".to_string(),
                solver_name: "solver_b".to_string(),
                result: SolverOutcome::Sat,
                time_ms: 20,
                memory_bytes: None,
            },
        ];

        let report = runner.compare_solvers(&results_a, &results_b);
        assert_eq!(report.solver_a, "solver_a");
        assert_eq!(report.solver_b, "solver_b");
        assert_eq!(report.a_wins, 1);  // b1: 10 < 20
        assert_eq!(report.b_wins, 1);  // b2: 50 > 30
        assert_eq!(report.ties, 1);    // b3: 20 == 20
    }

    #[test]
    fn test_runner_compare_solvers_empty() {
        let runner = BenchmarkRunner::new();
        let report = runner.compare_solvers(&[], &[]);
        assert_eq!(report.a_wins, 0);
        assert_eq!(report.b_wins, 0);
        assert_eq!(report.ties, 0);
    }

    #[test]
    fn test_runner_generate_report() {
        let mut runner = BenchmarkRunner::new();
        let mut suite = BenchmarkSuite::new("s");
        suite.add(Benchmark {
            name: "arith1".to_string(),
            category: BenchmarkCategory::Arithmetic,
            formula: "sat".to_string(),
            expected_result: ExpectedResult::Sat,
            timeout_ms: 1000,
        });
        suite.add(Benchmark {
            name: "bv1".to_string(),
            category: BenchmarkCategory::BitVector,
            formula: "sat".to_string(),
            expected_result: ExpectedResult::Sat,
            timeout_ms: 1000,
        });
        runner.add_suite(suite);

        let results = vec![
            BenchmarkResult {
                benchmark_name: "arith1".to_string(),
                solver_name: "z4".to_string(),
                result: SolverOutcome::Sat,
                time_ms: 10,
                memory_bytes: None,
            },
            BenchmarkResult {
                benchmark_name: "bv1".to_string(),
                solver_name: "z4".to_string(),
                result: SolverOutcome::Sat,
                time_ms: 20,
                memory_bytes: None,
            },
        ];

        let report = runner.generate_report(&results);
        assert_eq!(report.total, 2);
        assert_eq!(report.total_time_ms, 30);
        assert_eq!(report.by_category.get("arithmetic"), Some(&1));
        assert_eq!(report.by_category.get("bitvector"), Some(&1));
        assert_eq!(report.fastest_solver, Some("z4".to_string()));
    }

    #[test]
    fn test_runner_generate_report_empty() {
        let runner = BenchmarkRunner::new();
        let report = runner.generate_report(&[]);
        assert_eq!(report.total, 0);
        assert_eq!(report.total_time_ms, 0);
        assert!(report.by_category.is_empty());
        assert!(report.fastest_solver.is_none());
    }

    // --- Standard suite tests ---

    #[test]
    fn test_standard_arithmetic_suite() {
        let suite = standard_arithmetic_suite();
        assert_eq!(suite.name, "standard-arithmetic");
        assert_eq!(suite.len(), 5);
        for b in &suite.benchmarks {
            assert_eq!(b.category, BenchmarkCategory::Arithmetic);
            assert!(b.timeout_ms > 0);
            assert!(!b.formula.is_empty());
        }
    }

    #[test]
    fn test_standard_bitvector_suite() {
        let suite = standard_bitvector_suite();
        assert_eq!(suite.name, "standard-bitvector");
        assert_eq!(suite.len(), 5);
        for b in &suite.benchmarks {
            assert_eq!(b.category, BenchmarkCategory::BitVector);
            assert!(b.timeout_ms > 0);
            assert!(!b.formula.is_empty());
        }
    }

    #[test]
    fn test_standard_suites_run_through_runner() {
        let mut runner = BenchmarkRunner::new();
        runner.add_suite(standard_arithmetic_suite());
        runner.add_suite(standard_bitvector_suite());

        let arith_results = runner.run_suite("standard-arithmetic");
        assert_eq!(arith_results.len(), 5);

        let bv_results = runner.run_suite("standard-bitvector");
        assert_eq!(bv_results.len(), 5);

        // All results should have the stub solver name
        for r in arith_results.iter().chain(bv_results.iter()) {
            assert_eq!(r.solver_name, "stub");
        }
    }
}
