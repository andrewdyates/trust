// trust-driver/benchmark.rs: Reproducible verification pipeline benchmarks
//
// Defines benchmark scenarios for profiling the verification pipeline.
// Each `BenchmarkScenario` specifies a workload (function count, VC count,
// expected cache behavior) and can be run against the profiled pipeline
// to produce a `BenchmarkResult` with stage-by-stage timing breakdown.
//
// Part of #670: Profile verification pipeline baseline before optimization
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::fmt;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use crate::profiling::{PipelineProfile, PipelineProfiler, PipelineStage};
use crate::{
    BackpropOutput, BackpropPhase, ProofFrontier, StrengthenPhase, VerifyOutput, VerifyPhase,
};
use trust_strengthen::StrengthenOutput;

// ---------------------------------------------------------------------------
// Benchmark scenario definition
// ---------------------------------------------------------------------------

/// Defines a reproducible benchmark workload for the verification pipeline.
#[derive(Debug, Clone)]
pub(crate) struct BenchmarkScenario {
    /// Human-readable name for this scenario.
    pub name: String,
    /// Description of what this scenario exercises.
    pub description: String,
    /// Number of functions to simulate.
    pub function_count: usize,
    /// Number of VCs per function (average).
    pub vcs_per_function: usize,
    /// Fraction of VCs that succeed on first pass (0.0 to 1.0).
    pub success_rate: f64,
    /// Simulated solver latency per VC.
    pub solver_latency: Duration,
    /// Simulated cache hit rate (0.0 to 1.0).
    pub cache_hit_rate: f64,
    /// Number of pipeline iterations to run.
    pub iterations: u32,
    /// Whether to simulate strengthening proposals.
    pub simulate_strengthening: bool,
}

impl BenchmarkScenario {
    /// Total VC count for this scenario.
    #[must_use]
    pub(crate) fn total_vcs(&self) -> usize {
        self.function_count * self.vcs_per_function
    }

    /// Expected number of proved VCs on first pass.
    #[must_use]
    pub(crate) fn expected_proved(&self) -> usize {
        (self.total_vcs() as f64 * self.success_rate) as usize
    }

    /// Expected number of failed VCs on first pass.
    #[must_use]
    pub(crate) fn expected_failed(&self) -> usize {
        self.total_vcs() - self.expected_proved()
    }

    /// Standard scenario: small crate verification.
    #[must_use]
    pub(crate) fn small_crate() -> Self {
        Self {
            name: "small_crate".into(),
            description: "Small crate: 20 functions, ~7 VCs each, 80% success rate".into(),
            function_count: 20,
            vcs_per_function: 7,
            success_rate: 0.8,
            solver_latency: Duration::from_millis(10),
            cache_hit_rate: 0.0,
            iterations: 3,
            simulate_strengthening: true,
        }
    }

    /// Standard scenario: medium crate verification.
    #[must_use]
    pub(crate) fn medium_crate() -> Self {
        Self {
            name: "medium_crate".into(),
            description: "Medium crate: 100 functions, ~10 VCs each, 70% success rate".into(),
            function_count: 100,
            vcs_per_function: 10,
            success_rate: 0.7,
            solver_latency: Duration::from_millis(15),
            cache_hit_rate: 0.3,
            iterations: 5,
            simulate_strengthening: true,
        }
    }

    /// Standard scenario: large crate verification.
    #[must_use]
    pub(crate) fn large_crate() -> Self {
        Self {
            name: "large_crate".into(),
            description: "Large crate: 200 functions, ~15 VCs each, 60% success rate".into(),
            function_count: 200,
            vcs_per_function: 15,
            success_rate: 0.6,
            solver_latency: Duration::from_millis(20),
            cache_hit_rate: 0.5,
            iterations: 8,
            simulate_strengthening: true,
        }
    }

    /// Standard scenario: cache-heavy re-verification.
    #[must_use]
    pub(crate) fn cache_heavy() -> Self {
        Self {
            name: "cache_heavy".into(),
            description: "Re-verification with high cache hit rate: 100 functions, 90% cache hits"
                .into(),
            function_count: 100,
            vcs_per_function: 10,
            success_rate: 0.9,
            solver_latency: Duration::from_millis(15),
            cache_hit_rate: 0.9,
            iterations: 2,
            simulate_strengthening: false,
        }
    }

    /// All standard scenarios.
    #[must_use]
    pub(crate) fn all_standard() -> Vec<Self> {
        vec![
            Self::small_crate(),
            Self::medium_crate(),
            Self::large_crate(),
            Self::cache_heavy(),
        ]
    }
}

impl fmt::Display for BenchmarkScenario {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}: {} ({} functions, {} VCs total, {:.0}% success)",
            self.name,
            self.description,
            self.function_count,
            self.total_vcs(),
            self.success_rate * 100.0,
        )
    }
}

// ---------------------------------------------------------------------------
// Benchmark result
// ---------------------------------------------------------------------------

/// Result of running a benchmark scenario.
#[derive(Debug, Clone)]
pub(crate) struct BenchmarkResult {
    /// Which scenario was run.
    pub scenario_name: String,
    /// Profiling data from the run.
    pub profile: PipelineProfile,
    /// Wall-clock time for the entire benchmark (includes overhead).
    pub wall_clock: Duration,
    /// Number of iterations actually executed.
    pub iterations_run: u32,
}

impl BenchmarkResult {
    /// Throughput: VCs dispatched per second.
    #[must_use]
    pub(crate) fn vc_throughput(&self) -> f64 {
        let secs = self.wall_clock.as_secs_f64();
        if secs == 0.0 {
            return 0.0;
        }
        self.profile.total_vcs_dispatched as f64 / secs
    }

    /// Time per VC in milliseconds.
    #[must_use]
    pub(crate) fn ms_per_vc(&self) -> f64 {
        if self.profile.total_vcs_dispatched == 0 {
            return 0.0;
        }
        (self.wall_clock.as_secs_f64() * 1000.0) / self.profile.total_vcs_dispatched as f64
    }
}

impl fmt::Display for BenchmarkResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "=== Benchmark: {} ===", self.scenario_name)?;
        writeln!(
            f,
            "Wall clock: {:.1}ms",
            self.wall_clock.as_secs_f64() * 1000.0
        )?;
        writeln!(f, "Iterations: {}", self.iterations_run)?;
        writeln!(f, "Throughput: {:.1} VCs/sec", self.vc_throughput())?;
        writeln!(f, "Latency:   {:.2} ms/VC", self.ms_per_vc())?;
        writeln!(f)?;
        write!(f, "{}", self.profile)?;
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// Benchmark runner
// ---------------------------------------------------------------------------

/// Runs benchmark scenarios against the verification pipeline.
pub(crate) struct BenchmarkRunner;

impl BenchmarkRunner {
    /// Run a single benchmark scenario and return the result.
    #[must_use]
    pub(crate) fn run(scenario: &BenchmarkScenario) -> BenchmarkResult {
        let profiler = PipelineProfiler::new();
        let start = Instant::now();

        let verify = ScenarioVerifyPhase::new(scenario);
        let strengthen = ScenarioStrengthenPhase::new(scenario);
        let backprop = ScenarioBackpropPhase;

        for iter in 0..scenario.iterations {
            // Simulate verify phase
            let verify_start = Instant::now();
            let v_out = verify.verify(&PathBuf::from("/benchmark"));
            let verify_elapsed = verify_start.elapsed();

            profiler.record_timing(
                PipelineStage::SolverDispatch,
                verify_elapsed,
                Some(v_out.vcs_dispatched),
            );
            profiler.record_vcs_dispatched(v_out.vcs_dispatched);
            profiler.record_vcs_generated(v_out.vcs_dispatched);

            // Simulate cache
            let cache_hits =
                (v_out.vcs_dispatched as f64 * scenario.cache_hit_rate) as usize;
            let cache_misses = v_out.vcs_dispatched - cache_hits;
            profiler.record_cache_stats(cache_hits, cache_misses);

            if v_out.vcs_failed == 0 {
                break;
            }

            // Simulate strengthen phase
            if scenario.simulate_strengthening {
                let strengthen_start = Instant::now();
                let s_out = strengthen.strengthen(&PathBuf::from("/benchmark"), &v_out);
                let strengthen_elapsed = strengthen_start.elapsed();

                profiler.record_timing(
                    PipelineStage::Strengthening,
                    strengthen_elapsed,
                    None,
                );

                if s_out.has_proposals {
                    let backprop_start = Instant::now();
                    let b_out =
                        backprop.backpropagate(&PathBuf::from("/benchmark"), &s_out.proposals);
                    let backprop_elapsed = backprop_start.elapsed();

                    profiler.record_timing(
                        PipelineStage::Backprop,
                        backprop_elapsed,
                        None,
                    );
                    profiler.record_proposals(s_out.proposals.len(), b_out.applied);
                }
            }

            if iter + 1 < scenario.iterations {
                profiler.next_iteration();
            }
        }

        let wall_clock = start.elapsed();
        let profile = profiler.finalize();

        BenchmarkResult {
            scenario_name: scenario.name.clone(),
            profile,
            wall_clock,
            iterations_run: scenario.iterations,
        }
    }

    /// Run all standard benchmark scenarios and return results.
    #[must_use]
    pub(crate) fn run_all_standard() -> Vec<BenchmarkResult> {
        BenchmarkScenario::all_standard()
            .iter()
            .map(Self::run)
            .collect()
    }

    /// Print a comparative summary of multiple benchmark results.
    pub(crate) fn print_comparison(results: &[BenchmarkResult]) {
        println!("=== Pipeline Benchmark Comparison ===");
        println!("{:<20} {:>10} {:>10} {:>10} {:>10} {:>10}",
            "Scenario", "Wall(ms)", "VCs", "VCs/sec", "ms/VC", "Cache%");
        println!("{}", "-".repeat(70));
        for r in results {
            println!(
                "{:<20} {:>10.1} {:>10} {:>10.1} {:>10.2} {:>10.1}",
                r.scenario_name,
                r.wall_clock.as_secs_f64() * 1000.0,
                r.profile.total_vcs_dispatched,
                r.vc_throughput(),
                r.ms_per_vc(),
                r.profile.cache_hit_rate(),
            );
        }
    }
}

// ---------------------------------------------------------------------------
// Scenario-driven mock phases
// ---------------------------------------------------------------------------

/// Verify phase that simulates solver dispatch based on scenario parameters.
struct ScenarioVerifyPhase {
    total_vcs: usize,
    proved: usize,
    failed: usize,
    solver_latency: Duration,
}

impl ScenarioVerifyPhase {
    fn new(scenario: &BenchmarkScenario) -> Self {
        let total_vcs = scenario.total_vcs();
        let proved = scenario.expected_proved();
        let failed = total_vcs - proved;
        Self {
            total_vcs,
            proved,
            failed,
            solver_latency: scenario.solver_latency,
        }
    }
}

impl VerifyPhase for ScenarioVerifyPhase {
    fn verify(&self, _: &Path) -> VerifyOutput {
        // Simulate solver latency (scaled down to avoid slow benchmarks)
        let simulated = Duration::from_nanos(
            (self.solver_latency.as_nanos() as f64 * (self.total_vcs as f64).sqrt()) as u64,
        );
        std::thread::sleep(simulated.min(Duration::from_millis(50)));

        VerifyOutput {
            frontier: ProofFrontier {
                trusted: self.proved as u32,
                certified: 0,
                runtime_checked: 0,
                failed: self.failed as u32,
                unknown: 0,
            },
            fingerprint: None,
            vcs_dispatched: self.total_vcs,
            vcs_failed: self.failed,
            detailed_results: None,
        }
    }
}

/// Strengthen phase that simulates proposal generation.
struct ScenarioStrengthenPhase {
    proposals_per_failure: usize,
}

impl ScenarioStrengthenPhase {
    fn new(scenario: &BenchmarkScenario) -> Self {
        Self {
            proposals_per_failure: if scenario.simulate_strengthening {
                1
            } else {
                0
            },
        }
    }
}

impl StrengthenPhase for ScenarioStrengthenPhase {
    fn strengthen(&self, _: &Path, verify_output: &VerifyOutput) -> StrengthenOutput {
        // Simulate analysis time (proportional to failures)
        let simulated = Duration::from_micros(100 * verify_output.vcs_failed as u64);
        std::thread::sleep(simulated.min(Duration::from_millis(10)));

        let proposal_count = verify_output.vcs_failed * self.proposals_per_failure;
        let proposals: Vec<trust_strengthen::Proposal> = (0..proposal_count)
            .map(|i| trust_strengthen::Proposal {
                function_path: format!("bench::fn_{i}"),
                function_name: format!("fn_{i}"),
                kind: trust_strengthen::ProposalKind::AddPrecondition {
                    spec_body: format!("x > {i}"),
                },
                confidence: 0.7,
                rationale: format!("benchmark proposal {i}"),
            })
            .collect();

        StrengthenOutput {
            has_proposals: !proposals.is_empty(),
            failures_analyzed: verify_output.vcs_failed,
            proposals,
        }
    }
}

/// Backprop phase that simulates applying proposals.
struct ScenarioBackpropPhase;

impl BackpropPhase for ScenarioBackpropPhase {
    fn backpropagate(
        &self,
        _: &Path,
        proposals: &[trust_strengthen::Proposal],
    ) -> BackpropOutput {
        // Simulate write time
        std::thread::sleep(Duration::from_micros(50 * proposals.len() as u64));

        BackpropOutput {
            applied: proposals.len(),
            skipped: 0,
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_scenario_total_vcs() {
        let scenario = BenchmarkScenario {
            name: "test".into(),
            description: "test".into(),
            function_count: 10,
            vcs_per_function: 5,
            success_rate: 0.8,
            solver_latency: Duration::from_millis(1),
            cache_hit_rate: 0.0,
            iterations: 1,
            simulate_strengthening: false,
        };
        assert_eq!(scenario.total_vcs(), 50);
        assert_eq!(scenario.expected_proved(), 40);
        assert_eq!(scenario.expected_failed(), 10);
    }

    #[test]
    fn test_scenario_display() {
        let scenario = BenchmarkScenario::small_crate();
        let display = format!("{scenario}");
        assert!(display.contains("small_crate"));
        assert!(display.contains("20 functions"));
    }

    #[test]
    fn test_small_crate_scenario() {
        let s = BenchmarkScenario::small_crate();
        assert_eq!(s.function_count, 20);
        assert_eq!(s.vcs_per_function, 7);
        assert_eq!(s.total_vcs(), 140);
    }

    #[test]
    fn test_medium_crate_scenario() {
        let s = BenchmarkScenario::medium_crate();
        assert_eq!(s.function_count, 100);
        assert_eq!(s.total_vcs(), 1000);
    }

    #[test]
    fn test_large_crate_scenario() {
        let s = BenchmarkScenario::large_crate();
        assert_eq!(s.function_count, 200);
        assert_eq!(s.total_vcs(), 3000);
    }

    #[test]
    fn test_cache_heavy_scenario() {
        let s = BenchmarkScenario::cache_heavy();
        assert_eq!(s.cache_hit_rate, 0.9);
        assert!(!s.simulate_strengthening);
    }

    #[test]
    fn test_all_standard_scenarios() {
        let scenarios = BenchmarkScenario::all_standard();
        assert_eq!(scenarios.len(), 4);
    }

    #[test]
    fn test_run_small_benchmark() {
        let scenario = BenchmarkScenario {
            name: "unit_test".into(),
            description: "tiny benchmark for unit testing".into(),
            function_count: 2,
            vcs_per_function: 3,
            success_rate: 1.0, // all pass, single iteration
            solver_latency: Duration::from_millis(1),
            cache_hit_rate: 0.0,
            iterations: 1,
            simulate_strengthening: false,
        };

        let result = BenchmarkRunner::run(&scenario);

        assert_eq!(result.scenario_name, "unit_test");
        assert!(result.wall_clock > Duration::ZERO);
        assert_eq!(result.profile.total_vcs_dispatched, 6);
        assert!(result.vc_throughput() > 0.0);
    }

    #[test]
    fn test_run_benchmark_with_failures() {
        let scenario = BenchmarkScenario {
            name: "with_failures".into(),
            description: "benchmark with some failures".into(),
            function_count: 5,
            vcs_per_function: 4,
            success_rate: 0.5,
            solver_latency: Duration::from_millis(1),
            cache_hit_rate: 0.0,
            iterations: 2,
            simulate_strengthening: true,
        };

        let result = BenchmarkRunner::run(&scenario);

        assert_eq!(result.scenario_name, "with_failures");
        assert!(result.profile.total_proposals > 0);
        assert!(result.profile.total_applied > 0);
    }

    #[test]
    fn test_run_benchmark_with_cache() {
        let scenario = BenchmarkScenario {
            name: "cached".into(),
            description: "benchmark with cache hits".into(),
            function_count: 5,
            vcs_per_function: 4,
            success_rate: 1.0,
            solver_latency: Duration::from_millis(1),
            cache_hit_rate: 0.5,
            iterations: 1,
            simulate_strengthening: false,
        };

        let result = BenchmarkRunner::run(&scenario);

        assert_eq!(result.profile.total_cache_hits, 10); // 50% of 20
        assert_eq!(result.profile.total_cache_misses, 10);
        let rate = result.profile.cache_hit_rate();
        assert!((rate - 50.0).abs() < 0.01);
    }

    #[test]
    fn test_benchmark_result_display() {
        let scenario = BenchmarkScenario {
            name: "display_test".into(),
            description: "test display".into(),
            function_count: 3,
            vcs_per_function: 2,
            success_rate: 1.0,
            solver_latency: Duration::from_millis(1),
            cache_hit_rate: 0.0,
            iterations: 1,
            simulate_strengthening: false,
        };

        let result = BenchmarkRunner::run(&scenario);
        let display = format!("{result}");

        assert!(display.contains("display_test"));
        assert!(display.contains("Wall clock"));
        assert!(display.contains("Throughput"));
        assert!(display.contains("Pipeline Profile"));
    }

    #[test]
    fn test_vc_throughput_zero_time() {
        let result = BenchmarkResult {
            scenario_name: "zero".into(),
            profile: PipelineProfile {
                timings: Vec::new(),
                total_duration: Duration::ZERO,
                iterations: 0,
                total_vcs_generated: 0,
                total_vcs_dispatched: 0,
                total_cache_hits: 0,
                total_cache_misses: 0,
                total_proposals: 0,
                total_applied: 0,
            },
            wall_clock: Duration::ZERO,
            iterations_run: 0,
        };
        assert_eq!(result.vc_throughput(), 0.0);
        assert_eq!(result.ms_per_vc(), 0.0);
    }

    #[test]
    fn test_ms_per_vc() {
        let result = BenchmarkResult {
            scenario_name: "test".into(),
            profile: PipelineProfile {
                timings: Vec::new(),
                total_duration: Duration::from_millis(100),
                iterations: 1,
                total_vcs_generated: 50,
                total_vcs_dispatched: 50,
                total_cache_hits: 0,
                total_cache_misses: 50,
                total_proposals: 0,
                total_applied: 0,
            },
            wall_clock: Duration::from_millis(100),
            iterations_run: 1,
        };
        assert!((result.ms_per_vc() - 2.0).abs() < 0.01);
    }
}
