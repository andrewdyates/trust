// trust-driver/profiling.rs: Pipeline stage profiling infrastructure
//
// Instruments the verification pipeline to collect wall-clock timing,
// VC counts, cache hit rates, and backend usage statistics per stage.
// Provides `PipelineProfile` summary and `ProfiledVerifyPhase` /
// `ProfiledStrengthenPhase` / `ProfiledBackpropPhase` wrappers that
// transparently collect timing data around existing phase implementations.
//
// Part of #670: Profile verification pipeline baseline before optimization
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::fmt;
use std::path::Path;
use std::sync::Mutex;
use std::time::{Duration, Instant};

use crate::{BackpropOutput, BackpropPhase, StrengthenPhase, VerifyOutput, VerifyPhase};
use trust_strengthen::{Proposal, StrengthenOutput};
use trust_types::fx::FxHashMap;

// ---------------------------------------------------------------------------
// Pipeline stage identifiers
// ---------------------------------------------------------------------------

/// Identifies a stage in the verification pipeline for profiling.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub(crate) enum PipelineStage {
    /// MIR extraction and VC generation.
    VcGeneration,
    /// Solver dispatch (all backends).
    SolverDispatch,
    /// Cache lookup (hit/miss).
    CacheLookup,
    /// Spec strengthening (AI inference).
    Strengthening,
    /// Source rewriting (backprop).
    Backprop,
    /// CEGAR refinement loop.
    CegarRefinement,
    /// Convergence checking.
    ConvergenceCheck,
    /// Proof certificate generation.
    Certification,
}

impl fmt::Display for PipelineStage {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::VcGeneration => write!(f, "vc_generation"),
            Self::SolverDispatch => write!(f, "solver_dispatch"),
            Self::CacheLookup => write!(f, "cache_lookup"),
            Self::Strengthening => write!(f, "strengthening"),
            Self::Backprop => write!(f, "backprop"),
            Self::CegarRefinement => write!(f, "cegar_refinement"),
            Self::ConvergenceCheck => write!(f, "convergence_check"),
            Self::Certification => write!(f, "certification"),
        }
    }
}

// ---------------------------------------------------------------------------
// Stage timing record
// ---------------------------------------------------------------------------

/// Timing and count data for a single invocation of a pipeline stage.
#[derive(Debug, Clone)]
pub(crate) struct StageTiming {
    /// Which stage was timed.
    pub stage: PipelineStage,
    /// Wall-clock duration of this invocation.
    pub duration: Duration,
    /// Pipeline iteration index (zero-based).
    pub iteration: u32,
    /// Number of VCs processed in this invocation (if applicable).
    pub vc_count: Option<usize>,
}

// ---------------------------------------------------------------------------
// Pipeline profile (aggregate)
// ---------------------------------------------------------------------------

/// Aggregated profiling data for the entire pipeline run.
#[derive(Debug, Clone)]
pub(crate) struct PipelineProfile {
    /// Per-invocation timing records.
    pub timings: Vec<StageTiming>,
    /// Total wall-clock time for the entire pipeline run.
    pub total_duration: Duration,
    /// Total number of pipeline iterations.
    pub iterations: u32,
    /// Total VCs generated across all iterations.
    pub total_vcs_generated: usize,
    /// Total VCs dispatched to solvers.
    pub total_vcs_dispatched: usize,
    /// Total VCs served from cache.
    pub total_cache_hits: usize,
    /// Total VCs that missed the cache.
    pub total_cache_misses: usize,
    /// Total strengthening proposals generated.
    pub total_proposals: usize,
    /// Total proposals applied by backprop.
    pub total_applied: usize,
}

impl PipelineProfile {
    /// Compute the percentage of total time spent in each stage.
    #[must_use]
    pub(crate) fn stage_percentages(&self) -> Vec<(PipelineStage, f64)> {
        let total_ms = self.total_duration.as_secs_f64() * 1000.0;
        if total_ms == 0.0 {
            return Vec::new();
        }

        let mut stage_totals: FxHashMap<PipelineStage, f64> =
            FxHashMap::default();

        for t in &self.timings {
            let ms = t.duration.as_secs_f64() * 1000.0;
            *stage_totals.entry(t.stage).or_default() += ms;
        }

        let mut percentages: Vec<(PipelineStage, f64)> = stage_totals
            .into_iter()
            .map(|(stage, ms)| (stage, (ms / total_ms) * 100.0))
            .collect();
        percentages.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap_or(std::cmp::Ordering::Equal));
        percentages
    }

    /// Total time spent in a specific stage across all iterations.
    #[must_use]
    pub(crate) fn stage_total_duration(&self, stage: PipelineStage) -> Duration {
        self.timings
            .iter()
            .filter(|t| t.stage == stage)
            .map(|t| t.duration)
            .sum()
    }

    /// Average time per invocation for a specific stage.
    #[must_use]
    pub(crate) fn stage_average_duration(&self, stage: PipelineStage) -> Option<Duration> {
        let matching: Vec<_> = self.timings.iter().filter(|t| t.stage == stage).collect();
        if matching.is_empty() {
            return None;
        }
        let total: Duration = matching.iter().map(|t| t.duration).sum();
        Some(total / matching.len() as u32)
    }

    /// Number of invocations of a specific stage.
    #[must_use]
    pub(crate) fn stage_invocation_count(&self, stage: PipelineStage) -> usize {
        self.timings.iter().filter(|t| t.stage == stage).count()
    }

    /// Cache hit rate as a percentage (0.0 to 100.0).
    #[must_use]
    pub(crate) fn cache_hit_rate(&self) -> f64 {
        let total = self.total_cache_hits + self.total_cache_misses;
        if total == 0 {
            return 0.0;
        }
        (self.total_cache_hits as f64 / total as f64) * 100.0
    }

    /// Average VCs per function (total VCs / iterations, as a proxy).
    #[must_use]
    pub(crate) fn avg_vcs_per_iteration(&self) -> f64 {
        if self.iterations == 0 {
            return 0.0;
        }
        self.total_vcs_dispatched as f64 / self.iterations as f64
    }
}

impl fmt::Display for PipelineProfile {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "=== Pipeline Profile ===")?;
        writeln!(
            f,
            "Total time: {:.1}ms ({} iterations)",
            self.total_duration.as_secs_f64() * 1000.0,
            self.iterations
        )?;
        writeln!(f)?;
        writeln!(f, "--- Stage Breakdown ---")?;
        for (stage, pct) in self.stage_percentages() {
            let total = self.stage_total_duration(stage);
            let count = self.stage_invocation_count(stage);
            writeln!(
                f,
                "  {:<20} {:6.1}%  ({:.1}ms, {} calls)",
                stage,
                pct,
                total.as_secs_f64() * 1000.0,
                count,
            )?;
        }
        writeln!(f)?;
        writeln!(f, "--- VC Statistics ---")?;
        writeln!(
            f,
            "  VCs generated:     {}",
            self.total_vcs_generated
        )?;
        writeln!(
            f,
            "  VCs dispatched:    {}",
            self.total_vcs_dispatched
        )?;
        writeln!(
            f,
            "  Cache hits:        {} ({:.1}%)",
            self.total_cache_hits,
            self.cache_hit_rate()
        )?;
        writeln!(
            f,
            "  Cache misses:      {}",
            self.total_cache_misses
        )?;
        writeln!(
            f,
            "  Avg VCs/iteration: {:.1}",
            self.avg_vcs_per_iteration()
        )?;
        writeln!(f)?;
        writeln!(f, "--- Strengthening ---")?;
        writeln!(
            f,
            "  Proposals:  {}",
            self.total_proposals
        )?;
        writeln!(
            f,
            "  Applied:    {}",
            self.total_applied
        )?;
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// PipelineProfiler — mutable accumulator
// ---------------------------------------------------------------------------

/// Mutable accumulator for pipeline profiling data.
///
/// Thread-safe: uses internal `Mutex` so profiled phase wrappers can
/// record timings from any context.
#[derive(Debug)]
pub(crate) struct PipelineProfiler {
    inner: Mutex<ProfilerInner>,
    start: Instant,
}

#[derive(Debug)]
struct ProfilerInner {
    timings: Vec<StageTiming>,
    iteration: u32,
    total_vcs_generated: usize,
    total_vcs_dispatched: usize,
    total_cache_hits: usize,
    total_cache_misses: usize,
    total_proposals: usize,
    total_applied: usize,
}

impl PipelineProfiler {
    /// Create a new profiler. Call this before the pipeline run begins.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            inner: Mutex::new(ProfilerInner {
                timings: Vec::new(),
                iteration: 0,
                total_vcs_generated: 0,
                total_vcs_dispatched: 0,
                total_cache_hits: 0,
                total_cache_misses: 0,
                total_proposals: 0,
                total_applied: 0,
            }),
            start: Instant::now(),
        }
    }

    /// Record a stage timing.
    pub(crate) fn record_timing(&self, stage: PipelineStage, duration: Duration, vc_count: Option<usize>) {
        if let Ok(mut inner) = self.inner.lock() {
            let iteration = inner.iteration;
            inner.timings.push(StageTiming {
                stage,
                duration,
                iteration,
                vc_count,
            });
        }
    }

    /// Advance to the next iteration.
    pub(crate) fn next_iteration(&self) {
        if let Ok(mut inner) = self.inner.lock() {
            inner.iteration += 1;
        }
    }

    /// Record VC generation statistics.
    pub(crate) fn record_vcs_generated(&self, count: usize) {
        if let Ok(mut inner) = self.inner.lock() {
            inner.total_vcs_generated += count;
        }
    }

    /// Record VCs dispatched to solvers.
    pub(crate) fn record_vcs_dispatched(&self, count: usize) {
        if let Ok(mut inner) = self.inner.lock() {
            inner.total_vcs_dispatched += count;
        }
    }

    /// Record cache hit/miss counts.
    pub(crate) fn record_cache_stats(&self, hits: usize, misses: usize) {
        if let Ok(mut inner) = self.inner.lock() {
            inner.total_cache_hits += hits;
            inner.total_cache_misses += misses;
        }
    }

    /// Record strengthening proposal counts.
    pub(crate) fn record_proposals(&self, generated: usize, applied: usize) {
        if let Ok(mut inner) = self.inner.lock() {
            inner.total_proposals += generated;
            inner.total_applied += applied;
        }
    }

    /// Current iteration index.
    #[must_use]
    pub(crate) fn current_iteration(&self) -> u32 {
        self.inner.lock().map(|i| i.iteration).unwrap_or(0)
    }

    /// Finalize and produce the aggregate profile.
    #[must_use]
    pub(crate) fn finalize(&self) -> PipelineProfile {
        let inner = self.inner.lock().expect("profiler lock poisoned");
        PipelineProfile {
            timings: inner.timings.clone(),
            total_duration: self.start.elapsed(),
            iterations: inner.iteration + 1,
            total_vcs_generated: inner.total_vcs_generated,
            total_vcs_dispatched: inner.total_vcs_dispatched,
            total_cache_hits: inner.total_cache_hits,
            total_cache_misses: inner.total_cache_misses,
            total_proposals: inner.total_proposals,
            total_applied: inner.total_applied,
        }
    }
}

impl Default for PipelineProfiler {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Profiled phase wrappers
// ---------------------------------------------------------------------------

/// Wraps a `VerifyPhase` to record timing and VC count data.
pub(crate) struct ProfiledVerifyPhase<'a> {
    inner: &'a dyn VerifyPhase,
    profiler: &'a PipelineProfiler,
}

impl<'a> ProfiledVerifyPhase<'a> {
    /// Create a profiled wrapper around an existing verify phase.
    #[must_use]
    pub(crate) fn new(inner: &'a dyn VerifyPhase, profiler: &'a PipelineProfiler) -> Self {
        Self { inner, profiler }
    }
}

impl<'a> VerifyPhase for ProfiledVerifyPhase<'a> {
    fn verify(&self, source_path: &Path) -> VerifyOutput {
        let start = Instant::now();
        let output = self.inner.verify(source_path);
        let elapsed = start.elapsed();

        self.profiler.record_timing(
            PipelineStage::SolverDispatch,
            elapsed,
            Some(output.vcs_dispatched),
        );
        self.profiler.record_vcs_dispatched(output.vcs_dispatched);
        self.profiler
            .record_vcs_generated(output.vcs_dispatched);

        output
    }
}

/// Wraps a `StrengthenPhase` to record timing and proposal counts.
pub(crate) struct ProfiledStrengthenPhase<'a> {
    inner: &'a dyn StrengthenPhase,
    profiler: &'a PipelineProfiler,
}

impl<'a> ProfiledStrengthenPhase<'a> {
    /// Create a profiled wrapper around an existing strengthen phase.
    #[must_use]
    pub(crate) fn new(inner: &'a dyn StrengthenPhase, profiler: &'a PipelineProfiler) -> Self {
        Self { inner, profiler }
    }
}

impl<'a> StrengthenPhase for ProfiledStrengthenPhase<'a> {
    fn strengthen(&self, source_path: &Path, verify_output: &VerifyOutput) -> StrengthenOutput {
        let start = Instant::now();
        let output = self.inner.strengthen(source_path, verify_output);
        let elapsed = start.elapsed();

        self.profiler.record_timing(
            PipelineStage::Strengthening,
            elapsed,
            None,
        );

        output
    }
}

/// Wraps a `BackpropPhase` to record timing and applied counts.
pub(crate) struct ProfiledBackpropPhase<'a> {
    inner: &'a dyn BackpropPhase,
    profiler: &'a PipelineProfiler,
}

impl<'a> ProfiledBackpropPhase<'a> {
    /// Create a profiled wrapper around an existing backprop phase.
    #[must_use]
    pub(crate) fn new(inner: &'a dyn BackpropPhase, profiler: &'a PipelineProfiler) -> Self {
        Self { inner, profiler }
    }
}

impl<'a> BackpropPhase for ProfiledBackpropPhase<'a> {
    fn backpropagate(&self, source_path: &Path, proposals: &[Proposal]) -> BackpropOutput {
        let start = Instant::now();
        let output = self.inner.backpropagate(source_path, proposals);
        let elapsed = start.elapsed();

        self.profiler.record_timing(
            PipelineStage::Backprop,
            elapsed,
            None,
        );
        self.profiler
            .record_proposals(proposals.len(), output.applied);

        output
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ProofFrontier;
    use std::path::PathBuf;
    use std::thread;
    use std::time::Duration;

    // -- Mock phases for profiling tests --

    struct TimedMockVerify {
        delay: Duration,
        vcs: usize,
    }

    impl VerifyPhase for TimedMockVerify {
        fn verify(&self, _: &Path) -> VerifyOutput {
            thread::sleep(self.delay);
            VerifyOutput {
                frontier: ProofFrontier {
                    trusted: self.vcs as u32,
                    certified: 0,
                    runtime_checked: 0,
                    failed: 0,
                    unknown: 0,
                },
                fingerprint: None,
                vcs_dispatched: self.vcs,
                vcs_failed: 0,
                detailed_results: None,
            }
        }
    }

    struct TimedMockStrengthen {
        delay: Duration,
        proposals: usize,
    }

    impl StrengthenPhase for TimedMockStrengthen {
        fn strengthen(&self, _: &Path, _: &VerifyOutput) -> StrengthenOutput {
            thread::sleep(self.delay);
            StrengthenOutput {
                has_proposals: self.proposals > 0,
                failures_analyzed: self.proposals,
                proposals: Vec::new(),
            }
        }
    }

    struct TimedMockBackprop {
        delay: Duration,
    }

    impl BackpropPhase for TimedMockBackprop {
        fn backpropagate(&self, _: &Path, proposals: &[Proposal]) -> BackpropOutput {
            thread::sleep(self.delay);
            BackpropOutput {
                applied: proposals.len(),
                skipped: 0,
            }
        }
    }

    #[test]
    fn test_profiler_records_timing() {
        let profiler = PipelineProfiler::new();

        profiler.record_timing(
            PipelineStage::SolverDispatch,
            Duration::from_millis(100),
            Some(50),
        );
        profiler.record_timing(
            PipelineStage::Strengthening,
            Duration::from_millis(200),
            None,
        );

        let profile = profiler.finalize();
        assert_eq!(profile.timings.len(), 2);
        assert_eq!(profile.timings[0].stage, PipelineStage::SolverDispatch);
        assert_eq!(profile.timings[0].vc_count, Some(50));
        assert_eq!(profile.timings[1].stage, PipelineStage::Strengthening);
    }

    #[test]
    fn test_profiler_iteration_tracking() {
        let profiler = PipelineProfiler::new();

        profiler.record_timing(
            PipelineStage::SolverDispatch,
            Duration::from_millis(10),
            None,
        );
        assert_eq!(profiler.current_iteration(), 0);

        profiler.next_iteration();
        profiler.record_timing(
            PipelineStage::SolverDispatch,
            Duration::from_millis(10),
            None,
        );
        assert_eq!(profiler.current_iteration(), 1);

        let profile = profiler.finalize();
        assert_eq!(profile.timings[0].iteration, 0);
        assert_eq!(profile.timings[1].iteration, 1);
        assert_eq!(profile.iterations, 2);
    }

    #[test]
    fn test_profiler_vc_statistics() {
        let profiler = PipelineProfiler::new();

        profiler.record_vcs_generated(100);
        profiler.record_vcs_dispatched(90);
        profiler.record_cache_stats(30, 60);

        let profile = profiler.finalize();
        assert_eq!(profile.total_vcs_generated, 100);
        assert_eq!(profile.total_vcs_dispatched, 90);
        assert_eq!(profile.total_cache_hits, 30);
        assert_eq!(profile.total_cache_misses, 60);
    }

    #[test]
    fn test_cache_hit_rate() {
        let profile = PipelineProfile {
            timings: Vec::new(),
            total_duration: Duration::from_millis(100),
            iterations: 1,
            total_vcs_generated: 100,
            total_vcs_dispatched: 100,
            total_cache_hits: 75,
            total_cache_misses: 25,
            total_proposals: 0,
            total_applied: 0,
        };
        let rate = profile.cache_hit_rate();
        assert!((rate - 75.0).abs() < 0.01);
    }

    #[test]
    fn test_cache_hit_rate_zero_total() {
        let profile = PipelineProfile {
            timings: Vec::new(),
            total_duration: Duration::from_millis(100),
            iterations: 1,
            total_vcs_generated: 0,
            total_vcs_dispatched: 0,
            total_cache_hits: 0,
            total_cache_misses: 0,
            total_proposals: 0,
            total_applied: 0,
        };
        assert_eq!(profile.cache_hit_rate(), 0.0);
    }

    #[test]
    fn test_stage_percentages() {
        let profile = PipelineProfile {
            timings: vec![
                StageTiming {
                    stage: PipelineStage::SolverDispatch,
                    duration: Duration::from_millis(600),
                    iteration: 0,
                    vc_count: Some(100),
                },
                StageTiming {
                    stage: PipelineStage::Strengthening,
                    duration: Duration::from_millis(300),
                    iteration: 0,
                    vc_count: None,
                },
                StageTiming {
                    stage: PipelineStage::Backprop,
                    duration: Duration::from_millis(100),
                    iteration: 0,
                    vc_count: None,
                },
            ],
            total_duration: Duration::from_millis(1000),
            iterations: 1,
            total_vcs_generated: 100,
            total_vcs_dispatched: 100,
            total_cache_hits: 0,
            total_cache_misses: 100,
            total_proposals: 5,
            total_applied: 3,
        };

        let pcts = profile.stage_percentages();
        assert_eq!(pcts.len(), 3);
        // Sorted by percentage descending
        assert_eq!(pcts[0].0, PipelineStage::SolverDispatch);
        assert!((pcts[0].1 - 60.0).abs() < 0.01);
        assert_eq!(pcts[1].0, PipelineStage::Strengthening);
        assert!((pcts[1].1 - 30.0).abs() < 0.01);
        assert_eq!(pcts[2].0, PipelineStage::Backprop);
        assert!((pcts[2].1 - 10.0).abs() < 0.01);
    }

    #[test]
    fn test_stage_average_duration() {
        let profile = PipelineProfile {
            timings: vec![
                StageTiming {
                    stage: PipelineStage::SolverDispatch,
                    duration: Duration::from_millis(100),
                    iteration: 0,
                    vc_count: None,
                },
                StageTiming {
                    stage: PipelineStage::SolverDispatch,
                    duration: Duration::from_millis(200),
                    iteration: 1,
                    vc_count: None,
                },
                StageTiming {
                    stage: PipelineStage::SolverDispatch,
                    duration: Duration::from_millis(300),
                    iteration: 2,
                    vc_count: None,
                },
            ],
            total_duration: Duration::from_millis(600),
            iterations: 3,
            total_vcs_generated: 0,
            total_vcs_dispatched: 0,
            total_cache_hits: 0,
            total_cache_misses: 0,
            total_proposals: 0,
            total_applied: 0,
        };

        let avg = profile.stage_average_duration(PipelineStage::SolverDispatch).unwrap();
        assert_eq!(avg, Duration::from_millis(200));
        assert!(profile.stage_average_duration(PipelineStage::Backprop).is_none());
    }

    #[test]
    fn test_avg_vcs_per_iteration() {
        let profile = PipelineProfile {
            timings: Vec::new(),
            total_duration: Duration::from_millis(100),
            iterations: 4,
            total_vcs_generated: 200,
            total_vcs_dispatched: 200,
            total_cache_hits: 0,
            total_cache_misses: 0,
            total_proposals: 0,
            total_applied: 0,
        };
        assert!((profile.avg_vcs_per_iteration() - 50.0).abs() < 0.01);
    }

    #[test]
    fn test_avg_vcs_per_iteration_zero() {
        let profile = PipelineProfile {
            timings: Vec::new(),
            total_duration: Duration::from_millis(100),
            iterations: 0,
            total_vcs_generated: 0,
            total_vcs_dispatched: 0,
            total_cache_hits: 0,
            total_cache_misses: 0,
            total_proposals: 0,
            total_applied: 0,
        };
        assert_eq!(profile.avg_vcs_per_iteration(), 0.0);
    }

    #[test]
    fn test_profiled_verify_phase_records_timing() {
        let mock_verify = TimedMockVerify {
            delay: Duration::from_millis(5),
            vcs: 42,
        };
        let profiler = PipelineProfiler::new();
        let profiled = ProfiledVerifyPhase::new(&mock_verify, &profiler);

        let output = profiled.verify(&PathBuf::from("/tmp/test.rs"));

        assert_eq!(output.vcs_dispatched, 42);
        let profile = profiler.finalize();
        assert_eq!(profile.timings.len(), 1);
        assert_eq!(profile.timings[0].stage, PipelineStage::SolverDispatch);
        assert_eq!(profile.timings[0].vc_count, Some(42));
        assert!(profile.timings[0].duration >= Duration::from_millis(4));
        assert_eq!(profile.total_vcs_dispatched, 42);
        assert_eq!(profile.total_vcs_generated, 42);
    }

    #[test]
    fn test_profiled_strengthen_phase_records_timing() {
        let mock_strengthen = TimedMockStrengthen {
            delay: Duration::from_millis(5),
            proposals: 3,
        };
        let profiler = PipelineProfiler::new();
        let profiled = ProfiledStrengthenPhase::new(&mock_strengthen, &profiler);

        let verify_output = VerifyOutput {
            frontier: ProofFrontier {
                trusted: 5,
                certified: 0,
                runtime_checked: 0,
                failed: 3,
                unknown: 0,
            },
            fingerprint: None,
            vcs_dispatched: 8,
            vcs_failed: 3,
            detailed_results: None,
        };

        let output = profiled.strengthen(&PathBuf::from("/tmp/test.rs"), &verify_output);
        assert!(output.has_proposals);

        let profile = profiler.finalize();
        assert_eq!(profile.timings.len(), 1);
        assert_eq!(profile.timings[0].stage, PipelineStage::Strengthening);
        assert!(profile.timings[0].duration >= Duration::from_millis(4));
    }

    #[test]
    fn test_profiled_backprop_phase_records_timing() {
        let mock_backprop = TimedMockBackprop {
            delay: Duration::from_millis(5),
        };
        let profiler = PipelineProfiler::new();
        let profiled = ProfiledBackpropPhase::new(&mock_backprop, &profiler);

        let proposals = vec![
            Proposal {
                function_path: "test::foo".into(),
                function_name: "foo".into(),
                kind: trust_strengthen::ProposalKind::AddPrecondition {
                    spec_body: "x > 0".into(),
                },
                confidence: 0.9,
                rationale: "test".into(),
            },
        ];

        let output = profiled.backpropagate(&PathBuf::from("/tmp/test.rs"), &proposals);
        assert_eq!(output.applied, 1);

        let profile = profiler.finalize();
        assert_eq!(profile.timings.len(), 1);
        assert_eq!(profile.timings[0].stage, PipelineStage::Backprop);
        assert_eq!(profile.total_proposals, 1);
        assert_eq!(profile.total_applied, 1);
    }

    #[test]
    fn test_pipeline_profile_display() {
        let profile = PipelineProfile {
            timings: vec![
                StageTiming {
                    stage: PipelineStage::SolverDispatch,
                    duration: Duration::from_millis(800),
                    iteration: 0,
                    vc_count: Some(150),
                },
                StageTiming {
                    stage: PipelineStage::Strengthening,
                    duration: Duration::from_millis(150),
                    iteration: 0,
                    vc_count: None,
                },
                StageTiming {
                    stage: PipelineStage::Backprop,
                    duration: Duration::from_millis(50),
                    iteration: 0,
                    vc_count: None,
                },
            ],
            total_duration: Duration::from_millis(1000),
            iterations: 1,
            total_vcs_generated: 150,
            total_vcs_dispatched: 150,
            total_cache_hits: 40,
            total_cache_misses: 110,
            total_proposals: 8,
            total_applied: 5,
        };

        let display = format!("{profile}");
        assert!(display.contains("Pipeline Profile"));
        assert!(display.contains("solver_dispatch"));
        assert!(display.contains("strengthening"));
        assert!(display.contains("backprop"));
        assert!(display.contains("VCs generated"));
        assert!(display.contains("Cache hits"));
        assert!(display.contains("Proposals"));
    }

    #[test]
    fn test_pipeline_stage_display() {
        assert_eq!(PipelineStage::VcGeneration.to_string(), "vc_generation");
        assert_eq!(PipelineStage::SolverDispatch.to_string(), "solver_dispatch");
        assert_eq!(PipelineStage::CacheLookup.to_string(), "cache_lookup");
        assert_eq!(PipelineStage::Strengthening.to_string(), "strengthening");
        assert_eq!(PipelineStage::Backprop.to_string(), "backprop");
        assert_eq!(PipelineStage::CegarRefinement.to_string(), "cegar_refinement");
        assert_eq!(PipelineStage::ConvergenceCheck.to_string(), "convergence_check");
        assert_eq!(PipelineStage::Certification.to_string(), "certification");
    }

    #[test]
    fn test_profiler_thread_safe() {
        let profiler = PipelineProfiler::new();

        // Record from multiple contexts (simulating multi-phase)
        profiler.record_timing(
            PipelineStage::SolverDispatch,
            Duration::from_millis(10),
            Some(5),
        );
        profiler.record_vcs_dispatched(5);
        profiler.record_cache_stats(2, 3);
        profiler.next_iteration();
        profiler.record_timing(
            PipelineStage::Strengthening,
            Duration::from_millis(20),
            None,
        );
        profiler.record_proposals(3, 2);

        let profile = profiler.finalize();
        assert_eq!(profile.timings.len(), 2);
        assert_eq!(profile.total_vcs_dispatched, 5);
        assert_eq!(profile.total_cache_hits, 2);
        assert_eq!(profile.total_cache_misses, 3);
        assert_eq!(profile.total_proposals, 3);
        assert_eq!(profile.total_applied, 2);
    }

    #[test]
    fn test_stage_total_duration() {
        let profile = PipelineProfile {
            timings: vec![
                StageTiming {
                    stage: PipelineStage::SolverDispatch,
                    duration: Duration::from_millis(100),
                    iteration: 0,
                    vc_count: None,
                },
                StageTiming {
                    stage: PipelineStage::Strengthening,
                    duration: Duration::from_millis(50),
                    iteration: 0,
                    vc_count: None,
                },
                StageTiming {
                    stage: PipelineStage::SolverDispatch,
                    duration: Duration::from_millis(150),
                    iteration: 1,
                    vc_count: None,
                },
            ],
            total_duration: Duration::from_millis(300),
            iterations: 2,
            total_vcs_generated: 0,
            total_vcs_dispatched: 0,
            total_cache_hits: 0,
            total_cache_misses: 0,
            total_proposals: 0,
            total_applied: 0,
        };

        assert_eq!(
            profile.stage_total_duration(PipelineStage::SolverDispatch),
            Duration::from_millis(250)
        );
        assert_eq!(
            profile.stage_total_duration(PipelineStage::Strengthening),
            Duration::from_millis(50)
        );
        assert_eq!(
            profile.stage_total_duration(PipelineStage::Backprop),
            Duration::ZERO
        );
    }
}
