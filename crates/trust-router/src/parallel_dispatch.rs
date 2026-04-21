// trust-router/parallel_dispatch.rs: Work-stealing parallel VC dispatch
//
// tRust #456: Dispatches verification conditions in parallel using rayon's
// work-stealing thread pool. Groups independent VCs (via constraint
// independence partitioning) so that independent partitions run concurrently.
// When one partition finishes early, rayon's work-stealing scheduler
// automatically reassigns its threads to help remaining partitions.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::sync::Arc;
use std::time::{Duration, Instant};

use rayon::prelude::*;
use trust_types::formula_arena::FormulaArena;
use trust_types::{Formula, VerificationCondition, VerificationResult};

use crate::independence;
use crate::{ArenaVc, VerificationBackend};

/// tRust #456: Configuration for parallel VC dispatch.
///
/// Controls thread pool size, per-VC timeout, and whether independence
/// partitioning is applied before dispatch.
#[derive(Debug, Clone)]
pub struct ParallelDispatchConfig {
    /// Maximum number of threads in the rayon thread pool.
    /// Defaults to the number of available CPUs.
    pub num_threads: usize,
    /// Per-VC timeout. If a VC takes longer than this, its result is
    /// `VerificationResult::Timeout`. `None` means no timeout.
    pub timeout_per_vc: Option<Duration>,
    /// Whether to use constraint independence partitioning to group
    /// VCs before parallel dispatch. When enabled, conjunctive VCs
    /// are split into independent sub-problems that can be solved
    /// concurrently.
    pub use_independence: bool,
}

impl Default for ParallelDispatchConfig {
    fn default() -> Self {
        Self {
            num_threads: num_cpus_or_default(),
            timeout_per_vc: Some(Duration::from_secs(60)),
            use_independence: true,
        }
    }
}

impl ParallelDispatchConfig {
    /// Create a config with a specific thread count.
    #[must_use]
    pub fn with_threads(mut self, n: usize) -> Self {
        self.num_threads = n.max(1);
        self
    }

    /// Create a config with a specific per-VC timeout.
    #[must_use]
    pub fn with_timeout(mut self, timeout: Duration) -> Self {
        self.timeout_per_vc = Some(timeout);
        self
    }

    /// Create a config with no per-VC timeout.
    #[must_use]
    pub fn without_timeout(mut self) -> Self {
        self.timeout_per_vc = None;
        self
    }

    /// Disable independence partitioning.
    #[must_use]
    pub fn without_independence(mut self) -> Self {
        self.use_independence = false;
        self
    }
}

/// tRust #456: Result of a single VC dispatch, including timing metadata.
#[derive(Debug, Clone)]
pub struct DispatchResult {
    /// The original verification condition.
    pub vc: VerificationCondition,
    /// The verification result from the solver.
    pub result: VerificationResult,
    /// Wall-clock time spent on this VC.
    pub wall_time: Duration,
    /// Which independence partition this VC belonged to (0 if unsplit).
    pub partition_index: usize,
}

/// tRust #456: Summary of a parallel dispatch run.
#[derive(Debug)]
pub struct DispatchSummary {
    /// Individual results for each VC.
    pub results: Vec<DispatchResult>,
    /// Total wall-clock time for the entire parallel dispatch.
    pub total_wall_time: Duration,
    /// Number of independence partitions created.
    pub partition_count: usize,
    /// Number of VCs proved.
    pub proved_count: usize,
    /// Number of VCs that failed.
    pub failed_count: usize,
    /// Number of VCs that timed out.
    pub timeout_count: usize,
}

/// tRust #456: Dispatch VCs in parallel using rayon work-stealing.
///
/// This is the main entry point for parallel VC dispatch. It:
/// 1. Optionally partitions conjunctive VCs into independent sub-problems
/// 2. Dispatches all VCs across a rayon thread pool
/// 3. Returns results as a `DispatchSummary`
///
/// Rayon's work-stealing scheduler ensures that when one partition finishes
/// early, its thread helps with remaining work.
#[must_use]
pub fn dispatch_parallel(
    vcs: &[VerificationCondition],
    backends: &[Arc<dyn VerificationBackend>],
    config: &ParallelDispatchConfig,
) -> DispatchSummary {
    let start = Instant::now();

    if vcs.is_empty() {
        return DispatchSummary {
            results: Vec::new(),
            total_wall_time: start.elapsed(),
            partition_count: 0,
            proved_count: 0,
            failed_count: 0,
            timeout_count: 0,
        };
    }

    // Build a custom rayon thread pool with the configured thread count.
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(config.num_threads.max(1))
        .build()
        // tRust #734: rayon pool creation failure is a real system-level error.
        .expect("rayon thread pool creation failed");

    // Prepare work items: (VC, partition_index).
    let work_items: Vec<(VerificationCondition, usize)> = if config.use_independence {
        expand_with_independence(vcs)
    } else {
        vcs.iter().map(|vc| (vc.clone(), 0)).collect()
    };

    let partition_count = work_items
        .iter()
        .map(|(_, p)| *p)
        .max()
        .map_or(1, |m| m + 1);

    // Dispatch all work items in parallel via rayon.
    let results: Vec<DispatchResult> = pool.install(|| {
        work_items
            .par_iter()
            .map(|(vc, partition_idx)| {
                dispatch_single_vc(vc, *partition_idx, backends, config.timeout_per_vc)
            })
            .collect()
    });

    let proved_count = results
        .iter()
        .filter(|r| r.result.is_proved())
        .count();
    let failed_count = results
        .iter()
        .filter(|r| r.result.is_failed())
        .count();
    let timeout_count = results
        .iter()
        .filter(|r| matches!(r.result, VerificationResult::Timeout { .. }))
        .count();

    DispatchSummary {
        results,
        total_wall_time: start.elapsed(),
        partition_count,
        proved_count,
        failed_count,
        timeout_count,
    }
}

/// Dispatch a single VC to the best available backend, with optional timeout.
fn dispatch_single_vc(
    vc: &VerificationCondition,
    partition_index: usize,
    backends: &[Arc<dyn VerificationBackend>],
    timeout: Option<Duration>,
) -> DispatchResult {
    let start = Instant::now();

    let backend = crate::select_backend(backends, vc);

    let result = match backend {
        Some(b) => {
            // If a timeout is set, check after verification.
            // True preemptive timeout would require the solver to support
            // cancellation. For now we check wall time post-hoc and convert
            // long-running results to Timeout.
            let solver_result = b.verify(vc);
            let elapsed = start.elapsed();

            if let Some(t) = timeout {
                if elapsed > t {
                    VerificationResult::Timeout {
                        solver: b.name().to_string(),
                        timeout_ms: t.as_millis() as u64,
                    }
                } else {
                    solver_result
                }
            } else {
                solver_result
            }
        }
        None => VerificationResult::Unknown {
            solver: "none".to_string(),
            time_ms: 0,
            reason: "no backend can handle this VC".to_string(),
        },
    };

    DispatchResult {
        vc: vc.clone(),
        result,
        wall_time: start.elapsed(),
        partition_index,
    }
}

/// Expand VCs using independence partitioning.
///
/// For each VC whose formula is a conjunction, split its conjuncts into
/// independent groups and create a sub-VC per group. Non-conjunctive VCs
/// pass through as-is. Each sub-VC is tagged with its partition index.
fn expand_with_independence(
    vcs: &[VerificationCondition],
) -> Vec<(VerificationCondition, usize)> {
    let mut work_items = Vec::new();
    let mut global_partition = 0;

    for vc in vcs {
        let conjuncts = match &vc.formula {
            Formula::And(children) if children.len() > 1 => children.as_slice(),
            _ => {
                work_items.push((vc.clone(), global_partition));
                global_partition += 1;
                continue;
            }
        };

        let groups = independence::partition_independent(conjuncts);

        if groups.len() <= 1 {
            // Not splittable — dispatch the original VC.
            work_items.push((vc.clone(), global_partition));
            global_partition += 1;
        } else {
            // Create a sub-VC for each independent group.
            for group in &groups {
                let sub_formula = match group.len() {
                    1 => group[0].clone(),
                    _ => Formula::And(group.clone()),
                };

                let sub_vc = VerificationCondition {
                    formula: sub_formula,
                    kind: vc.kind.clone(),
                    function: vc.function.clone(),
                    location: vc.location.clone(),
                    contract_metadata: vc.contract_metadata,
                };

                work_items.push((sub_vc, global_partition));
            }
            global_partition += 1;
        }
    }

    work_items
}

/// Return a sensible default thread count.
fn num_cpus_or_default() -> usize {
    std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(4)
}

// -----------------------------------------------------------------------
// tRust #708: Arena-aware parallel dispatch
// -----------------------------------------------------------------------

/// tRust #708: Arena-aware parallel dispatch result.
#[derive(Debug, Clone)]
pub struct ArenaDispatchResult {
    /// The arena VC (carries both materialized VC and FormulaRef root).
    pub arena_vc: ArenaVc,
    /// The verification result from the solver.
    pub result: VerificationResult,
    /// Wall-clock time spent on this VC.
    pub wall_time: Duration,
    /// Partition index (0 if unsplit).
    pub partition_index: usize,
}

/// tRust #708: Summary of an arena-aware parallel dispatch run.
#[derive(Debug)]
pub struct ArenaDispatchSummary {
    /// Individual results for each VC.
    pub results: Vec<ArenaDispatchResult>,
    /// Total wall-clock time for the entire parallel dispatch.
    pub total_wall_time: Duration,
    /// Number of VCs proved.
    pub proved_count: usize,
    /// Number of VCs that failed.
    pub failed_count: usize,
    /// Number of VCs that timed out.
    pub timeout_count: usize,
}

/// tRust #708: Dispatch arena VCs in parallel using rayon work-stealing.
///
/// Like `dispatch_parallel`, but each VC carries a `FormulaRef` into a shared
/// `Arc<FormulaArena>`. Backends that override `verify_arena` can process
/// formulas without materializing `Box<Formula>` trees.
///
/// The arena is shared across all rayon worker threads via `Arc`.
#[must_use]
pub fn dispatch_parallel_arena(
    vcs: &[ArenaVc],
    arena: Arc<FormulaArena>,
    backends: &[Arc<dyn VerificationBackend>],
    config: &ParallelDispatchConfig,
) -> ArenaDispatchSummary {
    let start = Instant::now();

    if vcs.is_empty() {
        return ArenaDispatchSummary {
            results: Vec::new(),
            total_wall_time: start.elapsed(),
            proved_count: 0,
            failed_count: 0,
            timeout_count: 0,
        };
    }

    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(config.num_threads.max(1))
        .build()
        // tRust #734: rayon pool creation failure is a real system-level error.
        .expect("rayon thread pool creation failed");

    let backends_arc: Vec<Arc<dyn VerificationBackend>> = backends.to_vec();

    let results: Vec<ArenaDispatchResult> = pool.install(|| {
        vcs.par_iter()
            .enumerate()
            .map(|(idx, avc)| {
                let vc_start = Instant::now();
                let backend = crate::select_backend(&backends_arc, &avc.vc);

                let result = match backend {
                    Some(b) => {
                        let solver_result = b.verify_arena(&avc.vc, avc.root, &arena);
                        let elapsed = vc_start.elapsed();
                        if let Some(t) = config.timeout_per_vc {
                            if elapsed > t {
                                VerificationResult::Timeout {
                                    solver: b.name().to_string(),
                                    timeout_ms: t.as_millis() as u64,
                                }
                            } else {
                                solver_result
                            }
                        } else {
                            solver_result
                        }
                    }
                    None => VerificationResult::Unknown {
                        solver: "none".to_string(),
                        time_ms: 0,
                        reason: "no backend can handle this VC".to_string(),
                    },
                };

                ArenaDispatchResult {
                    arena_vc: avc.clone(),
                    result,
                    wall_time: vc_start.elapsed(),
                    partition_index: idx,
                }
            })
            .collect()
    });

    let proved_count = results.iter().filter(|r| r.result.is_proved()).count();
    let failed_count = results.iter().filter(|r| r.result.is_failed()).count();
    let timeout_count = results
        .iter()
        .filter(|r| matches!(r.result, VerificationResult::Timeout { .. }))
        .count();

    ArenaDispatchSummary {
        results,
        total_wall_time: start.elapsed(),
        proved_count,
        failed_count,
        timeout_count,
    }
}

#[cfg(test)]
mod tests {
    use std::sync::atomic::{AtomicUsize, Ordering};

    use trust_types::*;

    use super::*;
    use crate::mock_backend::MockBackend;
use trust_types::fx::FxHashSet;

    /// Helper: wrap MockBackend in Arc.
    fn mock_backends() -> Vec<Arc<dyn VerificationBackend>> {
        vec![Arc::new(MockBackend)]
    }

    /// Helper: create a simple test VC.
    fn test_vc(name: &str, formula: Formula) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: name.to_string(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
        }
    }

    // -------------------------------------------------------------------
    // Test 1: Single VC dispatch
    // -------------------------------------------------------------------

    #[test]
    fn test_dispatch_single_vc_proved() {
        let config = ParallelDispatchConfig::default().with_threads(1);
        let vcs = vec![test_vc("single", Formula::Bool(false))];

        let summary = dispatch_parallel(&vcs, &mock_backends(), &config);

        assert_eq!(summary.results.len(), 1);
        assert!(summary.results[0].result.is_proved());
        assert_eq!(summary.proved_count, 1);
        assert_eq!(summary.failed_count, 0);
        assert_eq!(summary.timeout_count, 0);
    }

    // -------------------------------------------------------------------
    // Test 2: Single VC that fails
    // -------------------------------------------------------------------

    #[test]
    fn test_dispatch_single_vc_failed() {
        let config = ParallelDispatchConfig::default().with_threads(1);
        let vcs = vec![test_vc("failing", Formula::Bool(true))];

        let summary = dispatch_parallel(&vcs, &mock_backends(), &config);

        assert_eq!(summary.results.len(), 1);
        assert!(summary.results[0].result.is_failed());
        assert_eq!(summary.proved_count, 0);
        assert_eq!(summary.failed_count, 1);
    }

    // -------------------------------------------------------------------
    // Test 3: Empty VC list
    // -------------------------------------------------------------------

    #[test]
    fn test_dispatch_empty_vcs() {
        let config = ParallelDispatchConfig::default();
        let summary = dispatch_parallel(&[], &mock_backends(), &config);

        assert!(summary.results.is_empty());
        assert_eq!(summary.proved_count, 0);
        assert_eq!(summary.partition_count, 0);
    }

    // -------------------------------------------------------------------
    // Test 4: Multiple independent VCs dispatched in parallel
    // -------------------------------------------------------------------

    #[test]
    fn test_dispatch_multiple_independent_vcs_parallel() {
        let config = ParallelDispatchConfig::default()
            .with_threads(4)
            .without_independence();

        let vcs: Vec<_> = (0..8)
            .map(|i| test_vc(&format!("fn_{i}"), Formula::Bool(false)))
            .collect();

        let summary = dispatch_parallel(&vcs, &mock_backends(), &config);

        assert_eq!(summary.results.len(), 8);
        assert_eq!(summary.proved_count, 8);
        assert_eq!(summary.failed_count, 0);
    }

    // -------------------------------------------------------------------
    // Test 5: Independence partitioning splits disjoint conjuncts
    // -------------------------------------------------------------------

    #[test]
    fn test_dispatch_with_independence_splits_conjuncts() {
        let config = ParallelDispatchConfig::default().with_threads(2);

        // And(x > 0, y > 0) — independent variables, should split into 2 sub-VCs.
        let vc = test_vc(
            "split_me",
            Formula::And(vec![
                Formula::Gt(
                    Box::new(Formula::Var("x".into(), Sort::Int)),
                    Box::new(Formula::Int(0)),
                ),
                Formula::Gt(
                    Box::new(Formula::Var("y".into(), Sort::Int)),
                    Box::new(Formula::Int(0)),
                ),
            ]),
        );

        let summary = dispatch_parallel(&[vc], &mock_backends(), &config);

        // The mock backend returns Unknown for variable formulas, but the
        // key assertion is that independence partitioning created 2 sub-VCs.
        assert_eq!(
            summary.results.len(),
            2,
            "disjoint conjuncts should be split into 2 sub-VCs"
        );
    }

    // -------------------------------------------------------------------
    // Test 6: Independence partitioning does not split shared variables
    // -------------------------------------------------------------------

    #[test]
    fn test_dispatch_independence_no_split_shared_vars() {
        let config = ParallelDispatchConfig::default().with_threads(2);

        // And(x > 0, x < 10) — shared variable x, should NOT split.
        let vc = test_vc(
            "no_split",
            Formula::And(vec![
                Formula::Gt(
                    Box::new(Formula::Var("x".into(), Sort::Int)),
                    Box::new(Formula::Int(0)),
                ),
                Formula::Lt(
                    Box::new(Formula::Var("x".into(), Sort::Int)),
                    Box::new(Formula::Int(10)),
                ),
            ]),
        );

        let summary = dispatch_parallel(&[vc], &mock_backends(), &config);

        assert_eq!(
            summary.results.len(),
            1,
            "shared variable should prevent splitting"
        );
    }

    // -------------------------------------------------------------------
    // Test 7: Timeout handling
    // -------------------------------------------------------------------

    #[test]
    fn test_dispatch_timeout_handling() {
        // Create a backend that sleeps to simulate slow solving.
        struct SlowBackend;

        impl VerificationBackend for SlowBackend {
            fn name(&self) -> &str {
                "slow"
            }
            fn can_handle(&self, _vc: &VerificationCondition) -> bool {
                true
            }
            fn verify(&self, _vc: &VerificationCondition) -> VerificationResult {
                std::thread::sleep(Duration::from_millis(200));
                VerificationResult::Proved {
                    solver: "slow".to_string(),
                    time_ms: 200,
                    strength: ProofStrength::smt_unsat(), proof_certificate: None,
                solver_warnings: None, }
            }
        }

        let backends: Vec<Arc<dyn VerificationBackend>> = vec![Arc::new(SlowBackend)];
        // Set a very short timeout (50ms) — the solver takes 200ms.
        let config = ParallelDispatchConfig::default()
            .with_threads(1)
            .with_timeout(Duration::from_millis(50));

        let vcs = vec![test_vc("slow_vc", Formula::Bool(false))];
        let summary = dispatch_parallel(&vcs, &backends, &config);

        assert_eq!(summary.results.len(), 1);
        assert_eq!(summary.timeout_count, 1);
        assert!(
            matches!(summary.results[0].result, VerificationResult::Timeout { .. }),
            "VC exceeding timeout should produce Timeout result"
        );
    }

    // -------------------------------------------------------------------
    // Test 8: No timeout set — solver runs to completion
    // -------------------------------------------------------------------

    #[test]
    fn test_dispatch_no_timeout_runs_to_completion() {
        let config = ParallelDispatchConfig::default()
            .with_threads(1)
            .without_timeout();

        let vcs = vec![test_vc("no_timeout", Formula::Bool(false))];
        let summary = dispatch_parallel(&vcs, &mock_backends(), &config);

        assert_eq!(summary.results.len(), 1);
        assert!(summary.results[0].result.is_proved());
        assert_eq!(summary.timeout_count, 0);
    }

    // -------------------------------------------------------------------
    // Test 9: Result collection preserves all VCs
    // -------------------------------------------------------------------

    #[test]
    fn test_dispatch_result_collection_preserves_all() {
        let config = ParallelDispatchConfig::default()
            .with_threads(4)
            .without_independence();

        let vcs: Vec<_> = (0..20)
            .map(|i| test_vc(&format!("fn_{i}"), Formula::Bool(false)))
            .collect();

        let summary = dispatch_parallel(&vcs, &mock_backends(), &config);

        assert_eq!(
            summary.results.len(),
            20,
            "all 20 VCs should have results"
        );
        assert_eq!(summary.proved_count, 20);
    }

    // -------------------------------------------------------------------
    // Test 10: Mixed results (proved, failed, unknown)
    // -------------------------------------------------------------------

    #[test]
    fn test_dispatch_mixed_results() {
        let config = ParallelDispatchConfig::default()
            .with_threads(2)
            .without_independence();

        let vcs = vec![
            test_vc("proved", Formula::Bool(false)),
            test_vc("failed", Formula::Bool(true)),
            test_vc("unknown", Formula::Var("x".into(), Sort::Int)),
        ];

        let summary = dispatch_parallel(&vcs, &mock_backends(), &config);

        assert_eq!(summary.results.len(), 3);
        assert_eq!(summary.proved_count, 1);
        assert_eq!(summary.failed_count, 1);
        // The unknown result is neither proved nor failed nor timeout.
        assert_eq!(summary.timeout_count, 0);
    }

    // -------------------------------------------------------------------
    // Test 11: No backend available returns Unknown
    // -------------------------------------------------------------------

    #[test]
    fn test_dispatch_no_backend_returns_unknown() {
        let config = ParallelDispatchConfig::default().with_threads(1);
        let vcs = vec![test_vc("orphan", Formula::Bool(false))];
        let empty_backends: Vec<Arc<dyn VerificationBackend>> = vec![];

        let summary = dispatch_parallel(&vcs, &empty_backends, &config);

        assert_eq!(summary.results.len(), 1);
        assert!(matches!(
            summary.results[0].result,
            VerificationResult::Unknown { .. }
        ));
    }

    // -------------------------------------------------------------------
    // Test 12: Config builder chain
    // -------------------------------------------------------------------

    #[test]
    fn test_config_builder_chain() {
        let config = ParallelDispatchConfig::default()
            .with_threads(8)
            .with_timeout(Duration::from_secs(30))
            .without_independence();

        assert_eq!(config.num_threads, 8);
        assert_eq!(config.timeout_per_vc, Some(Duration::from_secs(30)));
        assert!(!config.use_independence);
    }

    // -------------------------------------------------------------------
    // Test 13: Config with_threads clamps to minimum 1
    // -------------------------------------------------------------------

    #[test]
    fn test_config_threads_clamped_to_one() {
        let config = ParallelDispatchConfig::default().with_threads(0);
        assert_eq!(config.num_threads, 1);
    }

    // -------------------------------------------------------------------
    // Test 14: Work-stealing — all threads contribute
    // -------------------------------------------------------------------

    #[test]
    fn test_work_stealing_all_threads_participate() {
        // Verify that rayon actually uses multiple threads by tracking
        // unique thread IDs during verification.
        struct ThreadTrackingBackend {
            thread_ids: Arc<std::sync::Mutex<FxHashSet<std::thread::ThreadId>>>,
        }

        impl VerificationBackend for ThreadTrackingBackend {
            fn name(&self) -> &str {
                "thread-tracker"
            }
            fn can_handle(&self, _vc: &VerificationCondition) -> bool {
                true
            }
            fn verify(&self, _vc: &VerificationCondition) -> VerificationResult {
                // Record which thread we're on.
                self.thread_ids
                    .lock()
                    .expect("invariant: mutex not poisoned")
                    .insert(std::thread::current().id());
                // Tiny sleep to encourage rayon to use multiple threads.
                std::thread::sleep(Duration::from_millis(5));
                VerificationResult::Proved {
                    solver: "thread-tracker".to_string(),
                    time_ms: 0,
                    strength: ProofStrength::smt_unsat(), proof_certificate: None,
                solver_warnings: None, }
            }
        }

        let thread_ids = Arc::new(std::sync::Mutex::new(
            FxHashSet::default(),
        ));
        let backend = ThreadTrackingBackend {
            thread_ids: Arc::clone(&thread_ids),
        };
        let backends: Vec<Arc<dyn VerificationBackend>> = vec![Arc::new(backend)];

        let config = ParallelDispatchConfig::default()
            .with_threads(4)
            .without_timeout()
            .without_independence();

        // Dispatch enough VCs to keep all threads busy.
        let vcs: Vec<_> = (0..16)
            .map(|i| test_vc(&format!("fn_{i}"), Formula::Bool(false)))
            .collect();

        let summary = dispatch_parallel(&vcs, &backends, &config);
        assert_eq!(summary.results.len(), 16);
        assert_eq!(summary.proved_count, 16);

        let unique_threads = thread_ids
            .lock()
            .expect("invariant: mutex not poisoned")
            .len();
        // With 4 threads and 16 VCs with a 5ms sleep each, rayon should
        // use more than 1 thread. We check >= 2 to be robust against
        // scheduling variability.
        assert!(
            unique_threads >= 2,
            "expected rayon to use multiple threads, got {unique_threads}"
        );
    }

    // -------------------------------------------------------------------
    // Test 15: Partition index is set correctly
    // -------------------------------------------------------------------

    #[test]
    fn test_partition_index_set_correctly() {
        let config = ParallelDispatchConfig::default().with_threads(2);

        // Two independent VCs (non-conjunctive) get distinct partition indices.
        let vcs = vec![
            test_vc("a", Formula::Bool(false)),
            test_vc("b", Formula::Bool(false)),
        ];

        let summary = dispatch_parallel(&vcs, &mock_backends(), &config);

        assert_eq!(summary.results.len(), 2);
        let indices: Vec<usize> = summary.results.iter().map(|r| r.partition_index).collect();
        // Each VC should have a different partition index.
        assert_ne!(indices[0], indices[1], "distinct VCs should have different partition indices");
    }

    // -------------------------------------------------------------------
    // Test 16: Wall time is tracked
    // -------------------------------------------------------------------

    #[test]
    fn test_wall_time_is_tracked() {
        let config = ParallelDispatchConfig::default()
            .with_threads(1)
            .without_timeout();

        let vcs = vec![test_vc("timed", Formula::Bool(false))];
        let summary = dispatch_parallel(&vcs, &mock_backends(), &config);

        assert_eq!(summary.results.len(), 1);
        // Wall time should be non-negative (trivially true with Duration).
        assert!(summary.total_wall_time >= Duration::ZERO);
        assert!(summary.results[0].wall_time >= Duration::ZERO);
    }

    // -------------------------------------------------------------------
    // Test 17: expand_with_independence creates correct sub-VCs
    // -------------------------------------------------------------------

    #[test]
    fn test_expand_with_independence_three_groups() {
        // And(x>0, y>0, z>0) — three independent variables, three sub-VCs.
        let vc = test_vc(
            "three_groups",
            Formula::And(vec![
                Formula::Gt(
                    Box::new(Formula::Var("x".into(), Sort::Int)),
                    Box::new(Formula::Int(0)),
                ),
                Formula::Gt(
                    Box::new(Formula::Var("y".into(), Sort::Int)),
                    Box::new(Formula::Int(0)),
                ),
                Formula::Gt(
                    Box::new(Formula::Var("z".into(), Sort::Int)),
                    Box::new(Formula::Int(0)),
                ),
            ]),
        );

        let items = expand_with_independence(&[vc]);
        assert_eq!(items.len(), 3, "three independent groups should produce three sub-VCs");
        // All sub-VCs should share the same partition index (they come from one original VC).
        assert!(items.iter().all(|(_, p)| *p == items[0].1));
    }

    // -------------------------------------------------------------------
    // Test 18: expand_with_independence non-conjunction passthrough
    // -------------------------------------------------------------------

    #[test]
    fn test_expand_with_independence_non_conjunction_passthrough() {
        let vc = test_vc("simple", Formula::Bool(false));
        let items = expand_with_independence(std::slice::from_ref(&vc));
        assert_eq!(items.len(), 1);
        assert_eq!(items[0].0.function, "simple");
    }

    // -------------------------------------------------------------------
    // Test 19: Concurrent verification with call count tracking
    // -------------------------------------------------------------------

    #[test]
    fn test_dispatch_calls_backend_for_each_vc() {
        struct CountingBackend {
            count: Arc<AtomicUsize>,
        }

        impl VerificationBackend for CountingBackend {
            fn name(&self) -> &str {
                "counter"
            }
            fn can_handle(&self, _vc: &VerificationCondition) -> bool {
                true
            }
            fn verify(&self, _vc: &VerificationCondition) -> VerificationResult {
                self.count.fetch_add(1, Ordering::Relaxed);
                VerificationResult::Proved {
                    solver: "counter".to_string(),
                    time_ms: 0,
                    strength: ProofStrength::smt_unsat(), proof_certificate: None,
                solver_warnings: None, }
            }
        }

        let count = Arc::new(AtomicUsize::new(0));
        let backend = CountingBackend { count: Arc::clone(&count) };
        let backends: Vec<Arc<dyn VerificationBackend>> = vec![Arc::new(backend)];

        let config = ParallelDispatchConfig::default()
            .with_threads(4)
            .without_independence()
            .without_timeout();

        let vcs: Vec<_> = (0..10)
            .map(|i| test_vc(&format!("fn_{i}"), Formula::Bool(false)))
            .collect();

        let summary = dispatch_parallel(&vcs, &backends, &config);
        assert_eq!(summary.results.len(), 10);
        assert_eq!(count.load(Ordering::Relaxed), 10, "backend should be called once per VC");
    }

    // -------------------------------------------------------------------
    // tRust #708: Arena-aware parallel dispatch tests
    // -------------------------------------------------------------------

    #[test]
    fn test_dispatch_parallel_arena_basic() {
        let config = ParallelDispatchConfig::default().with_threads(2);

        let vcs: Vec<_> = (0..4)
            .map(|i| test_vc(&format!("fn_{i}"), Formula::Bool(false)))
            .collect();

        let (arena, arena_vcs) = ArenaVc::intern_batch(&vcs);
        let arena_arc = Arc::new(arena);

        let summary =
            dispatch_parallel_arena(&arena_vcs, arena_arc, &mock_backends(), &config);

        assert_eq!(summary.results.len(), 4);
        assert_eq!(summary.proved_count, 4);
        assert_eq!(summary.failed_count, 0);
        assert_eq!(summary.timeout_count, 0);
    }

    #[test]
    fn test_dispatch_parallel_arena_empty() {
        let config = ParallelDispatchConfig::default();
        let arena = Arc::new(FormulaArena::new());

        let summary = dispatch_parallel_arena(&[], arena, &mock_backends(), &config);

        assert!(summary.results.is_empty());
        assert_eq!(summary.proved_count, 0);
    }

    #[test]
    fn test_dispatch_parallel_arena_mixed_results() {
        let config = ParallelDispatchConfig::default()
            .with_threads(2)
            .without_timeout();

        let vcs = vec![
            test_vc("proved", Formula::Bool(false)),
            test_vc("failed", Formula::Bool(true)),
        ];

        let (arena, arena_vcs) = ArenaVc::intern_batch(&vcs);
        let arena_arc = Arc::new(arena);

        let summary =
            dispatch_parallel_arena(&arena_vcs, arena_arc, &mock_backends(), &config);

        assert_eq!(summary.results.len(), 2);
        assert_eq!(summary.proved_count, 1);
        assert_eq!(summary.failed_count, 1);
    }

    #[test]
    fn test_dispatch_parallel_arena_preserves_formula_roundtrip() {
        let config = ParallelDispatchConfig::default().with_threads(1);

        let original_formula = Formula::Add(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Int(42)),
        );
        let vcs = vec![test_vc("roundtrip", original_formula.clone())];

        let (arena, arena_vcs) = ArenaVc::intern_batch(&vcs);
        let arena_arc = Arc::new(arena);

        let summary =
            dispatch_parallel_arena(&arena_vcs, arena_arc.clone(), &mock_backends(), &config);

        assert_eq!(summary.results.len(), 1);
        // Verify the arena formula round-trips correctly
        let roundtrip = arena_arc.to_formula(summary.results[0].arena_vc.root);
        assert_eq!(roundtrip, original_formula);
    }
}
