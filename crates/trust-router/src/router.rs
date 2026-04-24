//! The Router struct: dispatches VCs to verification backends.
//!
//! Author: Andrew Yates <andrew@andrewdyates.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::sync::Arc;

use trust_types::formula_arena::{FormulaArena, FormulaRef};
use trust_types::*;

use crate::{
    ArenaVc, BackendSelection, IndependenceResult, VerificationBackend, cegar_backend,
    independence, memory_guard::MemoryGuard, mock_backend, routing, tla2_backend,
};

/// Routes VCs to appropriate backends.
///
/// tRust: Backends are stored as `Arc<dyn VerificationBackend>` internally
/// to support both sequential and parallel verification modes. The public
/// constructors accept `Box<dyn VerificationBackend>` for backward
/// compatibility and convert to Arc on construction.
/// tRust #676: Router owns an optional shared rayon `ThreadPool` that can be
/// passed to `ParallelDispatchConfig` and `PortfolioRacer` to avoid
/// per-invocation pool creation overhead.
///
/// # Examples
///
/// ```
/// use trust_types::{VerificationCondition, VcKind, Formula, Sort, SourceSpan};
/// use trust_router::{Router, mock_backend::MockBackend};
///
/// // Create a router with the mock backend
/// let router = Router::with_backends(vec![Box::new(MockBackend)]);
///
/// // Build a VC and verify it
/// let vc = VerificationCondition {
///     kind: VcKind::DivisionByZero,
///     function: "my_fn".into(),
///     location: SourceSpan::default(),
///     formula: Formula::Bool(false),
///     contract_metadata: None,
/// };
///
/// let result = router.verify_one(&vc);
/// assert!(result.is_proved());
///
/// // Verify multiple VCs at once
/// let results = router.verify_all(&[vc]);
/// assert_eq!(results.len(), 1);
/// ```
pub struct Router {
    // tRust: Arc storage enables zero-copy sharing with parallel threads.
    backends: Vec<Arc<dyn VerificationBackend>>,
    // tRust #676: Shared rayon thread pool for parallel dispatch and portfolio racing.
    thread_pool: Option<Arc<rayon::ThreadPool>>,
    // tRust #882: Process memory guard — checks RSS before each solver dispatch.
    memory_guard: MemoryGuard,
}

impl Router {
    /// Create a router with the mock backend only.
    ///
    /// For real verification, use `Router::with_backends()` and pass in
    /// concrete backend implementations (e.g., Z4Backend from trust-driver).
    pub fn new() -> Self {
        Router {
            backends: vec![Arc::new(mock_backend::MockBackend)],
            thread_pool: None,
            memory_guard: MemoryGuard::default(),
        }
    }

    /// Create a router with specific backends.
    ///
    /// Accepts `Box<dyn VerificationBackend>` for backward compatibility.
    /// Converts to Arc internally to support parallel verification.
    pub fn with_backends(backends: Vec<Box<dyn VerificationBackend>>) -> Self {
        Router {
            backends: backends.into_iter().map(Arc::from).collect(),
            thread_pool: None,
            memory_guard: MemoryGuard::default(),
        }
    }

    /// tRust: Create a router that includes the CEGAR predicate abstraction backend.
    ///
    /// Convenience constructor that prepends the CEGAR backend to the given
    /// backends list.  VCs whose `cegar_classifier` score exceeds the threshold
    /// will be dispatched to the CEGAR refinement loop; others fall through to
    /// the remaining backends.
    pub fn with_cegar(
        cegar_config: cegar_backend::CegarBackendConfig,
        other_backends: Vec<Box<dyn VerificationBackend>>,
    ) -> Self {
        let mut backends: Vec<Arc<dyn VerificationBackend>> =
            Vec::with_capacity(1 + other_backends.len());
        backends.push(Arc::new(cegar_backend::CegarBackend::with_config(cegar_config)));
        backends.extend(other_backends.into_iter().map(Arc::from));
        Router { backends, thread_pool: None, memory_guard: MemoryGuard::default() }
    }

    // tRust #798: with_z4_direct() removed — z4 integration now via trust-zani-lib (Pipeline v2).
    // tRust #798: with_sunder_native() removed — sunder integration now via trust-sunder-lib (Pipeline v2).

    /// tRust: Create a router with Arc-wrapped backends for parallel use.
    ///
    /// Use this when you already have Arc-wrapped backends (e.g., when
    /// sharing backends between a Router and standalone parallel functions).
    pub fn with_arc_backends(backends: Vec<Arc<dyn VerificationBackend>>) -> Self {
        Router { backends, thread_pool: None, memory_guard: MemoryGuard::default() }
    }

    /// tRust #676: Set a shared rayon thread pool on this router.
    ///
    /// The pool is accessible via `thread_pool()` and can be passed to
    /// `ParallelDispatchConfig::with_thread_pool()` and
    /// `PortfolioRacer::with_thread_pool()` to avoid per-call pool creation.
    #[must_use]
    pub fn with_thread_pool(mut self, pool: Arc<rayon::ThreadPool>) -> Self {
        self.thread_pool = Some(pool);
        self
    }

    /// tRust #882: Set a custom memory guard on this router.
    ///
    /// The guard's `check_memory()` is called before each solver dispatch.
    /// Use `MemoryGuard::new(limit_mb)` to set the limit, or
    /// `MemoryGuard::new(0)` to disable enforcement.
    #[must_use]
    pub fn with_memory_guard(mut self, guard: MemoryGuard) -> Self {
        self.memory_guard = guard;
        self
    }

    /// tRust #882: Get a reference to the router's memory guard.
    #[must_use]
    pub fn memory_guard(&self) -> &MemoryGuard {
        &self.memory_guard
    }

    /// tRust #676: Get the shared thread pool, if configured.
    #[must_use]
    pub fn thread_pool(&self) -> Option<&Arc<rayon::ThreadPool>> {
        self.thread_pool.as_ref()
    }

    /// tRust: Get a clone of the Arc-wrapped backend list.
    ///
    /// Useful for passing backends to standalone parallel functions
    /// without re-wrapping.
    pub fn arc_backends(&self) -> Vec<Arc<dyn VerificationBackend>> {
        self.backends.clone()
    }

    /// tRust: Return the backend selection plan for a VC.
    ///
    /// The plan is ordered by router heuristics, not by insertion order:
    /// the preferred backend family for the VC's proof level is tried first,
    /// then fallback families, then general-purpose backends.
    pub fn backend_plan(&self, vc: &VerificationCondition) -> Vec<BackendSelection> {
        routing::backend_plan(&self.backends, vc)
    }

    /// Verify all VCs, returning paired results.
    pub fn verify_all(
        &self,
        vcs: &[VerificationCondition],
    ) -> Vec<(VerificationCondition, VerificationResult)> {
        vcs.iter()
            .map(|vc| {
                let result = self.verify_one(vc);
                (vc.clone(), result)
            })
            .collect()
    }

    /// Verify a single VC by finding an appropriate backend.
    ///
    /// tRust #882: Checks process RSS against the configured memory limit
    /// before dispatching to a solver backend. Returns an Unknown result
    /// with the memory error reason if the limit is exceeded.
    pub fn verify_one(&self, vc: &VerificationCondition) -> VerificationResult {
        // tRust #882: Pre-dispatch memory check.
        if let Some(result) = self.check_memory_limit() {
            return result;
        }

        if let Some(backend) = routing::select_backend(&self.backends, vc) {
            return backend.verify(vc);
        }

        VerificationResult::Unknown {
            solver: "none".into(),
            time_ms: 0,
            reason: "no backend can handle this VC".to_string(),
        }
    }

    /// tRust: Verify all VCs using bounded thread parallelism.
    ///
    /// For a single VC or `max_threads <= 1`, falls back to sequential
    /// `verify_all` to avoid thread overhead. Otherwise splits VCs into
    /// chunks and verifies each chunk on a separate thread.
    ///
    /// `max_threads` bounds concurrency (clamped to `1..=vcs.len()`).
    pub fn verify_all_parallel(
        &self,
        vcs: &[VerificationCondition],
        max_threads: usize,
    ) -> Vec<(VerificationCondition, VerificationResult)> {
        // tRust: Sequential fallback for trivial cases.
        if vcs.is_empty() {
            return Vec::new();
        }
        if vcs.len() <= 1 || max_threads <= 1 {
            return self.verify_all(vcs);
        }

        // tRust #970: Inlined from deleted parallel.rs — simple chunked threading.
        let max_threads = max_threads.min(vcs.len()).max(1);
        let backends = Arc::new(self.backends.clone());
        let chunk_size = vcs.len().div_ceil(max_threads);
        let chunks: Vec<Vec<VerificationCondition>> =
            vcs.chunks(chunk_size).map(|c| c.to_vec()).collect();

        let mut handles = Vec::with_capacity(chunks.len());
        for chunk in chunks {
            let backends = Arc::clone(&backends);
            let handle = std::thread::spawn(move || {
                let mut results = Vec::with_capacity(chunk.len());
                for vc in &chunk {
                    let result = crate::select_backend(backends.as_slice(), vc)
                        .map(|backend| backend.verify(vc))
                        .unwrap_or_else(|| VerificationResult::Unknown {
                            solver: "none".into(),
                            time_ms: 0,
                            reason: "no backend can handle this VC".to_string(),
                        });
                    results.push((vc.clone(), result));
                }
                results
            });
            handles.push(handle);
        }

        let mut all_results = Vec::with_capacity(vcs.len());
        for handle in handles {
            if let Ok(chunk_results) = handle.join() {
                all_results.extend(chunk_results);
            }
        }
        all_results
    }

    /// tRust #529: Verify all VCs using portfolio dispatch.
    ///
    /// For each VC, selects the first capable backend and verifies sequentially.
    /// tRust #970: Portfolio racing removed — pipeline-v2 uses MirRouter instead.
    pub fn verify_all_portfolio(
        &self,
        vcs: &[VerificationCondition],
    ) -> Vec<(VerificationCondition, VerificationResult)> {
        self.verify_all(vcs)
    }

    /// tRust #441: Verify a single VC with constraint independence optimization.
    ///
    /// If the VC's formula is a conjunction (`And([f1, f2, ...])`), partitions
    /// the conjuncts into independent groups (groups sharing no free variables)
    /// and dispatches each group separately. This is the KLEE-inspired
    /// constraint independence optimization applied at the router dispatch level.
    ///
    /// For the overall VC to be proved, ALL partitions must be proved (UNSAT).
    /// If any partition fails, the overall result is failure. The result includes
    /// the partition count for diagnostics.
    ///
    /// Falls back to `verify_one` when the formula is not a conjunction or
    /// all conjuncts share variables (single partition).
    pub fn verify_with_independence(&self, vc: &VerificationCondition) -> IndependenceResult {
        let conjuncts = match &vc.formula {
            Formula::And(children) if children.len() > 1 => children.as_slice(),
            _ => {
                return IndependenceResult {
                    result: self.verify_one(vc),
                    was_split: false,
                    partition_count: 1,
                };
            }
        };

        let groups = independence::partition_independent(conjuncts);
        let partition_count = groups.len();

        if partition_count <= 1 {
            return IndependenceResult {
                result: self.verify_one(vc),
                was_split: false,
                partition_count: 1,
            };
        }

        // Solve each independent partition as a sub-VC.
        let mut total_time_ms: u64 = 0;
        let mut last_solver = trust_types::Symbol::intern("");

        for group in &groups {
            let sub_formula = match group.len() {
                1 => group[0].clone(),
                _ => Formula::And(group.clone()),
            };

            let sub_vc = VerificationCondition {
                formula: sub_formula,
                kind: vc.kind.clone(),
                function: vc.function,
                location: vc.location.clone(),
                contract_metadata: vc.contract_metadata,
            };

            let sub_result = self.verify_one(&sub_vc);

            match &sub_result {
                VerificationResult::Proved { time_ms, solver, .. } => {
                    total_time_ms += time_ms;
                    last_solver = *solver;
                    // This partition proved, continue to next.
                }
                VerificationResult::Failed { .. }
                | VerificationResult::Unknown { .. }
                | VerificationResult::Timeout { .. } => {
                    // Any non-proof result means the overall result is not proved.
                    return IndependenceResult {
                        result: sub_result,
                        was_split: true,
                        partition_count,
                    };
                }
                _ => {
                    // Gracefully handle any future VerificationResult variants
                    // by treating them as non-proof results.
                    return IndependenceResult {
                        result: sub_result,
                        was_split: true,
                        partition_count,
                    };
                }
            }
        }

        // All partitions proved.
        IndependenceResult {
            result: VerificationResult::Proved {
                solver: if last_solver.is_empty() { "independence".into() } else { last_solver },
                time_ms: total_time_ms,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: None,
                solver_warnings: None,
            },
            was_split: true,
            partition_count,
        }
    }

    /// tRust: Verify a single VC and replay any counterexample through symex.
    ///
    /// When the solver returns `Failed` with a counterexample, replays the
    /// counterexample concretely using the function's basic blocks to classify
    /// it as a real bug or spurious path. The replay result is returned
    /// alongside the original solver result.
    ///
    /// Pass `None` for `blocks` to skip replay (e.g., when MIR is unavailable).
    pub fn verify_and_replay(
        &self,
        vc: &VerificationCondition,
        blocks: Option<&[BasicBlock]>,
        replay_config: &crate::replay::ReplayConfig,
    ) -> (VerificationResult, Option<Result<crate::replay::ReplayResult, crate::replay::ReplayError>>)
    {
        let result = self.verify_one(vc);

        // Only replay when we have a counterexample and blocks.
        let replay_result = match (&result, blocks) {
            (VerificationResult::Failed { counterexample: Some(cex), .. }, Some(blks)) => {
                Some(crate::replay::replay_counterexample(cex, vc, blks, replay_config))
            }
            _ => None,
        };

        (result, replay_result)
    }

    /// tRust #683: Verify temporal VCs that carry an associated StateMachine.
    ///
    /// Unlike `verify_all`, these VCs were produced by the temporal discovery
    /// pipeline and each comes with an explicit `StateMachine`. The Tla2Backend
    /// requires this machine for BFS exploration and deadlock/dead-state analysis.
    ///
    /// Dispatches through the standard backend selection: if a Temporal backend
    /// is registered, it uses `Tla2Backend::verify_with_machine`; otherwise
    /// falls through to general backends.
    pub fn verify_temporal_vcs(
        &self,
        vcs: &[(VerificationCondition, trust_temporal::StateMachine)],
    ) -> Vec<(VerificationCondition, VerificationResult)> {
        vcs.iter()
            .map(|(vc, machine)| {
                // tRust #683: Try Tla2Backend::verify_with_machine directly for
                // temporal VCs with an accompanying state machine.
                let result = tla2_backend::Tla2Backend::verify_with_machine(vc, machine);
                (vc.clone(), result)
            })
            .collect()
    }

    // -------------------------------------------------------------------
    // tRust #708: Arena-aware verification dispatch
    // -------------------------------------------------------------------

    /// tRust #708: Verify a single VC using arena-aware dispatch.
    ///
    /// Selects the best backend (same heuristics as `verify_one`) and calls
    /// `verify_arena` on it, passing the arena and root ref so arena-native
    /// backends can avoid the `to_formula()` round-trip.
    pub fn verify_one_arena(
        &self,
        vc: &VerificationCondition,
        root: FormulaRef,
        arena: &FormulaArena,
    ) -> VerificationResult {
        // tRust #882: Pre-dispatch memory check.
        if let Some(result) = self.check_memory_limit() {
            return result;
        }

        if let Some(backend) = routing::select_backend(&self.backends, vc) {
            return backend.verify_arena(vc, root, arena);
        }
        VerificationResult::Unknown {
            solver: "none".into(),
            time_ms: 0,
            reason: "no backend can handle this VC".to_string(),
        }
    }

    /// tRust #708: Verify all VCs using arena-aware dispatch.
    ///
    /// Each `ArenaVc` carries both a materialized `VerificationCondition`
    /// (for `can_handle` / routing) and a `FormulaRef` root into the shared
    /// arena. The arena is passed by shared reference; for parallel dispatch
    /// use `verify_all_arena_parallel`.
    pub fn verify_all_arena(
        &self,
        vcs: &[ArenaVc],
        arena: &FormulaArena,
    ) -> Vec<(VerificationCondition, VerificationResult)> {
        vcs.iter()
            .map(|avc| {
                let result = self.verify_one_arena(&avc.vc, avc.root, arena);
                (avc.vc.clone(), result)
            })
            .collect()
    }

    /// tRust #708: Verify all VCs in parallel using arena-aware dispatch.
    ///
    /// The arena is wrapped in `Arc` for safe sharing across rayon threads.
    /// Falls back to sequential `verify_all_arena` for single VCs or
    /// `max_threads <= 1`.
    pub fn verify_all_arena_parallel(
        &self,
        vcs: &[ArenaVc],
        arena: Arc<FormulaArena>,
        max_threads: usize,
    ) -> Vec<(VerificationCondition, VerificationResult)> {
        if vcs.len() <= 1 || max_threads <= 1 {
            return self.verify_all_arena(vcs, &arena);
        }

        let backends = self.backends.clone();
        let vcs_owned: Vec<ArenaVc> = vcs.to_vec();

        // tRust #708: Use rayon parallel iterator with Arc<FormulaArena>.
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(max_threads.clamp(1, vcs.len()))
            .build()
            // tRust #734: rayon pool creation failure is a real system-level error.
            .expect("rayon thread pool creation failed");

        pool.install(|| {
            use rayon::prelude::*;
            vcs_owned
                .par_iter()
                .map(|avc| {
                    let backend = routing::select_backend(&backends, &avc.vc);
                    let result = match backend {
                        Some(b) => b.verify_arena(&avc.vc, avc.root, &arena),
                        None => VerificationResult::Unknown {
                            solver: "none".into(),
                            time_ms: 0,
                            reason: "no backend can handle this VC".to_string(),
                        },
                    };
                    (avc.vc.clone(), result)
                })
                .collect()
        })
    }

    // tRust #791: Pipeline v2 MIR-level dispatch methods

    /// tRust #791: Verify a single function using the v2 MIR-level pipeline.
    #[cfg(feature = "pipeline-v2")]
    pub fn verify_function_v2(
        mir_router: &crate::mir_router::MirRouter,
        func: &trust_types::VerifiableFunction,
    ) -> crate::verification_obligation::VerificationObligation {
        let strategy = mir_router.classify(func);
        let result = mir_router.verify_with_strategy(func, &strategy);
        let kind = crate::verification_obligation::vc_kind_for_mir_strategy(&strategy);
        crate::verification_obligation::VerificationObligation::new(
            func.def_path.clone(),
            func.name.clone(),
            func.span.clone(),
            kind,
        )
        .with_strategy(strategy)
        .with_result(result)
    }

    /// tRust #791: Verify multiple functions using the v2 MIR-level pipeline.
    #[cfg(feature = "pipeline-v2")]
    pub fn verify_functions_v2(
        mir_router: &crate::mir_router::MirRouter,
        funcs: &[trust_types::VerifiableFunction],
    ) -> Vec<crate::verification_obligation::VerificationObligation> {
        funcs.iter().map(|func| Self::verify_function_v2(mir_router, func)).collect()
    }

    // -------------------------------------------------------------------
    // tRust #882: Memory guard integration
    // -------------------------------------------------------------------

    /// tRust #882: Check process memory before solver dispatch.
    ///
    /// Returns `Some(VerificationResult::Unknown { .. })` if the memory
    /// limit is exceeded, or `None` if the check passes (or if the guard
    /// has no limit / query fails gracefully).
    fn check_memory_limit(&self) -> Option<VerificationResult> {
        match self.memory_guard.check_memory() {
            Ok(_snapshot) => None,
            Err(crate::memory_guard::MemoryGuardError::LimitExceeded {
                current_mb,
                limit_mb,
                peak_mb,
            }) => Some(VerificationResult::Unknown {
                solver: "memory-guard".into(),
                time_ms: 0,
                reason: format!(
                    "memory limit exceeded: {current_mb}MB used, {limit_mb}MB limit \
                     (peak: {peak_mb}MB) — skipping solver dispatch"
                ),
            }),
            Err(_query_err) => {
                // Query failure is non-fatal: proceed with dispatch.
                // The guard already logs warnings to stderr.
                None
            }
        }
    }
}

impl Default for Router {
    fn default() -> Self {
        Self::new()
    }
}
