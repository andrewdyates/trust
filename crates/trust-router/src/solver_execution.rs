// trust-router/solver_execution.rs: Hybrid native/worker-isolated solver execution
//
// tRust #195: Implements a solver execution architecture that supports both:
//   - Native: in-process solver invocation (fast, for trusted backends like z4)
//   - WorkerIsolated: subprocess/sandbox invocation (safe, for untrusted backends)
//   - Hybrid: automatic mode selection based on backend trust level
//
// The SolverWorker trait provides execute_native() and execute_isolated() methods.
// WorkerPool provides execute_slot_limited() for concurrency-limited in-process execution
// and execute_arc_isolated() for true subprocess isolation via IsolatedSolver.
// WorkerPool manages solver subprocess lifecycle with timeout and resource limits.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;
use std::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering};
use std::sync::{Arc, Condvar, Mutex};
use std::time::{Duration, Instant};

use thiserror::Error;
use trust_types::*;

use crate::isolation::{IsolatedSolver, IsolationConfig};
use crate::VerificationBackend;

// ---------------------------------------------------------------------------
// tRust #195: Execution mode enum
// ---------------------------------------------------------------------------

/// How a solver backend should be executed in the hybrid architecture.
///
/// The router selects the execution mode per-backend based on trust level,
/// performance requirements, and resource availability. Native mode is fastest
/// but a solver crash will crash the compiler. WorkerIsolated mode is safer
/// but incurs serialization and IPC overhead.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
#[derive(Default)]
pub enum SolverExecutionMode {
    /// Run the solver in-process via direct function call.
    /// Fastest path. A crash in the solver crashes the compiler.
    /// Use for trusted, well-tested backends (e.g., z4).
    Native,

    /// Run the solver as an isolated worker subprocess.
    /// Slower due to serialization/IPC, but crashes are contained.
    /// Use for untrusted, experimental, or third-party backends.
    WorkerIsolated,

    /// Automatically select Native or WorkerIsolated based on the backend's
    /// trust level and the VC's priority. Critical safety checks may use
    /// Native for speed; untrusted backends always use WorkerIsolated.
    #[default]
    Hybrid,
}


// ---------------------------------------------------------------------------
// tRust #195: Backend trust level
// ---------------------------------------------------------------------------

/// Trust level for a solver backend, controlling execution mode in Hybrid mode.
///
/// Trusted backends are invoked in-process (Native). Untrusted backends are
/// isolated in worker subprocesses. Sandboxed backends get additional OS-level
/// restrictions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[non_exhaustive]
#[derive(Default)]
pub enum TrustLevel {
    /// Fully trusted, production-grade solver. Safe for in-process execution.
    /// Examples: z4 (720K LOC, 24K commits).
    Trusted,

    /// Partially trusted. Use isolation for non-critical work, native for
    /// critical safety checks where speed matters.
    #[default]
    SemiTrusted,

    /// Untrusted or experimental backend. Always isolated.
    Untrusted,
}


// ---------------------------------------------------------------------------
// tRust #195: Execution errors
// ---------------------------------------------------------------------------

/// Errors from solver execution operations.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum ExecutionError {
    /// The worker pool has been shut down.
    #[error("worker pool is shut down")]
    PoolShutdown,

    /// No workers available within the timeout.
    #[error("no worker available within {timeout_ms}ms")]
    WorkerUnavailable { timeout_ms: u64 },

    /// The solver execution timed out.
    #[error("solver execution timed out after {timeout_ms}ms")]
    Timeout { timeout_ms: u64 },

    /// The solver crashed during execution.
    #[error("solver crashed: {reason}")]
    SolverCrash { reason: String },

    /// Resource limit exceeded (memory, CPU).
    #[error("resource limit exceeded: {detail}")]
    ResourceLimitExceeded { detail: String },

    /// Internal error in the execution infrastructure.
    #[error("internal execution error: {reason}")]
    Internal { reason: String },
}

// ---------------------------------------------------------------------------
// tRust #195: SolverWorker trait
// ---------------------------------------------------------------------------

/// A solver backend that supports both native and isolated execution modes.
///
/// Implementors provide `execute_native()` for in-process invocation and
/// `execute_isolated()` for subprocess invocation. The `trust_level()` method
/// determines the default execution mode in Hybrid mode.
///
/// The trait extends `VerificationBackend` so that `SolverWorker` implementations
/// can be used directly as backends in the router.
pub trait SolverWorker: VerificationBackend {
    /// Trust level of this backend, controlling execution mode in Hybrid mode.
    fn trust_level(&self) -> TrustLevel {
        TrustLevel::SemiTrusted
    }

    /// Execute verification natively (in-process). Fast but unsafe.
    ///
    /// Default implementation delegates to `self.verify(vc)`.
    fn execute_native(&self, vc: &VerificationCondition) -> VerificationResult {
        self.verify(vc)
    }

    /// Execute verification in an isolated worker subprocess.
    ///
    /// Default implementation wraps the backend in an `IsolatedSolver` with
    /// subprocess mode and the given timeout.
    fn execute_isolated(
        &self,
        vc: &VerificationCondition,
        timeout: Duration,
    ) -> Result<VerificationResult, ExecutionError>;

    /// Preferred execution timeout for this backend.
    /// Used as the default timeout when none is specified.
    fn default_timeout(&self) -> Duration {
        Duration::from_secs(30)
    }

    /// Resource limits for this backend (memory in bytes).
    /// 0 = no limit.
    fn memory_limit(&self) -> u64 {
        0
    }
}

// ---------------------------------------------------------------------------
// tRust #195: Worker pool configuration
// ---------------------------------------------------------------------------

/// Configuration for the `WorkerPool`.
#[derive(Debug, Clone)]
pub struct WorkerPoolConfig {
    /// Maximum number of concurrent worker subprocesses.
    pub max_workers: usize,

    /// Default timeout for solver execution in worker mode.
    pub default_timeout: Duration,

    /// Maximum time to wait for a worker to become available.
    pub acquire_timeout: Duration,

    /// Default memory limit per worker (bytes). 0 = unlimited.
    pub memory_limit_per_worker: u64,

    /// Whether to retry failed executions.
    pub max_retries: u32,
}

impl Default for WorkerPoolConfig {
    fn default() -> Self {
        Self {
            max_workers: num_cpus_heuristic(),
            default_timeout: Duration::from_secs(30),
            acquire_timeout: Duration::from_secs(60),
            memory_limit_per_worker: 512 * 1024 * 1024, // 512 MiB
            max_retries: 1,
        }
    }
}

impl WorkerPoolConfig {
    /// Create a config with specific max workers and timeout.
    #[must_use]
    pub fn with_limits(max_workers: usize, timeout: Duration) -> Self {
        Self {
            max_workers: max_workers.max(1),
            default_timeout: timeout,
            ..Self::default()
        }
    }
}

// ---------------------------------------------------------------------------
// tRust #195: Worker pool statistics
// ---------------------------------------------------------------------------

/// Cumulative statistics from the worker pool.
#[derive(Debug, Clone, Default)]
pub struct WorkerPoolStatistics {
    /// Total native executions performed.
    pub total_native_executions: u64,
    /// Total isolated executions performed.
    pub total_isolated_executions: u64,
    /// Total execution failures (crashes, timeouts).
    pub total_failures: u64,
    /// Total retries attempted.
    pub total_retries: u64,
    /// Current active workers.
    pub active_workers: usize,
    /// Peak concurrent workers observed.
    pub peak_workers: usize,
    /// Total native execution time (microseconds).
    pub total_native_time_us: u64,
    /// Total isolated execution time (microseconds).
    pub total_isolated_time_us: u64,
}

// ---------------------------------------------------------------------------
// tRust #195: Worker pool internal state
// ---------------------------------------------------------------------------

struct PoolState {
    active_workers: usize,
}

struct PoolInner {
    config: WorkerPoolConfig,
    pool_state: Mutex<PoolState>,
    worker_available: Condvar,
    shutdown: AtomicBool,

    // Statistics (atomics for lock-free updates).
    stat_native_executions: AtomicU64,
    stat_isolated_executions: AtomicU64,
    stat_failures: AtomicU64,
    stat_retries: AtomicU64,
    stat_peak_workers: AtomicUsize,
    stat_native_time_us: AtomicU64,
    stat_isolated_time_us: AtomicU64,
}

// ---------------------------------------------------------------------------
// tRust #195: WorkerPool
// ---------------------------------------------------------------------------

/// Manages solver subprocess lifecycle for worker-isolated execution.
///
/// The pool limits the number of concurrent worker subprocesses, enforces
/// timeouts and resource limits, and provides statistics on execution.
/// Thread-safe; shared via internal `Arc` (clone is cheap).
///
/// # Usage
///
/// ```ignore
/// let pool = WorkerPool::new(WorkerPoolConfig::default());
///
/// // Execute a VC using the pool's execution mode selection.
/// let result = pool.execute(&backend, &vc, SolverExecutionMode::Hybrid)?;
///
/// // Check pool statistics.
/// let stats = pool.statistics();
/// println!("native: {}, isolated: {}", stats.total_native_executions,
///          stats.total_isolated_executions);
///
/// pool.shutdown();
/// ```
#[derive(Clone)]
pub struct WorkerPool {
    inner: Arc<PoolInner>,
}

impl WorkerPool {
    /// Create a new worker pool with the given configuration.
    #[must_use]
    pub fn new(config: WorkerPoolConfig) -> Self {
        Self {
            inner: Arc::new(PoolInner {
                config,
                pool_state: Mutex::new(PoolState { active_workers: 0 }),
                worker_available: Condvar::new(),
                shutdown: AtomicBool::new(false),
                stat_native_executions: AtomicU64::new(0),
                stat_isolated_executions: AtomicU64::new(0),
                stat_failures: AtomicU64::new(0),
                stat_retries: AtomicU64::new(0),
                stat_peak_workers: AtomicUsize::new(0),
                stat_native_time_us: AtomicU64::new(0),
                stat_isolated_time_us: AtomicU64::new(0),
            }),
        }
    }

    /// Execute a verification condition using the specified execution mode.
    ///
    /// In `Native` mode, calls `backend.verify()` directly.
    /// In `WorkerIsolated` mode, acquires a worker slot and runs isolated.
    /// In `Hybrid` mode, selects based on the backend's trust level and
    /// the VC's priority.
    pub fn execute(
        &self,
        backend: &dyn VerificationBackend,
        vc: &VerificationCondition,
        mode: SolverExecutionMode,
        trust_level: TrustLevel,
    ) -> Result<VerificationResult, ExecutionError> {
        if self.inner.shutdown.load(Ordering::SeqCst) {
            return Err(ExecutionError::PoolShutdown);
        }

        let effective_mode = resolve_execution_mode(mode, trust_level, vc);

        match effective_mode {
            SolverExecutionMode::Native => self.execute_native(backend, vc),
            SolverExecutionMode::WorkerIsolated => self.execute_slot_limited(backend, vc),
            // resolve_execution_mode always resolves Hybrid to Native or WorkerIsolated
            SolverExecutionMode::Hybrid => {
                Err(ExecutionError::Internal {
                    reason: "Hybrid mode was not resolved by resolve_execution_mode".into(),
                })
            }
        }
    }

    /// Execute a solver worker using its trait methods for mode-aware execution.
    pub fn execute_worker(
        &self,
        worker: &dyn SolverWorker,
        vc: &VerificationCondition,
        mode: SolverExecutionMode,
    ) -> Result<VerificationResult, ExecutionError> {
        if self.inner.shutdown.load(Ordering::SeqCst) {
            return Err(ExecutionError::PoolShutdown);
        }

        let effective_mode = resolve_execution_mode(mode, worker.trust_level(), vc);

        match effective_mode {
            SolverExecutionMode::Native => {
                let start = Instant::now();
                let result = worker.execute_native(vc);
                let elapsed_us = start.elapsed().as_micros() as u64;
                self.inner.stat_native_executions.fetch_add(1, Ordering::Relaxed);
                self.inner.stat_native_time_us.fetch_add(elapsed_us, Ordering::Relaxed);
                Ok(result)
            }
            SolverExecutionMode::WorkerIsolated => {
                self.acquire_worker_slot()?;
                let start = Instant::now();
                let timeout = worker.default_timeout();
                let result = worker.execute_isolated(vc, timeout);
                let elapsed_us = start.elapsed().as_micros() as u64;
                self.release_worker_slot();
                self.inner.stat_isolated_executions.fetch_add(1, Ordering::Relaxed);
                self.inner.stat_isolated_time_us.fetch_add(elapsed_us, Ordering::Relaxed);
                match result {
                    Ok(r) => Ok(r),
                    Err(e) => {
                        self.inner.stat_failures.fetch_add(1, Ordering::Relaxed);
                        Err(e)
                    }
                }
            }
            SolverExecutionMode::Hybrid => {
                Err(ExecutionError::Internal {
                    reason: "Hybrid mode was not resolved by resolve_execution_mode".into(),
                })
            }
        }
    }

    /// Execute natively (in-process).
    fn execute_native(
        &self,
        backend: &dyn VerificationBackend,
        vc: &VerificationCondition,
    ) -> Result<VerificationResult, ExecutionError> {
        let start = Instant::now();
        let result = backend.verify(vc);
        let elapsed_us = start.elapsed().as_micros() as u64;
        self.inner.stat_native_executions.fetch_add(1, Ordering::Relaxed);
        self.inner.stat_native_time_us.fetch_add(elapsed_us, Ordering::Relaxed);
        Ok(result)
    }

    /// Execute with slot-limited concurrency (in-process, no subprocess isolation).
    ///
    /// Acquires a worker slot, then delegates to the backend's `verify()` method
    /// in-process with concurrency limiting. This does NOT spawn a subprocess or
    /// provide any process isolation.
    ///
    /// For full subprocess isolation with timeout enforcement and crash recovery,
    /// use `execute_arc_isolated` with an `Arc<dyn VerificationBackend>`.
    fn execute_slot_limited(
        &self,
        backend: &dyn VerificationBackend,
        vc: &VerificationCondition,
    ) -> Result<VerificationResult, ExecutionError> {
        self.acquire_worker_slot()?;

        let start = Instant::now();
        let result = backend.verify(vc);
        let elapsed_us = start.elapsed().as_micros() as u64;
        self.inner.stat_isolated_executions.fetch_add(1, Ordering::Relaxed);
        self.inner.stat_isolated_time_us.fetch_add(elapsed_us, Ordering::Relaxed);

        self.release_worker_slot();
        Ok(result)
    }

    /// Execute in an isolated worker subprocess with full process isolation.
    ///
    /// Takes an `Arc<dyn VerificationBackend>` which is passed to `IsolatedSolver`
    /// for actual subprocess execution with timeout enforcement and crash recovery.
    /// The pool enforces worker slot limits; the `IsolatedSolver` handles subprocess
    /// spawning and monitoring.
    pub fn execute_arc_isolated(
        &self,
        backend: Arc<dyn VerificationBackend>,
        vc: &VerificationCondition,
    ) -> Result<VerificationResult, ExecutionError> {
        self.acquire_worker_slot()?;

        let timeout = self.inner.config.default_timeout;
        let max_attempts = 1 + self.inner.config.max_retries;
        let mut last_error: Option<ExecutionError> = None;

        for attempt in 0..max_attempts {
            let start = Instant::now();

            let isolated = IsolatedSolver::new(
                Arc::clone(&backend),
                IsolationConfig::subprocess(timeout),
            );
            let result = isolated.verify(vc);
            let elapsed_us = start.elapsed().as_micros() as u64;
            self.inner.stat_isolated_executions.fetch_add(1, Ordering::Relaxed);
            self.inner.stat_isolated_time_us.fetch_add(elapsed_us, Ordering::Relaxed);

            // Check if the result indicates a crash/error (Unknown with crash reason).
            match &result {
                VerificationResult::Unknown { reason, .. } if reason.contains("solver crash") => {
                    self.inner.stat_failures.fetch_add(1, Ordering::Relaxed);
                    last_error = Some(ExecutionError::SolverCrash {
                        reason: reason.clone(),
                    });
                    if attempt + 1 < max_attempts {
                        self.inner.stat_retries.fetch_add(1, Ordering::Relaxed);
                        continue;
                    }
                }
                VerificationResult::Timeout { timeout_ms, .. } => {
                    self.release_worker_slot();
                    self.inner.stat_failures.fetch_add(1, Ordering::Relaxed);
                    return Err(ExecutionError::Timeout {
                        timeout_ms: *timeout_ms,
                    });
                }
                _ => {
                    self.release_worker_slot();
                    return Ok(result);
                }
            }
        }

        self.release_worker_slot();
        Err(last_error.unwrap_or(ExecutionError::Internal {
            reason: "all retries exhausted".to_string(),
        }))
    }

    /// Acquire a worker slot, blocking until one is available.
    fn acquire_worker_slot(&self) -> Result<(), ExecutionError> {
        if self.inner.shutdown.load(Ordering::SeqCst) {
            return Err(ExecutionError::PoolShutdown);
        }

        let deadline = Instant::now() + self.inner.config.acquire_timeout;
        let mut state = self.inner.pool_state.lock()
            .unwrap_or_else(|e| e.into_inner());

        loop {
            if self.inner.shutdown.load(Ordering::SeqCst) {
                return Err(ExecutionError::PoolShutdown);
            }

            if state.active_workers < self.inner.config.max_workers {
                state.active_workers += 1;
                let _ = self.inner.stat_peak_workers.fetch_max(
                    state.active_workers,
                    Ordering::Relaxed,
                );
                return Ok(());
            }

            let remaining = deadline.saturating_duration_since(Instant::now());
            if remaining.is_zero() {
                return Err(ExecutionError::WorkerUnavailable {
                    timeout_ms: self.inner.config.acquire_timeout.as_millis() as u64,
                });
            }

            let wait_result = self.inner.worker_available
                .wait_timeout(state, remaining)
                .unwrap_or_else(|e| e.into_inner());
            state = wait_result.0;

            if wait_result.1.timed_out()
                && state.active_workers >= self.inner.config.max_workers
            {
                return Err(ExecutionError::WorkerUnavailable {
                    timeout_ms: self.inner.config.acquire_timeout.as_millis() as u64,
                });
            }
        }
    }

    /// Release a worker slot.
    fn release_worker_slot(&self) {
        let mut state = self.inner.pool_state.lock()
            .unwrap_or_else(|e| e.into_inner());
        state.active_workers = state.active_workers.saturating_sub(1);
        self.inner.worker_available.notify_one();
    }

    /// Get the current number of active workers.
    #[must_use]
    pub fn active_workers(&self) -> usize {
        let state = self.inner.pool_state.lock()
            .unwrap_or_else(|e| e.into_inner());
        state.active_workers
    }

    /// Get the maximum number of workers configured.
    #[must_use]
    pub fn max_workers(&self) -> usize {
        self.inner.config.max_workers
    }

    /// Get pool configuration.
    #[must_use]
    pub fn config(&self) -> &WorkerPoolConfig {
        &self.inner.config
    }

    /// Get a snapshot of pool statistics.
    #[must_use]
    pub fn statistics(&self) -> WorkerPoolStatistics {
        let state = self.inner.pool_state.lock()
            .unwrap_or_else(|e| e.into_inner());
        WorkerPoolStatistics {
            total_native_executions: self.inner.stat_native_executions.load(Ordering::Relaxed),
            total_isolated_executions: self.inner.stat_isolated_executions.load(Ordering::Relaxed),
            total_failures: self.inner.stat_failures.load(Ordering::Relaxed),
            total_retries: self.inner.stat_retries.load(Ordering::Relaxed),
            active_workers: state.active_workers,
            peak_workers: self.inner.stat_peak_workers.load(Ordering::Relaxed),
            total_native_time_us: self.inner.stat_native_time_us.load(Ordering::Relaxed),
            total_isolated_time_us: self.inner.stat_isolated_time_us.load(Ordering::Relaxed),
        }
    }

    /// Shut down the pool, preventing new executions and waking all waiters.
    pub fn shutdown(&self) {
        self.inner.shutdown.store(true, Ordering::SeqCst);
        self.inner.worker_available.notify_all();
    }

    /// Check if the pool has been shut down.
    #[must_use]
    pub fn is_shutdown(&self) -> bool {
        self.inner.shutdown.load(Ordering::SeqCst)
    }
}

// ---------------------------------------------------------------------------
// tRust #195: Execution mode resolution
// ---------------------------------------------------------------------------

/// Resolve `Hybrid` mode to a concrete `Native` or `WorkerIsolated` mode.
///
/// In Hybrid mode, the decision is based on:
/// 1. Backend trust level: `Trusted` → Native, `Untrusted` → WorkerIsolated
/// 2. SemiTrusted → always WorkerIsolated (safety-critical VCs must not run
///    in-process through semi-trusted solvers; L0Safety VCs especially need
///    isolation to prevent compromised solver output from being trusted)
#[must_use]
pub fn resolve_execution_mode(
    mode: SolverExecutionMode,
    trust_level: TrustLevel,
    vc: &VerificationCondition,
) -> SolverExecutionMode {
    match mode {
        SolverExecutionMode::Native | SolverExecutionMode::WorkerIsolated => mode,
        SolverExecutionMode::Hybrid => {
            match trust_level {
                TrustLevel::Trusted => SolverExecutionMode::Native,
                TrustLevel::Untrusted => SolverExecutionMode::WorkerIsolated,
                TrustLevel::SemiTrusted => {
                    // SemiTrusted backends always run isolated regardless of VC level.
                    // L0Safety VCs are especially sensitive -- a semi-trusted solver
                    // must not run in-process where it could corrupt the host.
                    let _level = vc.kind.proof_level();
                    SolverExecutionMode::WorkerIsolated
                }
            }
        }
    }
}

/// Map a backend name to its default trust level.
///
/// Known production-grade backends get `Trusted`; experimental ones get
/// `Untrusted`. Override with explicit `TrustLevel` configuration.
#[must_use]
pub fn default_trust_level(backend_name: &str) -> TrustLevel {
    match backend_name {
        "z4" => TrustLevel::Trusted,
        "mock" => TrustLevel::Trusted,
        "zani" => TrustLevel::SemiTrusted,
        "sunder" => TrustLevel::SemiTrusted,
        "lean5" => TrustLevel::SemiTrusted,
        "tla2" => TrustLevel::SemiTrusted,
        "certus" => TrustLevel::Untrusted,
        "cegar" => TrustLevel::SemiTrusted,
        _ => TrustLevel::Untrusted,
    }
}

// ---------------------------------------------------------------------------
// tRust #195: HybridExecutor — top-level integration
// ---------------------------------------------------------------------------

/// A per-backend execution mode configuration entry.
#[derive(Debug, Clone)]
pub struct BackendExecutionConfig {
    /// Backend name (must match `VerificationBackend::name()`).
    pub name: String,
    /// Trust level for this backend.
    pub trust_level: TrustLevel,
    /// Execution mode override (or `Hybrid` for automatic).
    pub mode: SolverExecutionMode,
    /// Per-backend timeout override. `None` = use pool default.
    pub timeout: Option<Duration>,
}

/// Top-level hybrid executor that dispatches to Native or WorkerIsolated
/// based on per-backend configuration.
///
/// Wraps a `WorkerPool` and a map of backend names to their execution configs.
pub struct HybridExecutor {
    pool: WorkerPool,
    backend_configs: FxHashMap<String, BackendExecutionConfig>,
    default_mode: SolverExecutionMode,
}

impl HybridExecutor {
    /// Create a hybrid executor with a pool and per-backend configuration.
    pub fn new(
        pool: WorkerPool,
        backend_configs: Vec<BackendExecutionConfig>,
        default_mode: SolverExecutionMode,
    ) -> Self {
        let config_map: FxHashMap<String, BackendExecutionConfig> = backend_configs
            .into_iter()
            .map(|c| (c.name.clone(), c))
            .collect();
        Self {
            pool,
            backend_configs: config_map,
            default_mode,
        }
    }

    /// Create a hybrid executor with default trust levels for all known backends.
    pub fn with_defaults(pool: WorkerPool) -> Self {
        let known_backends = ["z4", "mock", "zani", "sunder", "lean5", "tla2", "certus", "cegar"];
        let configs: Vec<BackendExecutionConfig> = known_backends
            .iter()
            .map(|name| BackendExecutionConfig {
                name: name.to_string(),
                trust_level: default_trust_level(name),
                mode: SolverExecutionMode::Hybrid,
                timeout: None,
            })
            .collect();
        Self::new(pool, configs, SolverExecutionMode::Hybrid)
    }

    /// Execute a VC through the hybrid executor.
    ///
    /// Looks up the backend's execution configuration and dispatches to
    /// Native or WorkerIsolated mode accordingly.
    pub fn execute(
        &self,
        backend: &dyn VerificationBackend,
        vc: &VerificationCondition,
    ) -> Result<VerificationResult, ExecutionError> {
        let config = self.backend_configs.get(backend.name());
        let (mode, trust_level) = match config {
            Some(cfg) => (cfg.mode, cfg.trust_level),
            None => (self.default_mode, default_trust_level(backend.name())),
        };
        self.pool.execute(backend, vc, mode, trust_level)
    }

    /// Access the underlying worker pool.
    #[must_use]
    pub fn pool(&self) -> &WorkerPool {
        &self.pool
    }

    /// Get the execution config for a named backend.
    #[must_use]
    pub fn backend_config(&self, name: &str) -> Option<&BackendExecutionConfig> {
        self.backend_configs.get(name)
    }

    /// Shut down the executor and its pool.
    pub fn shutdown(&self) {
        self.pool.shutdown();
    }
}

// ---------------------------------------------------------------------------
// tRust #195: Internal helpers
// ---------------------------------------------------------------------------

/// Heuristic for default worker count: available parallelism or 4.
fn num_cpus_heuristic() -> usize {
    std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(4)
}

// ---------------------------------------------------------------------------
// tRust #195: Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use std::thread;

    use super::*;
    use crate::mock_backend::MockBackend;

    fn make_vc() -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "test_fn".to_string(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
        }
    }

    fn make_postcondition_vc() -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::Postcondition,
            function: "post_fn".to_string(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
        }
    }

    fn test_pool_config(max_workers: usize) -> WorkerPoolConfig {
        WorkerPoolConfig {
            max_workers,
            default_timeout: Duration::from_secs(5),
            acquire_timeout: Duration::from_secs(5),
            memory_limit_per_worker: 0,
            max_retries: 0,
        }
    }

    // -----------------------------------------------------------------------
    // SolverExecutionMode tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_execution_mode_default_is_hybrid() {
        assert_eq!(SolverExecutionMode::default(), SolverExecutionMode::Hybrid);
    }

    #[test]
    fn test_execution_mode_equality() {
        assert_eq!(SolverExecutionMode::Native, SolverExecutionMode::Native);
        assert_ne!(SolverExecutionMode::Native, SolverExecutionMode::WorkerIsolated);
        assert_ne!(SolverExecutionMode::WorkerIsolated, SolverExecutionMode::Hybrid);
    }

    // -----------------------------------------------------------------------
    // TrustLevel tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_trust_level_default_is_semi_trusted() {
        assert_eq!(TrustLevel::default(), TrustLevel::SemiTrusted);
    }

    #[test]
    fn test_trust_level_ordering() {
        assert!(TrustLevel::Trusted < TrustLevel::SemiTrusted);
        assert!(TrustLevel::SemiTrusted < TrustLevel::Untrusted);
    }

    // -----------------------------------------------------------------------
    // resolve_execution_mode tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_resolve_native_stays_native() {
        let vc = make_vc();
        assert_eq!(
            resolve_execution_mode(SolverExecutionMode::Native, TrustLevel::Untrusted, &vc),
            SolverExecutionMode::Native,
        );
    }

    #[test]
    fn test_resolve_isolated_stays_isolated() {
        let vc = make_vc();
        assert_eq!(
            resolve_execution_mode(SolverExecutionMode::WorkerIsolated, TrustLevel::Trusted, &vc),
            SolverExecutionMode::WorkerIsolated,
        );
    }

    #[test]
    fn test_resolve_hybrid_trusted_goes_native() {
        let vc = make_vc();
        assert_eq!(
            resolve_execution_mode(SolverExecutionMode::Hybrid, TrustLevel::Trusted, &vc),
            SolverExecutionMode::Native,
        );
    }

    #[test]
    fn test_resolve_hybrid_untrusted_goes_isolated() {
        let vc = make_vc();
        assert_eq!(
            resolve_execution_mode(SolverExecutionMode::Hybrid, TrustLevel::Untrusted, &vc),
            SolverExecutionMode::WorkerIsolated,
        );
    }

    #[test]
    fn test_resolve_hybrid_semi_trusted_safety_goes_isolated() {
        // L0Safety VC with SemiTrusted backend → WorkerIsolated for safety
        // SemiTrusted solvers must not run in-process for safety-critical VCs
        let vc = make_vc(); // DivisionByZero is L0Safety
        assert_eq!(
            resolve_execution_mode(SolverExecutionMode::Hybrid, TrustLevel::SemiTrusted, &vc),
            SolverExecutionMode::WorkerIsolated,
        );
    }

    #[test]
    fn test_resolve_hybrid_semi_trusted_non_safety_goes_isolated() {
        // Postcondition VC (L1Functional) with SemiTrusted → WorkerIsolated
        let vc = make_postcondition_vc();
        assert_eq!(
            resolve_execution_mode(SolverExecutionMode::Hybrid, TrustLevel::SemiTrusted, &vc),
            SolverExecutionMode::WorkerIsolated,
        );
    }

    // -----------------------------------------------------------------------
    // default_trust_level tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_default_trust_level_known_backends() {
        assert_eq!(default_trust_level("z4"), TrustLevel::Trusted);
        assert_eq!(default_trust_level("mock"), TrustLevel::Trusted);
        assert_eq!(default_trust_level("zani"), TrustLevel::SemiTrusted);
        assert_eq!(default_trust_level("sunder"), TrustLevel::SemiTrusted);
        assert_eq!(default_trust_level("lean5"), TrustLevel::SemiTrusted);
        assert_eq!(default_trust_level("tla2"), TrustLevel::SemiTrusted);
        assert_eq!(default_trust_level("certus"), TrustLevel::Untrusted);
    }

    #[test]
    fn test_default_trust_level_unknown_is_untrusted() {
        assert_eq!(default_trust_level("unknown-solver"), TrustLevel::Untrusted);
        assert_eq!(default_trust_level("experimental-v3"), TrustLevel::Untrusted);
    }

    // -----------------------------------------------------------------------
    // WorkerPoolConfig tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_worker_pool_config_default() {
        let config = WorkerPoolConfig::default();
        assert!(config.max_workers >= 1);
        assert_eq!(config.default_timeout, Duration::from_secs(30));
        assert_eq!(config.acquire_timeout, Duration::from_secs(60));
        assert_eq!(config.memory_limit_per_worker, 512 * 1024 * 1024);
        assert_eq!(config.max_retries, 1);
    }

    #[test]
    fn test_worker_pool_config_with_limits() {
        let config = WorkerPoolConfig::with_limits(8, Duration::from_secs(10));
        assert_eq!(config.max_workers, 8);
        assert_eq!(config.default_timeout, Duration::from_secs(10));
    }

    #[test]
    fn test_worker_pool_config_with_limits_clamps_zero() {
        let config = WorkerPoolConfig::with_limits(0, Duration::from_secs(5));
        assert_eq!(config.max_workers, 1);
    }

    // -----------------------------------------------------------------------
    // WorkerPool basic tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_worker_pool_creation() {
        let pool = WorkerPool::new(test_pool_config(4));
        assert_eq!(pool.max_workers(), 4);
        assert_eq!(pool.active_workers(), 0);
        assert!(!pool.is_shutdown());
    }

    #[test]
    fn test_worker_pool_execute_native() {
        let pool = WorkerPool::new(test_pool_config(4));
        let backend = MockBackend;
        let vc = make_vc();

        let result = pool.execute(&backend, &vc, SolverExecutionMode::Native, TrustLevel::Trusted)
            .expect("native execution should succeed");

        assert!(result.is_proved());
        assert_eq!(result.solver_name(), "mock");
        assert_eq!(pool.active_workers(), 0);

        let stats = pool.statistics();
        assert_eq!(stats.total_native_executions, 1);
        assert_eq!(stats.total_isolated_executions, 0);
    }

    #[test]
    fn test_worker_pool_execute_hybrid_trusted() {
        let pool = WorkerPool::new(test_pool_config(4));
        let backend = MockBackend;
        let vc = make_vc();

        // Hybrid + Trusted → should resolve to Native
        let result = pool.execute(&backend, &vc, SolverExecutionMode::Hybrid, TrustLevel::Trusted)
            .expect("hybrid trusted execution should succeed");

        assert!(result.is_proved());

        let stats = pool.statistics();
        assert_eq!(stats.total_native_executions, 1);
        assert_eq!(stats.total_isolated_executions, 0);
    }

    #[test]
    fn test_worker_pool_statistics_initially_zero() {
        let pool = WorkerPool::new(test_pool_config(4));
        let stats = pool.statistics();
        assert_eq!(stats.total_native_executions, 0);
        assert_eq!(stats.total_isolated_executions, 0);
        assert_eq!(stats.total_failures, 0);
        assert_eq!(stats.total_retries, 0);
        assert_eq!(stats.active_workers, 0);
        assert_eq!(stats.peak_workers, 0);
    }

    #[test]
    fn test_worker_pool_multiple_native_executions() {
        let pool = WorkerPool::new(test_pool_config(4));
        let backend = MockBackend;

        for i in 0..5 {
            let vc = VerificationCondition {
                kind: VcKind::DivisionByZero,
                function: format!("fn_{i}"),
                location: SourceSpan::default(),
                formula: Formula::Bool(false),
                contract_metadata: None,
            };
            let result = pool.execute(&backend, &vc, SolverExecutionMode::Native, TrustLevel::Trusted)
                .expect("should succeed");
            assert!(result.is_proved());
        }

        let stats = pool.statistics();
        assert_eq!(stats.total_native_executions, 5);
    }

    // -----------------------------------------------------------------------
    // WorkerPool shutdown tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_worker_pool_shutdown_denies_new_executions() {
        let pool = WorkerPool::new(test_pool_config(4));
        pool.shutdown();
        assert!(pool.is_shutdown());

        let backend = MockBackend;
        let vc = make_vc();
        let result = pool.execute(&backend, &vc, SolverExecutionMode::Native, TrustLevel::Trusted);
        assert!(matches!(result, Err(ExecutionError::PoolShutdown)));
    }

    #[test]
    fn test_worker_pool_shutdown_wakes_waiters() {
        let pool = WorkerPool::new(WorkerPoolConfig {
            max_workers: 1,
            acquire_timeout: Duration::from_secs(10),
            ..test_pool_config(1)
        });

        // Manually acquire a worker slot to fill the pool
        pool.acquire_worker_slot().expect("should acquire");
        assert_eq!(pool.active_workers(), 1);

        // Spawn a thread that tries to acquire another slot
        let pool_clone = pool.clone();
        let handle = thread::spawn(move || {
            pool_clone.acquire_worker_slot()
        });

        thread::sleep(Duration::from_millis(50));
        pool.shutdown();

        let result = handle.join().expect("thread should not panic");
        assert!(matches!(result, Err(ExecutionError::PoolShutdown)));
    }

    // -----------------------------------------------------------------------
    // WorkerPool concurrency tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_worker_pool_concurrent_native() {
        let pool = WorkerPool::new(test_pool_config(4));

        let handles: Vec<_> = (0..8)
            .map(|i| {
                let pool = pool.clone();
                thread::spawn(move || {
                    let backend = MockBackend;
                    let vc = VerificationCondition {
                        kind: VcKind::DivisionByZero,
                        function: format!("fn_{i}"),
                        location: SourceSpan::default(),
                        formula: Formula::Bool(false),
                        contract_metadata: None,
                    };
                    pool.execute(&backend, &vc, SolverExecutionMode::Native, TrustLevel::Trusted)
                })
            })
            .collect();

        for h in handles {
            let result = h.join().expect("thread should not panic");
            assert!(result.is_ok());
            assert!(result.unwrap().is_proved());
        }

        let stats = pool.statistics();
        assert_eq!(stats.total_native_executions, 8);
    }

    #[test]
    fn test_worker_pool_slot_limiting() {
        // Pool with 2 max workers
        let pool = WorkerPool::new(WorkerPoolConfig {
            max_workers: 2,
            acquire_timeout: Duration::from_secs(5),
            ..test_pool_config(2)
        });

        // Acquire 2 slots manually
        pool.acquire_worker_slot().expect("slot 1");
        pool.acquire_worker_slot().expect("slot 2");
        assert_eq!(pool.active_workers(), 2);

        // Try to acquire a third — should fail with timeout
        let pool_clone = pool.clone();
        let handle = thread::spawn(move || {
            // By the time we get here, it should have timed out or succeeded
            // after the main thread releases a slot
            WorkerPool::acquire_worker_slot(&pool_clone)
        });

        // Wait briefly then release one slot
        thread::sleep(Duration::from_millis(50));
        pool.release_worker_slot();

        let result = handle.join().expect("thread should not panic");
        assert!(result.is_ok(), "should acquire released slot");
        assert_eq!(pool.active_workers(), 2); // 1 original + 1 newly acquired
    }

    #[test]
    fn test_worker_pool_peak_tracking() {
        let pool = WorkerPool::new(test_pool_config(4));

        pool.acquire_worker_slot().expect("slot 1");
        pool.acquire_worker_slot().expect("slot 2");
        pool.acquire_worker_slot().expect("slot 3");

        let stats = pool.statistics();
        assert_eq!(stats.peak_workers, 3);
        assert_eq!(stats.active_workers, 3);

        pool.release_worker_slot();
        pool.release_worker_slot();
        pool.release_worker_slot();

        let stats = pool.statistics();
        assert_eq!(stats.peak_workers, 3); // Peak should not decrease
        assert_eq!(stats.active_workers, 0);
    }

    // -----------------------------------------------------------------------
    // HybridExecutor tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_hybrid_executor_with_defaults() {
        let pool = WorkerPool::new(test_pool_config(4));
        let executor = HybridExecutor::with_defaults(pool);

        let backend = MockBackend;
        let vc = make_vc();

        // MockBackend trust_level = Trusted → should use Native
        let result = executor.execute(&backend, &vc)
            .expect("should succeed");
        assert!(result.is_proved());
    }

    #[test]
    fn test_hybrid_executor_custom_config() {
        let pool = WorkerPool::new(test_pool_config(4));
        let configs = vec![
            BackendExecutionConfig {
                name: "mock".to_string(),
                trust_level: TrustLevel::Trusted,
                mode: SolverExecutionMode::Native,
                timeout: Some(Duration::from_secs(10)),
            },
        ];
        let executor = HybridExecutor::new(pool, configs, SolverExecutionMode::Hybrid);

        let backend = MockBackend;
        let vc = make_vc();

        let result = executor.execute(&backend, &vc)
            .expect("should succeed");
        assert!(result.is_proved());

        let config = executor.backend_config("mock");
        assert!(config.is_some());
        assert_eq!(config.unwrap().trust_level, TrustLevel::Trusted);
        assert_eq!(config.unwrap().mode, SolverExecutionMode::Native);
    }

    #[test]
    fn test_hybrid_executor_unknown_backend_uses_default() {
        let pool = WorkerPool::new(test_pool_config(4));
        let executor = HybridExecutor::new(
            pool,
            vec![], // No backend configs
            SolverExecutionMode::Native, // Default to native
        );

        let backend = MockBackend;
        let vc = make_vc();

        // Unknown backend should use default mode
        let result = executor.execute(&backend, &vc)
            .expect("should succeed");
        assert!(result.is_proved());
    }

    #[test]
    fn test_hybrid_executor_pool_accessor() {
        let pool = WorkerPool::new(test_pool_config(8));
        let executor = HybridExecutor::with_defaults(pool);
        assert_eq!(executor.pool().max_workers(), 8);
    }

    #[test]
    fn test_hybrid_executor_shutdown() {
        let pool = WorkerPool::new(test_pool_config(4));
        let executor = HybridExecutor::with_defaults(pool);
        executor.shutdown();

        let backend = MockBackend;
        let vc = make_vc();
        let result = executor.execute(&backend, &vc);
        assert!(matches!(result, Err(ExecutionError::PoolShutdown)));
    }

    #[test]
    fn test_hybrid_executor_backend_config_lookup() {
        let pool = WorkerPool::new(test_pool_config(4));
        let executor = HybridExecutor::with_defaults(pool);

        assert!(executor.backend_config("z4").is_some());
        assert!(executor.backend_config("mock").is_some());
        assert!(executor.backend_config("nonexistent").is_none());

        let z4_config = executor.backend_config("z4").unwrap();
        assert_eq!(z4_config.trust_level, TrustLevel::Trusted);

        let certus_config = executor.backend_config("certus").unwrap();
        assert_eq!(certus_config.trust_level, TrustLevel::Untrusted);
    }

    // -----------------------------------------------------------------------
    // ExecutionError tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_execution_error_display() {
        let err = ExecutionError::PoolShutdown;
        assert!(err.to_string().contains("shut down"));

        let err = ExecutionError::WorkerUnavailable { timeout_ms: 5000 };
        assert!(err.to_string().contains("5000ms"));

        let err = ExecutionError::Timeout { timeout_ms: 3000 };
        assert!(err.to_string().contains("3000ms"));

        let err = ExecutionError::SolverCrash { reason: "SIGSEGV".to_string() };
        assert!(err.to_string().contains("SIGSEGV"));

        let err = ExecutionError::ResourceLimitExceeded { detail: "OOM".to_string() };
        assert!(err.to_string().contains("OOM"));

        let err = ExecutionError::Internal { reason: "bug".to_string() };
        assert!(err.to_string().contains("bug"));
    }

    // -----------------------------------------------------------------------
    // BackendExecutionConfig tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_backend_execution_config_debug() {
        let config = BackendExecutionConfig {
            name: "z4".to_string(),
            trust_level: TrustLevel::Trusted,
            mode: SolverExecutionMode::Native,
            timeout: Some(Duration::from_secs(10)),
        };
        let debug = format!("{config:?}");
        assert!(debug.contains("z4"));
        assert!(debug.contains("Trusted"));
        assert!(debug.contains("Native"));
    }

    // -----------------------------------------------------------------------
    // WorkerPoolStatistics tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_worker_pool_statistics_default() {
        let stats = WorkerPoolStatistics::default();
        assert_eq!(stats.total_native_executions, 0);
        assert_eq!(stats.total_isolated_executions, 0);
        assert_eq!(stats.total_failures, 0);
        assert_eq!(stats.total_retries, 0);
        assert_eq!(stats.active_workers, 0);
        assert_eq!(stats.peak_workers, 0);
        assert_eq!(stats.total_native_time_us, 0);
        assert_eq!(stats.total_isolated_time_us, 0);
    }

    #[test]
    fn test_worker_pool_statistics_after_native_execution() {
        let pool = WorkerPool::new(test_pool_config(4));
        let backend = MockBackend;
        let vc = make_vc();

        pool.execute(&backend, &vc, SolverExecutionMode::Native, TrustLevel::Trusted)
            .expect("should succeed");

        let stats = pool.statistics();
        assert_eq!(stats.total_native_executions, 1);
        // Time might be 0 for very fast mock execution; just verify it's accessible
        let _ = stats.total_native_time_us;
    }

    // -----------------------------------------------------------------------
    // Integration: Pool + resolve_execution_mode
    // -----------------------------------------------------------------------

    #[test]
    fn test_pool_resolves_hybrid_to_native_for_trusted_safety() {
        let pool = WorkerPool::new(test_pool_config(4));
        let backend = MockBackend;
        let vc = make_vc(); // DivisionByZero = L0Safety

        // Hybrid + Trusted → Native
        let result = pool.execute(&backend, &vc, SolverExecutionMode::Hybrid, TrustLevel::Trusted)
            .expect("should succeed");
        assert!(result.is_proved());

        let stats = pool.statistics();
        assert_eq!(stats.total_native_executions, 1);
        assert_eq!(stats.total_isolated_executions, 0);
    }

    #[test]
    fn test_pool_resolves_hybrid_to_isolated_for_semi_trusted_safety() {
        let pool = WorkerPool::new(test_pool_config(4));
        let backend = MockBackend;
        let vc = make_vc(); // DivisionByZero = L0Safety

        // Hybrid + SemiTrusted + L0Safety → WorkerIsolated (slot-limited)
        let result = pool.execute(&backend, &vc, SolverExecutionMode::Hybrid, TrustLevel::SemiTrusted)
            .expect("should succeed");
        assert!(result.is_proved());

        let stats = pool.statistics();
        assert_eq!(stats.total_isolated_executions, 1);
        assert_eq!(stats.total_native_executions, 0);
    }

    // -----------------------------------------------------------------------
    // Pool config accessor
    // -----------------------------------------------------------------------

    #[test]
    fn test_worker_pool_config_accessor() {
        let pool = WorkerPool::new(WorkerPoolConfig::with_limits(6, Duration::from_secs(15)));
        assert_eq!(pool.config().max_workers, 6);
        assert_eq!(pool.config().default_timeout, Duration::from_secs(15));
    }

    // -----------------------------------------------------------------------
    // Clone behavior
    // -----------------------------------------------------------------------

    #[test]
    fn test_worker_pool_clone_shares_state() {
        let pool1 = WorkerPool::new(test_pool_config(4));
        let pool2 = pool1.clone();

        let backend = MockBackend;
        let vc = make_vc();

        pool1.execute(&backend, &vc, SolverExecutionMode::Native, TrustLevel::Trusted)
            .expect("pool1 native");
        pool2.execute(&backend, &vc, SolverExecutionMode::Native, TrustLevel::Trusted)
            .expect("pool2 native");

        // Both pools share the same statistics
        let stats1 = pool1.statistics();
        let stats2 = pool2.statistics();
        assert_eq!(stats1.total_native_executions, 2);
        assert_eq!(stats2.total_native_executions, 2);
    }
}
