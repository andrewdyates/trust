// trust-router/governor.rs: Global verification resource governor
//
// tRust: Limits concurrent solver invocations, per-solver memory budgets,
// and total timeout budgets across all verification obligations. Integrates
// with Rust's jobserver protocol (CARGO_MAKEFLAGS) to respect the build
// system's concurrency limits.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering};
use std::sync::{Arc, Condvar, Mutex};
use std::time::{Duration, Instant};

use thiserror::Error;

/// Errors from the resource governor.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum GovernorError {
    #[error("timeout budget exhausted: {elapsed_ms}ms of {budget_ms}ms used")]
    TimeoutBudgetExhausted { elapsed_ms: u64, budget_ms: u64 },

    #[error("memory limit exceeded: {requested_bytes} bytes requested, {limit_bytes} bytes limit")]
    MemoryLimitExceeded { requested_bytes: u64, limit_bytes: u64 },

    #[error("governor is shut down")]
    Shutdown,

    #[error("slot acquisition timed out after {wait_ms}ms")]
    AcquireTimeout { wait_ms: u64 },
}

/// tRust: Configuration for the resource governor.
///
/// Governs max concurrent solvers, per-solver memory limits, and
/// total timeout budget across all obligations.
#[derive(Debug, Clone)]
pub struct GovernorConfig {
    /// Maximum number of concurrent solver invocations.
    pub max_concurrent_solvers: usize,
    /// Maximum memory (bytes) each solver may use. 0 = unlimited.
    pub max_memory_per_solver: u64,
    /// Total timeout budget across all obligations. `Duration::ZERO` = unlimited.
    pub total_timeout_budget: Duration,
    /// Maximum time to wait when acquiring a slot. `None` = block indefinitely.
    pub acquire_timeout: Option<Duration>,
}

impl Default for GovernorConfig {
    fn default() -> Self {
        Self {
            max_concurrent_solvers: num_cpus_heuristic(),
            max_memory_per_solver: 512 * 1024 * 1024, // 512 MiB
            total_timeout_budget: Duration::from_secs(300), // 5 minutes
            acquire_timeout: None,
        }
    }
}

impl GovernorConfig {
    /// Create a config that respects the jobserver protocol.
    ///
    /// Reads `CARGO_MAKEFLAGS` to detect the number of parallel jobs
    /// Cargo has allocated. Falls back to `default()` if not in a
    /// Cargo build or if parsing fails.
    #[must_use]
    pub fn from_jobserver() -> Self {
        let slots = detect_jobserver_slots().unwrap_or_else(num_cpus_heuristic);
        Self {
            max_concurrent_solvers: slots,
            ..Self::default()
        }
    }
}

/// tRust: RAII guard that releases a solver slot on drop.
///
/// Returned by `ResourceGovernor::acquire_slot()`. Tracks per-solver
/// memory usage. The slot is returned to the governor when this guard
/// is dropped (or when `release()` is called explicitly).
pub struct GovernorSlot {
    governor: Arc<GovernorInner>,
    memory_used: AtomicU64,
    released: AtomicBool,
}

impl std::fmt::Debug for GovernorSlot {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("GovernorSlot")
            .field("memory_used", &self.memory_used.load(Ordering::Relaxed))
            .field("released", &self.released.load(Ordering::Relaxed))
            .finish()
    }
}

impl GovernorSlot {
    /// Report memory usage for this solver invocation.
    ///
    /// Returns `Err` if the reported usage exceeds the per-solver limit.
    pub fn report_memory(&self, bytes: u64) -> Result<(), GovernorError> {
        let limit = self.governor.config.max_memory_per_solver;
        if limit > 0 && bytes > limit {
            return Err(GovernorError::MemoryLimitExceeded {
                requested_bytes: bytes,
                limit_bytes: limit,
            });
        }
        self.memory_used.store(bytes, Ordering::Relaxed);
        self.governor.total_memory.fetch_add(
            bytes.saturating_sub(self.memory_used.load(Ordering::Relaxed)),
            Ordering::Relaxed,
        );
        Ok(())
    }

    /// Remaining time in the global timeout budget.
    ///
    /// Returns `None` if the timeout budget is unlimited.
    #[must_use]
    pub fn remaining_budget(&self) -> Option<Duration> {
        self.governor.remaining_budget()
    }

    /// Check whether the global timeout budget has been exhausted.
    #[must_use]
    pub fn budget_exhausted(&self) -> bool {
        self.governor.budget_exhausted()
    }

    /// Explicitly release this slot (also happens on drop).
    pub fn release(self) {
        // Drop triggers the release logic.
        drop(self);
    }
}

impl Drop for GovernorSlot {
    fn drop(&mut self) {
        if !self.released.swap(true, Ordering::SeqCst) {
            let mem = self.memory_used.load(Ordering::Relaxed);
            self.governor.total_memory.fetch_sub(mem, Ordering::Relaxed);

            let mut active = self.governor.active_slots.lock()
                .unwrap_or_else(|e| e.into_inner());
            *active = active.saturating_sub(1);
            self.governor.slot_available.notify_one();
        }
    }
}

/// tRust: Global resource governor for verification solver invocations.
///
/// Thread-safe. Shared via `Arc`. Use `acquire_slot()` to obtain a
/// `GovernorSlot` RAII guard before launching a solver. The guard
/// releases the slot automatically on drop.
#[derive(Clone)]
pub struct ResourceGovernor {
    inner: Arc<GovernorInner>,
}

struct GovernorInner {
    config: GovernorConfig,
    active_slots: Mutex<usize>,
    slot_available: Condvar,
    total_memory: AtomicU64,
    start_time: Instant,
    shutdown: AtomicBool,
    completed_count: AtomicUsize,
}

impl ResourceGovernor {
    /// Create a new governor with the given configuration.
    #[must_use]
    pub fn new(config: GovernorConfig) -> Self {
        Self {
            inner: Arc::new(GovernorInner {
                config,
                active_slots: Mutex::new(0),
                slot_available: Condvar::new(),
                total_memory: AtomicU64::new(0),
                start_time: Instant::now(),
                shutdown: AtomicBool::new(false),
                completed_count: AtomicUsize::new(0),
            }),
        }
    }

    /// Create a governor using jobserver-aware defaults.
    #[must_use]
    pub fn from_jobserver() -> Self {
        Self::new(GovernorConfig::from_jobserver())
    }

    /// Acquire a solver slot, blocking until one is available.
    ///
    /// Returns `GovernorError::TimeoutBudgetExhausted` if the global
    /// timeout budget is exhausted, `GovernorError::Shutdown` if the
    /// governor has been shut down, or `GovernorError::AcquireTimeout`
    /// if the per-acquire timeout expires.
    pub fn acquire_slot(&self) -> Result<GovernorSlot, GovernorError> {
        let inner = &self.inner;

        // Check preconditions before waiting.
        if inner.shutdown.load(Ordering::SeqCst) {
            return Err(GovernorError::Shutdown);
        }
        if inner.budget_exhausted() {
            return Err(self.budget_exhausted_error());
        }

        let mut active = inner.active_slots.lock()
            .unwrap_or_else(|e| e.into_inner());

        let deadline = inner.config.acquire_timeout.map(|d| Instant::now() + d);

        while *active >= inner.config.max_concurrent_solvers {
            if inner.shutdown.load(Ordering::SeqCst) {
                return Err(GovernorError::Shutdown);
            }
            if inner.budget_exhausted() {
                return Err(self.budget_exhausted_error());
            }

            if let Some(deadline) = deadline {
                let remaining = deadline.saturating_duration_since(Instant::now());
                if remaining.is_zero() {
                    return Err(GovernorError::AcquireTimeout {
                        wait_ms: inner.config.acquire_timeout
                            .map_or(0, |d| d.as_millis() as u64),
                    });
                }
                let result = inner.slot_available.wait_timeout(active, remaining)
                    .unwrap_or_else(|e| e.into_inner());
                active = result.0;
                if result.1.timed_out() {
                    // Re-check: slot may have become available exactly at timeout.
                    if *active >= inner.config.max_concurrent_solvers {
                        return Err(GovernorError::AcquireTimeout {
                            wait_ms: inner.config.acquire_timeout
                                .map_or(0, |d| d.as_millis() as u64),
                        });
                    }
                }
            } else {
                active = inner.slot_available.wait(active)
                    .unwrap_or_else(|e| e.into_inner());
            }
        }

        *active += 1;

        Ok(GovernorSlot {
            governor: Arc::clone(inner),
            memory_used: AtomicU64::new(0),
            released: AtomicBool::new(false),
        })
    }

    /// Record that a solver invocation completed (for metrics).
    pub fn record_completion(&self) {
        self.inner.completed_count.fetch_add(1, Ordering::Relaxed);
    }

    /// Shut down the governor, waking all waiters.
    pub fn shutdown(&self) {
        self.inner.shutdown.store(true, Ordering::SeqCst);
        self.inner.slot_available.notify_all();
    }

    /// Number of currently active solver slots.
    #[must_use]
    pub fn active_slots(&self) -> usize {
        *self.inner.active_slots.lock()
            .unwrap_or_else(|e| e.into_inner())
    }

    /// Maximum concurrent solvers configured.
    #[must_use]
    pub fn max_concurrent(&self) -> usize {
        self.inner.config.max_concurrent_solvers
    }

    /// Total completed solver invocations.
    #[must_use]
    pub fn completed_count(&self) -> usize {
        self.inner.completed_count.load(Ordering::Relaxed)
    }

    /// Total memory currently tracked across all active solvers.
    #[must_use]
    pub fn total_memory_bytes(&self) -> u64 {
        self.inner.total_memory.load(Ordering::Relaxed)
    }

    /// Remaining time in the global timeout budget.
    ///
    /// Returns `None` if the budget is unlimited (`Duration::ZERO`).
    #[must_use]
    pub fn remaining_budget(&self) -> Option<Duration> {
        self.inner.remaining_budget()
    }

    /// Whether the global timeout budget has been exhausted.
    #[must_use]
    pub fn budget_exhausted(&self) -> bool {
        self.inner.budget_exhausted()
    }

    /// Access the underlying configuration.
    #[must_use]
    pub fn config(&self) -> &GovernorConfig {
        &self.inner.config
    }

    fn budget_exhausted_error(&self) -> GovernorError {
        let elapsed = self.inner.start_time.elapsed();
        GovernorError::TimeoutBudgetExhausted {
            elapsed_ms: elapsed.as_millis() as u64,
            budget_ms: self.inner.config.total_timeout_budget.as_millis() as u64,
        }
    }
}

impl GovernorInner {
    fn remaining_budget(&self) -> Option<Duration> {
        let budget = self.config.total_timeout_budget;
        if budget.is_zero() {
            return None; // unlimited
        }
        let elapsed = self.start_time.elapsed();
        Some(budget.saturating_sub(elapsed))
    }

    fn budget_exhausted(&self) -> bool {
        let budget = self.config.total_timeout_budget;
        if budget.is_zero() {
            return false; // unlimited
        }
        self.start_time.elapsed() >= budget
    }
}

// ---------------------------------------------------------------------------
// Jobserver integration
// ---------------------------------------------------------------------------

/// tRust: Detect the number of jobserver slots from `CARGO_MAKEFLAGS`.
///
/// Cargo sets `CARGO_MAKEFLAGS` with the `-j<N>` or `--jobserver-auth=<R>,<W>`
/// form. We parse the `-j<N>` flag to determine how many concurrent jobs
/// Cargo allocated. Returns `None` if the variable is absent or unparseable.
pub(crate) fn detect_jobserver_slots() -> Option<usize> {
    let flags = std::env::var("CARGO_MAKEFLAGS").ok()?;
    // Try `-jN` form first (common on macOS/Linux).
    for token in flags.split_whitespace() {
        if let Some(n_str) = token.strip_prefix("-j")
            && let Ok(n) = n_str.parse::<usize>()
                && n > 0 {
                    return Some(n);
                }
    }
    // Try `--jobserver-auth=R,W` form (pipe-based, count is implicit).
    // With pipe-based jobserver the slot count equals available tokens.
    // We cannot read the pipe without consuming tokens, so fall back.
    None
}

/// Heuristic for default concurrency: available parallelism or 4.
fn num_cpus_heuristic() -> usize {
    std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(4)
}

#[cfg(test)]
mod tests {
    use std::thread;

    use super::*;

    #[test]
    fn test_governor_config_default_has_sane_values() {
        let config = GovernorConfig::default();
        assert!(config.max_concurrent_solvers >= 1);
        assert_eq!(config.max_memory_per_solver, 512 * 1024 * 1024);
        assert_eq!(config.total_timeout_budget, Duration::from_secs(300));
        assert!(config.acquire_timeout.is_none());
    }

    #[test]
    fn test_governor_acquire_and_release_single_slot() {
        let gov = ResourceGovernor::new(GovernorConfig {
            max_concurrent_solvers: 2,
            total_timeout_budget: Duration::ZERO, // unlimited
            ..GovernorConfig::default()
        });

        assert_eq!(gov.active_slots(), 0);

        let slot = gov.acquire_slot().expect("should acquire slot");
        assert_eq!(gov.active_slots(), 1);

        drop(slot);
        assert_eq!(gov.active_slots(), 0);
    }

    #[test]
    fn test_governor_acquire_max_slots() {
        let gov = ResourceGovernor::new(GovernorConfig {
            max_concurrent_solvers: 3,
            total_timeout_budget: Duration::ZERO,
            ..GovernorConfig::default()
        });

        let s1 = gov.acquire_slot().expect("slot 1");
        let s2 = gov.acquire_slot().expect("slot 2");
        let s3 = gov.acquire_slot().expect("slot 3");
        assert_eq!(gov.active_slots(), 3);

        drop(s1);
        assert_eq!(gov.active_slots(), 2);
        drop(s2);
        drop(s3);
        assert_eq!(gov.active_slots(), 0);
    }

    #[test]
    fn test_governor_concurrent_slot_acquisition() {
        let gov = ResourceGovernor::new(GovernorConfig {
            max_concurrent_solvers: 2,
            total_timeout_budget: Duration::ZERO,
            acquire_timeout: Some(Duration::from_secs(5)),
            ..GovernorConfig::default()
        });

        // Fill both slots.
        let s1 = gov.acquire_slot().expect("slot 1");
        let s2 = gov.acquire_slot().expect("slot 2");
        assert_eq!(gov.active_slots(), 2);

        // Spawn a thread that tries to acquire a third slot.
        let gov_clone = gov.clone();
        let handle = thread::spawn(move || {
            gov_clone.acquire_slot()
        });

        // Brief sleep to let the thread block on the condvar.
        thread::sleep(Duration::from_millis(50));
        assert_eq!(gov.active_slots(), 2);

        // Release one slot — the waiting thread should unblock.
        drop(s1);

        let result = handle.join().expect("thread should not panic");
        assert!(result.is_ok(), "blocked thread should acquire released slot");
        assert_eq!(gov.active_slots(), 2);

        drop(s2);
        drop(result.unwrap());
        assert_eq!(gov.active_slots(), 0);
    }

    #[test]
    fn test_governor_slot_release_is_idempotent() {
        let gov = ResourceGovernor::new(GovernorConfig {
            max_concurrent_solvers: 1,
            total_timeout_budget: Duration::ZERO,
            ..GovernorConfig::default()
        });

        let slot = gov.acquire_slot().expect("slot");
        assert_eq!(gov.active_slots(), 1);
        drop(slot);
        assert_eq!(gov.active_slots(), 0);
        // Acquiring again should succeed (slot was properly released).
        let _slot2 = gov.acquire_slot().expect("should re-acquire");
        assert_eq!(gov.active_slots(), 1);
    }

    #[test]
    fn test_governor_timeout_budget_exhaustion() {
        let gov = ResourceGovernor::new(GovernorConfig {
            max_concurrent_solvers: 4,
            total_timeout_budget: Duration::from_millis(50),
            ..GovernorConfig::default()
        });

        // Budget should not be exhausted immediately.
        assert!(!gov.budget_exhausted());

        // Wait for the budget to expire.
        thread::sleep(Duration::from_millis(60));

        assert!(gov.budget_exhausted());

        let result = gov.acquire_slot();
        assert!(result.is_err());
        assert!(
            matches!(result.unwrap_err(), GovernorError::TimeoutBudgetExhausted { .. }),
            "should get TimeoutBudgetExhausted"
        );
    }

    #[test]
    fn test_governor_unlimited_timeout_budget() {
        let gov = ResourceGovernor::new(GovernorConfig {
            max_concurrent_solvers: 2,
            total_timeout_budget: Duration::ZERO, // unlimited
            ..GovernorConfig::default()
        });

        assert!(!gov.budget_exhausted());
        assert!(gov.remaining_budget().is_none());
    }

    #[test]
    fn test_governor_remaining_budget_decreases() {
        let gov = ResourceGovernor::new(GovernorConfig {
            max_concurrent_solvers: 2,
            total_timeout_budget: Duration::from_secs(10),
            ..GovernorConfig::default()
        });

        let budget_1 = gov.remaining_budget().expect("should have budget");
        thread::sleep(Duration::from_millis(20));
        let budget_2 = gov.remaining_budget().expect("should have budget");
        assert!(budget_2 < budget_1, "budget should decrease over time");
    }

    #[test]
    fn test_governor_memory_limit_exceeded() {
        let gov = ResourceGovernor::new(GovernorConfig {
            max_concurrent_solvers: 2,
            max_memory_per_solver: 1024, // 1 KiB
            total_timeout_budget: Duration::ZERO,
            ..GovernorConfig::default()
        });

        let slot = gov.acquire_slot().expect("slot");
        let result = slot.report_memory(2048);
        assert!(result.is_err());
        assert!(
            matches!(result.unwrap_err(), GovernorError::MemoryLimitExceeded { .. }),
            "should get MemoryLimitExceeded"
        );
    }

    #[test]
    fn test_governor_memory_within_limit() {
        let gov = ResourceGovernor::new(GovernorConfig {
            max_concurrent_solvers: 2,
            max_memory_per_solver: 1024,
            total_timeout_budget: Duration::ZERO,
            ..GovernorConfig::default()
        });

        let slot = gov.acquire_slot().expect("slot");
        let result = slot.report_memory(512);
        assert!(result.is_ok());
    }

    #[test]
    fn test_governor_memory_unlimited() {
        let gov = ResourceGovernor::new(GovernorConfig {
            max_concurrent_solvers: 2,
            max_memory_per_solver: 0, // unlimited
            total_timeout_budget: Duration::ZERO,
            ..GovernorConfig::default()
        });

        let slot = gov.acquire_slot().expect("slot");
        // Even a huge amount should be fine with unlimited.
        let result = slot.report_memory(u64::MAX);
        assert!(result.is_ok());
    }

    #[test]
    fn test_governor_shutdown_wakes_waiters() {
        let gov = ResourceGovernor::new(GovernorConfig {
            max_concurrent_solvers: 1,
            total_timeout_budget: Duration::ZERO,
            ..GovernorConfig::default()
        });

        let _slot = gov.acquire_slot().expect("slot 1");

        let gov_clone = gov.clone();
        let handle = thread::spawn(move || {
            gov_clone.acquire_slot()
        });

        thread::sleep(Duration::from_millis(50));
        gov.shutdown();

        let result = handle.join().expect("thread should not panic");
        assert!(result.is_err());
        assert!(
            matches!(result.unwrap_err(), GovernorError::Shutdown),
            "should get Shutdown error"
        );
    }

    #[test]
    fn test_governor_acquire_timeout() {
        let gov = ResourceGovernor::new(GovernorConfig {
            max_concurrent_solvers: 1,
            total_timeout_budget: Duration::ZERO,
            acquire_timeout: Some(Duration::from_millis(50)),
            ..GovernorConfig::default()
        });

        let _slot = gov.acquire_slot().expect("slot 1");

        let start = Instant::now();
        let result = gov.acquire_slot();
        let elapsed = start.elapsed();

        assert!(result.is_err());
        assert!(
            matches!(result.unwrap_err(), GovernorError::AcquireTimeout { .. }),
            "should get AcquireTimeout"
        );
        // Should have waited approximately the timeout duration.
        assert!(elapsed >= Duration::from_millis(40));
        assert!(elapsed < Duration::from_secs(2));
    }

    #[test]
    fn test_governor_completed_count() {
        let gov = ResourceGovernor::new(GovernorConfig {
            max_concurrent_solvers: 2,
            total_timeout_budget: Duration::ZERO,
            ..GovernorConfig::default()
        });

        assert_eq!(gov.completed_count(), 0);
        gov.record_completion();
        gov.record_completion();
        assert_eq!(gov.completed_count(), 2);
    }

    #[test]
    fn test_governor_slot_remaining_budget() {
        let gov = ResourceGovernor::new(GovernorConfig {
            max_concurrent_solvers: 2,
            total_timeout_budget: Duration::from_secs(60),
            ..GovernorConfig::default()
        });

        let slot = gov.acquire_slot().expect("slot");
        let remaining = slot.remaining_budget();
        assert!(remaining.is_some());
        assert!(remaining.unwrap() <= Duration::from_secs(60));
        assert!(remaining.unwrap() > Duration::from_secs(50));
    }

    #[test]
    fn test_governor_slot_budget_exhausted_check() {
        let gov = ResourceGovernor::new(GovernorConfig {
            max_concurrent_solvers: 2,
            total_timeout_budget: Duration::from_millis(30),
            ..GovernorConfig::default()
        });

        let slot = gov.acquire_slot().expect("slot");
        assert!(!slot.budget_exhausted());

        thread::sleep(Duration::from_millis(40));
        assert!(slot.budget_exhausted());
    }

    #[test]
    fn test_governor_config_from_jobserver_fallback() {
        // Without CARGO_MAKEFLAGS set, should fall back to CPU heuristic.
        // We cannot guarantee the env var is absent in all test environments,
        // but the function should not panic regardless.
        let config = GovernorConfig::from_jobserver();
        assert!(config.max_concurrent_solvers >= 1);
    }

    #[test]
    fn test_detect_jobserver_slots_parses_j_flag() {
        // Temporarily set CARGO_MAKEFLAGS for this test.
        // Note: this test is inherently not thread-safe with other tests
        // that read the same env var, but std test runner serializes by default.
        let original = std::env::var("CARGO_MAKEFLAGS").ok();

        // SAFETY: Single-threaded test context; no concurrent env var readers
        // in this test. We restore the original value at the end.
        unsafe {
            std::env::set_var("CARGO_MAKEFLAGS", "-j8 --jobserver-auth=3,4");
        }
        assert_eq!(detect_jobserver_slots(), Some(8));

        unsafe {
            std::env::set_var("CARGO_MAKEFLAGS", "--jobserver-auth=3,4");
        }
        assert_eq!(detect_jobserver_slots(), None);

        unsafe {
            std::env::set_var("CARGO_MAKEFLAGS", "-j1");
        }
        assert_eq!(detect_jobserver_slots(), Some(1));

        // Restore original value.
        match original {
            Some(val) => unsafe { std::env::set_var("CARGO_MAKEFLAGS", val) },
            None => unsafe { std::env::remove_var("CARGO_MAKEFLAGS") },
        }
    }

    #[test]
    fn test_governor_max_concurrent_accessor() {
        let gov = ResourceGovernor::new(GovernorConfig {
            max_concurrent_solvers: 7,
            total_timeout_budget: Duration::ZERO,
            ..GovernorConfig::default()
        });
        assert_eq!(gov.max_concurrent(), 7);
    }

    #[test]
    fn test_governor_config_accessor() {
        let gov = ResourceGovernor::new(GovernorConfig {
            max_concurrent_solvers: 3,
            max_memory_per_solver: 1024,
            total_timeout_budget: Duration::from_secs(60),
            acquire_timeout: Some(Duration::from_secs(5)),
        });
        let config = gov.config();
        assert_eq!(config.max_concurrent_solvers, 3);
        assert_eq!(config.max_memory_per_solver, 1024);
        assert_eq!(config.total_timeout_budget, Duration::from_secs(60));
        assert_eq!(config.acquire_timeout, Some(Duration::from_secs(5)));
    }

    #[test]
    fn test_governor_multi_thread_stress() {
        let gov = ResourceGovernor::new(GovernorConfig {
            max_concurrent_solvers: 3,
            total_timeout_budget: Duration::ZERO,
            ..GovernorConfig::default()
        });

        let handles: Vec<_> = (0..10)
            .map(|_| {
                let gov = gov.clone();
                thread::spawn(move || {
                    let slot = gov.acquire_slot().expect("should acquire");
                    assert!(gov.active_slots() <= 3);
                    thread::sleep(Duration::from_millis(5));
                    gov.record_completion();
                    drop(slot);
                })
            })
            .collect();

        for h in handles {
            h.join().expect("thread should not panic");
        }

        assert_eq!(gov.active_slots(), 0);
        assert_eq!(gov.completed_count(), 10);
    }
}
