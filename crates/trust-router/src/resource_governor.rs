// trust-router/resource_governor.rs: Global verification resource governor with
// jobserver integration, priority-based allocation, and backpressure
//
// tRust #196: Extends the base governor with typed ResourceRequest/ResourceGrant,
// priority-aware slot allocation (P1 verifications get reserved slots),
// backpressure signaling, utilization statistics, and portfolio racer integration.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering};
use std::sync::{Arc, Condvar, Mutex};
use std::time::{Duration, Instant};

use trust_types::ProofLevel;

use crate::governor::{self, GovernorConfig, GovernorError};

// ---------------------------------------------------------------------------
// Verification priority
// ---------------------------------------------------------------------------

/// tRust #196: Priority level for verification resource requests.
///
/// Higher-priority requests get reserved solver slots and are served before
/// lower-priority requests when resources are contended. The priority maps
/// to the verification proof level: safety checks (L0) are highest priority
/// because they catch UB; functional checks (L1) are normal; domain checks
/// (L2) are lower priority.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum VerificationPriority {
    /// Critical safety checks (overflow, division by zero, bounds).
    /// Gets reserved slots that lower priorities cannot consume.
    Critical,
    /// Normal functional verification (pre/postconditions).
    Normal,
    /// Low-priority domain/temporal verification.
    Low,
    /// Background verification tasks (re-checks, speculative).
    Background,
}

impl VerificationPriority {
    /// Convert from `ProofLevel` to resource priority.
    #[must_use]
    pub fn from_proof_level(level: ProofLevel) -> Self {
        match level {
            ProofLevel::L0Safety => Self::Critical,
            ProofLevel::L1Functional => Self::Normal,
            ProofLevel::L2Domain => Self::Low,
            _ => Self::Normal,
        }
    }
}

// ---------------------------------------------------------------------------
// Resource request / grant
// ---------------------------------------------------------------------------

/// tRust #196: A typed request for verification resources.
///
/// Callers create a `ResourceRequest` describing what they need, then
/// submit it to the governor. The governor returns a `ResourceGrant` if
/// resources are available, or applies backpressure.
#[derive(Debug, Clone)]
pub struct ResourceRequest {
    /// Identifier for the requesting verification task.
    pub task_id: String,
    /// Number of solver slots requested (typically 1 for single dispatch,
    /// N for portfolio racing).
    pub solver_slots: usize,
    /// Memory budget requested (bytes). 0 = use governor default.
    pub memory_bytes: u64,
    /// Priority of this request.
    pub priority: VerificationPriority,
    /// Maximum time the caller is willing to wait for resources.
    /// `None` = use governor default; `Some(Duration::ZERO)` = try-acquire.
    pub wait_timeout: Option<Duration>,
}

impl ResourceRequest {
    /// Create a single-slot request at the given priority.
    #[must_use]
    pub fn single(task_id: impl Into<String>, priority: VerificationPriority) -> Self {
        Self {
            task_id: task_id.into(),
            solver_slots: 1,
            memory_bytes: 0,
            priority,
            wait_timeout: None,
        }
    }

    /// Create a multi-slot request for portfolio racing.
    #[must_use]
    pub fn portfolio(
        task_id: impl Into<String>,
        slots: usize,
        priority: VerificationPriority,
    ) -> Self {
        Self {
            task_id: task_id.into(),
            solver_slots: slots.max(1),
            memory_bytes: 0,
            priority,
            wait_timeout: None,
        }
    }

    /// Set the memory budget for this request.
    #[must_use]
    pub fn with_memory(mut self, bytes: u64) -> Self {
        self.memory_bytes = bytes;
        self
    }

    /// Set the wait timeout for this request.
    #[must_use]
    pub fn with_timeout(mut self, timeout: Duration) -> Self {
        self.wait_timeout = Some(timeout);
        self
    }
}

/// tRust #196: A grant of verification resources from the governor.
///
/// RAII guard: releases all granted slots on drop. Tracks the grant's
/// priority, slot count, and timing for statistics.
pub struct ResourceGrant {
    inner: Arc<GovernorState>,
    /// Number of slots granted.
    pub slots_granted: usize,
    /// Memory budget for this grant (bytes).
    pub memory_budget: u64,
    /// Priority of the original request.
    pub priority: VerificationPriority,
    /// Wall-clock time spent waiting for this grant.
    pub wait_time: Duration,
    /// Task ID from the original request.
    pub task_id: String,
    released: AtomicBool,
}

impl std::fmt::Debug for ResourceGrant {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ResourceGrant")
            .field("task_id", &self.task_id)
            .field("slots_granted", &self.slots_granted)
            .field("memory_budget", &self.memory_budget)
            .field("priority", &self.priority)
            .field("wait_time", &self.wait_time)
            .finish()
    }
}

impl ResourceGrant {
    /// Check whether the global timeout budget has been exhausted.
    #[must_use]
    pub fn budget_exhausted(&self) -> bool {
        self.inner.base_governor.budget_exhausted()
    }

    /// Remaining time in the global timeout budget.
    #[must_use]
    pub fn remaining_budget(&self) -> Option<Duration> {
        self.inner.base_governor.remaining_budget()
    }
}

impl Drop for ResourceGrant {
    fn drop(&mut self) {
        if !self.released.swap(true, Ordering::SeqCst) {
            let mut state = self.inner.slot_state.lock()
                .unwrap_or_else(|e| e.into_inner());

            // Return slots based on priority tier.
            match self.priority {
                VerificationPriority::Critical => {
                    state.critical_active = state.critical_active.saturating_sub(self.slots_granted);
                }
                _ => {
                    state.normal_active = state.normal_active.saturating_sub(self.slots_granted);
                }
            }

            self.inner.base_governor.record_completion();
            self.inner.slot_available.notify_all();
        }
    }
}

// ---------------------------------------------------------------------------
// Backpressure
// ---------------------------------------------------------------------------

/// tRust #196: Backpressure signal from the governor.
///
/// When resources are heavily contended, the governor returns a signal
/// indicating the current pressure level. Callers can use this to
/// reduce request rate, simplify verification strategies, or defer
/// low-priority work.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BackpressureSignal {
    /// No pressure. Resources are available.
    None,
    /// Moderate pressure. Consider reducing solver count for portfolio races.
    /// Contains the recommended max concurrent solvers to use.
    Moderate { recommended_solvers: usize },
    /// High pressure. Defer non-critical work. Only Critical priority should proceed.
    High,
    /// Overloaded. All new requests should back off.
    Overloaded,
}

impl BackpressureSignal {
    /// Whether the caller should reduce its resource consumption.
    #[must_use]
    pub fn should_reduce(&self) -> bool {
        !matches!(self, Self::None)
    }

    /// Whether the caller should defer non-critical work entirely.
    #[must_use]
    pub fn should_defer_non_critical(&self) -> bool {
        matches!(self, Self::High | Self::Overloaded)
    }
}

// ---------------------------------------------------------------------------
// Statistics
// ---------------------------------------------------------------------------

/// tRust #196: Cumulative statistics from the resource governor.
///
/// Tracks utilization, wait times, grant/denial counts, and per-priority
/// breakdowns. All values are monotonically increasing counters (except
/// current utilization which is a snapshot).
#[derive(Debug, Clone, Default)]
pub struct GovernorStatistics {
    /// Total grant requests made.
    pub total_requests: u64,
    /// Total grants issued.
    pub total_grants: u64,
    /// Total denials (timeout, budget exhausted, backpressure).
    pub total_denials: u64,
    /// Total wait time across all granted requests (microseconds).
    pub total_wait_time_us: u64,
    /// Maximum wait time observed for any single grant (microseconds).
    pub max_wait_time_us: u64,
    /// Current utilization: active_slots / max_slots (0.0 - 1.0).
    pub current_utilization: f64,
    /// Current active slots.
    pub current_active_slots: usize,
    /// Peak concurrent slots observed.
    pub peak_active_slots: usize,
    /// Grants by priority level: [Critical, Normal, Low, Background].
    pub grants_by_priority: [u64; 4],
    /// Denials by priority level: [Critical, Normal, Low, Background].
    pub denials_by_priority: [u64; 4],
}

// ---------------------------------------------------------------------------
// Slot state (internal)
// ---------------------------------------------------------------------------

/// Internal slot tracking state, protected by Mutex.
struct SlotState {
    /// Slots used by Critical-priority tasks.
    critical_active: usize,
    /// Slots used by Normal/Low/Background tasks.
    normal_active: usize,
}

impl SlotState {
    fn total_active(&self) -> usize {
        self.critical_active + self.normal_active
    }
}

// ---------------------------------------------------------------------------
// Governor state (shared)
// ---------------------------------------------------------------------------

struct GovernorState {
    base_governor: governor::ResourceGovernor,
    slot_state: Mutex<SlotState>,
    slot_available: Condvar,
    /// Fraction of slots reserved for Critical priority (0.0 - 1.0).
    reserved_critical_fraction: f64,
    shutdown: AtomicBool,

    // Statistics counters (atomics for lock-free updates).
    stat_total_requests: AtomicU64,
    stat_total_grants: AtomicU64,
    stat_total_denials: AtomicU64,
    stat_total_wait_us: AtomicU64,
    stat_max_wait_us: AtomicU64,
    stat_peak_active: AtomicUsize,
    stat_grants_critical: AtomicU64,
    stat_grants_normal: AtomicU64,
    stat_grants_low: AtomicU64,
    stat_grants_background: AtomicU64,
    stat_denials_critical: AtomicU64,
    stat_denials_normal: AtomicU64,
    stat_denials_low: AtomicU64,
    stat_denials_background: AtomicU64,
}

// ---------------------------------------------------------------------------
// PriorityResourceGovernor
// ---------------------------------------------------------------------------

/// tRust #196: Priority-aware resource governor with backpressure and statistics.
///
/// Wraps the base `ResourceGovernor` with typed request/grant semantics,
/// priority-based slot reservation, backpressure signaling, and utilization
/// statistics. Thread-safe; shared via `Arc` internally (clone is cheap).
///
/// # Slot Reservation
///
/// A configurable fraction of total slots is reserved for `Critical` priority
/// requests. Non-critical requests cannot consume reserved slots, ensuring
/// safety checks always have available capacity.
///
/// # Usage
///
/// ```ignore
/// let gov = PriorityResourceGovernor::new(config);
/// let request = ResourceRequest::single("vc_42", VerificationPriority::Critical);
/// let grant = gov.request_resources(request)?;
/// // ... run solver ...
/// drop(grant); // releases slots
/// ```
#[derive(Clone)]
pub struct PriorityResourceGovernor {
    inner: Arc<GovernorState>,
}

/// tRust #196: Configuration for the priority resource governor.
#[derive(Debug, Clone)]
pub struct PriorityGovernorConfig {
    /// Base governor configuration (concurrency, memory, timeouts).
    pub base: GovernorConfig,
    /// Fraction of total solver slots reserved for Critical priority (0.0 - 1.0).
    /// Default: 0.25 (25% of slots reserved for safety checks).
    pub reserved_critical_fraction: f64,
}

impl Default for PriorityGovernorConfig {
    fn default() -> Self {
        Self {
            base: GovernorConfig::default(),
            reserved_critical_fraction: 0.25,
        }
    }
}

impl PriorityGovernorConfig {
    /// Create a config that respects the jobserver protocol.
    #[must_use]
    pub fn from_jobserver() -> Self {
        Self {
            base: GovernorConfig::from_jobserver(),
            ..Self::default()
        }
    }
}

impl PriorityResourceGovernor {
    /// Create a new priority resource governor.
    #[must_use]
    pub fn new(config: PriorityGovernorConfig) -> Self {
        let base_governor = governor::ResourceGovernor::new(config.base);
        Self {
            inner: Arc::new(GovernorState {
                base_governor,
                slot_state: Mutex::new(SlotState {
                    critical_active: 0,
                    normal_active: 0,
                }),
                slot_available: Condvar::new(),
                reserved_critical_fraction: config.reserved_critical_fraction.clamp(0.0, 1.0),
                shutdown: AtomicBool::new(false),
                stat_total_requests: AtomicU64::new(0),
                stat_total_grants: AtomicU64::new(0),
                stat_total_denials: AtomicU64::new(0),
                stat_total_wait_us: AtomicU64::new(0),
                stat_max_wait_us: AtomicU64::new(0),
                stat_peak_active: AtomicUsize::new(0),
                stat_grants_critical: AtomicU64::new(0),
                stat_grants_normal: AtomicU64::new(0),
                stat_grants_low: AtomicU64::new(0),
                stat_grants_background: AtomicU64::new(0),
                stat_denials_critical: AtomicU64::new(0),
                stat_denials_normal: AtomicU64::new(0),
                stat_denials_low: AtomicU64::new(0),
                stat_denials_background: AtomicU64::new(0),
            }),
        }
    }

    /// Create a governor using jobserver-aware defaults.
    #[must_use]
    pub fn from_jobserver() -> Self {
        Self::new(PriorityGovernorConfig::from_jobserver())
    }

    /// Request resources from the governor.
    ///
    /// Blocks until the requested slots are available (respecting priority
    /// reservation), or returns an error if the budget is exhausted, the
    /// governor is shut down, or the wait timeout expires.
    pub fn request_resources(
        &self,
        request: ResourceRequest,
    ) -> Result<ResourceGrant, GovernorError> {
        let wait_start = Instant::now();
        self.inner.stat_total_requests.fetch_add(1, Ordering::Relaxed);

        // Pre-checks.
        if self.inner.shutdown.load(Ordering::SeqCst) {
            self.record_denial(request.priority);
            return Err(GovernorError::Shutdown);
        }
        if self.inner.base_governor.budget_exhausted() {
            self.record_denial(request.priority);
            return Err(self.budget_exhausted_error());
        }

        let max_slots = self.inner.base_governor.max_concurrent();
        let slots_needed = request.solver_slots.min(max_slots).max(1);
        let memory_budget = if request.memory_bytes > 0 {
            request.memory_bytes
        } else {
            self.inner.base_governor.config().max_memory_per_solver
        };

        // Compute deadline from request-level or governor-level timeout.
        let deadline = request.wait_timeout
            .or(self.inner.base_governor.config().acquire_timeout)
            .map(|d| Instant::now() + d);

        let mut state = self.inner.slot_state.lock()
            .unwrap_or_else(|e| e.into_inner());

        loop {
            // Check exit conditions inside the loop.
            if self.inner.shutdown.load(Ordering::SeqCst) {
                self.record_denial(request.priority);
                return Err(GovernorError::Shutdown);
            }
            if self.inner.base_governor.budget_exhausted() {
                self.record_denial(request.priority);
                return Err(self.budget_exhausted_error());
            }

            let can_acquire = self.can_acquire_slots(&state, slots_needed, max_slots, request.priority);
            if can_acquire {
                // Grant the slots.
                match request.priority {
                    VerificationPriority::Critical => {
                        state.critical_active += slots_needed;
                    }
                    _ => {
                        state.normal_active += slots_needed;
                    }
                }

                // Update peak.
                let total = state.total_active();
                let _ = self.inner.stat_peak_active.fetch_max(total, Ordering::Relaxed);

                let wait_time = wait_start.elapsed();
                self.record_grant(request.priority, wait_time);

                return Ok(ResourceGrant {
                    inner: Arc::clone(&self.inner),
                    slots_granted: slots_needed,
                    memory_budget,
                    priority: request.priority,
                    wait_time,
                    task_id: request.task_id,
                    released: AtomicBool::new(false),
                });
            }

            // Wait for a slot to become available.
            if let Some(deadline) = deadline {
                let remaining = deadline.saturating_duration_since(Instant::now());
                if remaining.is_zero() {
                    self.record_denial(request.priority);
                    return Err(GovernorError::AcquireTimeout {
                        wait_ms: wait_start.elapsed().as_millis() as u64,
                    });
                }
                let result = self.inner.slot_available.wait_timeout(state, remaining)
                    .unwrap_or_else(|e| e.into_inner());
                state = result.0;
                if result.1.timed_out() {
                    // Re-check before giving up.
                    let can = self.can_acquire_slots(&state, slots_needed, max_slots, request.priority);
                    if !can {
                        self.record_denial(request.priority);
                        return Err(GovernorError::AcquireTimeout {
                            wait_ms: wait_start.elapsed().as_millis() as u64,
                        });
                    }
                }
            } else {
                state = self.inner.slot_available.wait(state)
                    .unwrap_or_else(|e| e.into_inner());
            }
        }
    }

    /// Try to acquire resources without blocking.
    ///
    /// Returns `Ok(grant)` if resources are immediately available, or
    /// `Err` if not. Does not wait.
    pub fn try_request_resources(
        &self,
        request: ResourceRequest,
    ) -> Result<ResourceGrant, GovernorError> {
        let mut req = request;
        req.wait_timeout = Some(Duration::ZERO);
        self.request_resources(req)
    }

    /// Query the current backpressure level.
    ///
    /// Callers should check this before submitting large portfolio races
    /// and reduce concurrency accordingly.
    #[must_use]
    pub fn backpressure(&self) -> BackpressureSignal {
        let max_slots = self.inner.base_governor.max_concurrent();
        if max_slots == 0 {
            return BackpressureSignal::Overloaded;
        }

        let state = self.inner.slot_state.lock()
            .unwrap_or_else(|e| e.into_inner());
        let active = state.total_active();
        let utilization = active as f64 / max_slots as f64;

        if utilization >= 0.95 {
            BackpressureSignal::Overloaded
        } else if utilization >= 0.80 {
            BackpressureSignal::High
        } else if utilization >= 0.60 {
            // Recommend at most half the remaining slots.
            let remaining = max_slots.saturating_sub(active);
            let recommended = (remaining / 2).max(1);
            BackpressureSignal::Moderate { recommended_solvers: recommended }
        } else {
            BackpressureSignal::None
        }
    }

    /// Get a snapshot of the governor's statistics.
    #[must_use]
    pub fn statistics(&self) -> GovernorStatistics {
        let max_slots = self.inner.base_governor.max_concurrent();
        let state = self.inner.slot_state.lock()
            .unwrap_or_else(|e| e.into_inner());
        let active = state.total_active();
        let utilization = if max_slots > 0 {
            active as f64 / max_slots as f64
        } else {
            0.0
        };

        GovernorStatistics {
            total_requests: self.inner.stat_total_requests.load(Ordering::Relaxed),
            total_grants: self.inner.stat_total_grants.load(Ordering::Relaxed),
            total_denials: self.inner.stat_total_denials.load(Ordering::Relaxed),
            total_wait_time_us: self.inner.stat_total_wait_us.load(Ordering::Relaxed),
            max_wait_time_us: self.inner.stat_max_wait_us.load(Ordering::Relaxed),
            current_utilization: utilization,
            current_active_slots: active,
            peak_active_slots: self.inner.stat_peak_active.load(Ordering::Relaxed),
            grants_by_priority: [
                self.inner.stat_grants_critical.load(Ordering::Relaxed),
                self.inner.stat_grants_normal.load(Ordering::Relaxed),
                self.inner.stat_grants_low.load(Ordering::Relaxed),
                self.inner.stat_grants_background.load(Ordering::Relaxed),
            ],
            denials_by_priority: [
                self.inner.stat_denials_critical.load(Ordering::Relaxed),
                self.inner.stat_denials_normal.load(Ordering::Relaxed),
                self.inner.stat_denials_low.load(Ordering::Relaxed),
                self.inner.stat_denials_background.load(Ordering::Relaxed),
            ],
        }
    }

    /// Shut down the governor, waking all waiters.
    pub fn shutdown(&self) {
        self.inner.shutdown.store(true, Ordering::SeqCst);
        self.inner.base_governor.shutdown();
        self.inner.slot_available.notify_all();
    }

    /// Maximum concurrent solvers configured.
    #[must_use]
    pub fn max_concurrent(&self) -> usize {
        self.inner.base_governor.max_concurrent()
    }

    /// Current number of active slots.
    #[must_use]
    pub fn active_slots(&self) -> usize {
        let state = self.inner.slot_state.lock()
            .unwrap_or_else(|e| e.into_inner());
        state.total_active()
    }

    /// Access the underlying base governor configuration.
    #[must_use]
    pub fn config(&self) -> &GovernorConfig {
        self.inner.base_governor.config()
    }

    // -- internal helpers --

    /// Check whether `slots_needed` can be acquired at the given priority.
    fn can_acquire_slots(
        &self,
        state: &SlotState,
        slots_needed: usize,
        max_slots: usize,
        priority: VerificationPriority,
    ) -> bool {
        let total_active = state.total_active();

        // Basic capacity check.
        if total_active + slots_needed > max_slots {
            return false;
        }

        // Priority reservation: non-critical requests cannot consume
        // slots reserved for critical tasks.
        if priority != VerificationPriority::Critical {
            let reserved = (max_slots as f64 * self.inner.reserved_critical_fraction).ceil() as usize;
            let available_for_normal = max_slots.saturating_sub(reserved);
            if state.normal_active + slots_needed > available_for_normal {
                return false;
            }
        }

        true
    }

    fn record_grant(&self, priority: VerificationPriority, wait_time: Duration) {
        self.inner.stat_total_grants.fetch_add(1, Ordering::Relaxed);
        let wait_us = wait_time.as_micros() as u64;
        self.inner.stat_total_wait_us.fetch_add(wait_us, Ordering::Relaxed);
        let _ = self.inner.stat_max_wait_us.fetch_max(wait_us, Ordering::Relaxed);

        match priority {
            VerificationPriority::Critical => {
                self.inner.stat_grants_critical.fetch_add(1, Ordering::Relaxed);
            }
            VerificationPriority::Normal => {
                self.inner.stat_grants_normal.fetch_add(1, Ordering::Relaxed);
            }
            VerificationPriority::Low => {
                self.inner.stat_grants_low.fetch_add(1, Ordering::Relaxed);
            }
            VerificationPriority::Background => {
                self.inner.stat_grants_background.fetch_add(1, Ordering::Relaxed);
            }
        }
    }

    fn record_denial(&self, priority: VerificationPriority) {
        self.inner.stat_total_denials.fetch_add(1, Ordering::Relaxed);

        match priority {
            VerificationPriority::Critical => {
                self.inner.stat_denials_critical.fetch_add(1, Ordering::Relaxed);
            }
            VerificationPriority::Normal => {
                self.inner.stat_denials_normal.fetch_add(1, Ordering::Relaxed);
            }
            VerificationPriority::Low => {
                self.inner.stat_denials_low.fetch_add(1, Ordering::Relaxed);
            }
            VerificationPriority::Background => {
                self.inner.stat_denials_background.fetch_add(1, Ordering::Relaxed);
            }
        }
    }

    fn budget_exhausted_error(&self) -> GovernorError {
        let config = self.inner.base_governor.config();
        GovernorError::TimeoutBudgetExhausted {
            elapsed_ms: config.total_timeout_budget.as_millis() as u64,
            budget_ms: config.total_timeout_budget.as_millis() as u64,
        }
    }
}

// ---------------------------------------------------------------------------
// GovernoredPortfolioRacer: portfolio racer with governor integration
// ---------------------------------------------------------------------------

/// tRust #196: Portfolio racer that respects the resource governor.
///
/// Wraps `PortfolioRacer` to acquire governor slots before racing, and
/// adjusts the number of concurrent solvers based on backpressure signals.
/// Ensures that portfolio races do not starve other verification tasks.
pub struct GovernoredPortfolioRacer {
    racer: crate::portfolio_racer::PortfolioRacer,
    governor: PriorityResourceGovernor,
}

impl GovernoredPortfolioRacer {
    /// Create a new governored portfolio racer.
    pub fn new(
        racer: crate::portfolio_racer::PortfolioRacer,
        governor: PriorityResourceGovernor,
    ) -> Self {
        Self { racer, governor }
    }

    /// Race with governor-managed resources.
    ///
    /// Queries backpressure to determine how many solvers to race, acquires
    /// slots from the governor, runs the race, then releases slots on
    /// completion.
    pub fn governed_race(
        &self,
        vc: &trust_types::VerificationCondition,
        config: &crate::portfolio_racer::RaceConfig,
        priority: VerificationPriority,
    ) -> Result<crate::portfolio_racer::RaceResult, GovernorError> {
        // Check backpressure and adjust solver count.
        let effective_max_solvers = match self.governor.backpressure() {
            BackpressureSignal::None => config.max_solvers,
            BackpressureSignal::Moderate { recommended_solvers } => {
                config.max_solvers.min(recommended_solvers)
            }
            BackpressureSignal::High => 1,
            BackpressureSignal::Overloaded => {
                // Only proceed for Critical priority under overload.
                if priority != VerificationPriority::Critical {
                    return Err(GovernorError::AcquireTimeout { wait_ms: 0 });
                }
                1
            }
        };

        // Request slots from the governor.
        let request = ResourceRequest::portfolio(
            format!("race_{}", vc.function),
            effective_max_solvers,
            priority,
        );

        let grant = self.governor.request_resources(request)?;

        // Build an adjusted config with the governor-limited solver count.
        let adjusted_config = crate::portfolio_racer::RaceConfig {
            max_solvers: grant.slots_granted,
            timeout: config.timeout,
            priority_order: config.priority_order.clone(),
            use_query_class: config.use_query_class,
        };

        let result = self.racer.race(vc, &adjusted_config);

        // Grant is dropped here, releasing slots.
        drop(grant);

        Ok(result)
    }

    /// Access the underlying governor for statistics or configuration.
    #[must_use]
    pub fn governor(&self) -> &PriorityResourceGovernor {
        &self.governor
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use std::thread;

    use trust_types::*;

    use super::*;

    fn test_config(max_solvers: usize) -> PriorityGovernorConfig {
        PriorityGovernorConfig {
            base: GovernorConfig {
                max_concurrent_solvers: max_solvers,
                max_memory_per_solver: 512 * 1024 * 1024,
                total_timeout_budget: Duration::ZERO, // unlimited
                acquire_timeout: None,
            },
            reserved_critical_fraction: 0.25,
        }
    }

    fn test_vc() -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "test_fn".to_string(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
        }
    }

    // -----------------------------------------------------------------------
    // ResourceRequest construction
    // -----------------------------------------------------------------------

    #[test]
    fn test_resource_request_single() {
        let req = ResourceRequest::single("vc_1", VerificationPriority::Critical);
        assert_eq!(req.task_id, "vc_1");
        assert_eq!(req.solver_slots, 1);
        assert_eq!(req.priority, VerificationPriority::Critical);
        assert_eq!(req.memory_bytes, 0);
        assert!(req.wait_timeout.is_none());
    }

    #[test]
    fn test_resource_request_portfolio() {
        let req = ResourceRequest::portfolio("race_1", 4, VerificationPriority::Normal);
        assert_eq!(req.solver_slots, 4);
        assert_eq!(req.priority, VerificationPriority::Normal);
    }

    #[test]
    fn test_resource_request_portfolio_clamps_to_one() {
        let req = ResourceRequest::portfolio("race_1", 0, VerificationPriority::Low);
        assert_eq!(req.solver_slots, 1);
    }

    #[test]
    fn test_resource_request_with_memory() {
        let req = ResourceRequest::single("vc_1", VerificationPriority::Normal)
            .with_memory(1024 * 1024);
        assert_eq!(req.memory_bytes, 1024 * 1024);
    }

    #[test]
    fn test_resource_request_with_timeout() {
        let req = ResourceRequest::single("vc_1", VerificationPriority::Normal)
            .with_timeout(Duration::from_secs(5));
        assert_eq!(req.wait_timeout, Some(Duration::from_secs(5)));
    }

    // -----------------------------------------------------------------------
    // VerificationPriority
    // -----------------------------------------------------------------------

    #[test]
    fn test_priority_from_proof_level() {
        assert_eq!(
            VerificationPriority::from_proof_level(ProofLevel::L0Safety),
            VerificationPriority::Critical
        );
        assert_eq!(
            VerificationPriority::from_proof_level(ProofLevel::L1Functional),
            VerificationPriority::Normal
        );
        assert_eq!(
            VerificationPriority::from_proof_level(ProofLevel::L2Domain),
            VerificationPriority::Low
        );
    }

    #[test]
    fn test_priority_ordering() {
        assert!(VerificationPriority::Critical < VerificationPriority::Normal);
        assert!(VerificationPriority::Normal < VerificationPriority::Low);
        assert!(VerificationPriority::Low < VerificationPriority::Background);
    }

    // -----------------------------------------------------------------------
    // PriorityResourceGovernor: basic acquire/release
    // -----------------------------------------------------------------------

    #[test]
    fn test_governor_acquire_and_release() {
        let gov = PriorityResourceGovernor::new(test_config(4));
        assert_eq!(gov.active_slots(), 0);

        let grant = gov.request_resources(
            ResourceRequest::single("vc_1", VerificationPriority::Normal),
        ).expect("should grant");

        assert_eq!(gov.active_slots(), 1);
        assert_eq!(grant.slots_granted, 1);
        assert_eq!(grant.priority, VerificationPriority::Normal);

        drop(grant);
        assert_eq!(gov.active_slots(), 0);
    }

    #[test]
    fn test_governor_multi_slot_acquire() {
        let gov = PriorityResourceGovernor::new(test_config(8));

        let grant = gov.request_resources(
            ResourceRequest::portfolio("race_1", 3, VerificationPriority::Normal),
        ).expect("should grant 3 slots");

        assert_eq!(grant.slots_granted, 3);
        assert_eq!(gov.active_slots(), 3);

        drop(grant);
        assert_eq!(gov.active_slots(), 0);
    }

    #[test]
    fn test_governor_slots_clamped_to_max() {
        let gov = PriorityResourceGovernor::new(test_config(2));

        // Requesting 10 slots should be clamped to 2.
        let grant = gov.request_resources(
            ResourceRequest::portfolio("race_1", 10, VerificationPriority::Critical),
        ).expect("should grant clamped slots");

        assert_eq!(grant.slots_granted, 2);
        drop(grant);
    }

    // -----------------------------------------------------------------------
    // Priority reservation
    // -----------------------------------------------------------------------

    #[test]
    fn test_critical_priority_can_use_reserved_slots() {
        // 4 slots, 25% reserved = 1 reserved for Critical.
        // Normal can use at most 3 (4 - ceil(4 * 0.25) = 4 - 1 = 3).
        let gov = PriorityResourceGovernor::new(test_config(4));

        // Fill 3 normal slots.
        let n1 = gov.request_resources(
            ResourceRequest::single("n1", VerificationPriority::Normal),
        ).expect("normal slot 1");
        let n2 = gov.request_resources(
            ResourceRequest::single("n2", VerificationPriority::Normal),
        ).expect("normal slot 2");
        let n3 = gov.request_resources(
            ResourceRequest::single("n3", VerificationPriority::Normal),
        ).expect("normal slot 3");
        assert_eq!(gov.active_slots(), 3);

        // Normal should NOT get a 4th slot (reserved for Critical).
        let n4_result = gov.try_request_resources(
            ResourceRequest::single("n4", VerificationPriority::Normal),
        );
        assert!(n4_result.is_err(), "normal should not get reserved slot");

        // Critical SHOULD get the 4th slot.
        let c1 = gov.request_resources(
            ResourceRequest::single("c1", VerificationPriority::Critical),
        ).expect("critical should get reserved slot");
        assert_eq!(gov.active_slots(), 4);

        drop(n1);
        drop(n2);
        drop(n3);
        drop(c1);
        assert_eq!(gov.active_slots(), 0);
    }

    #[test]
    fn test_critical_uses_all_slots_when_no_normal() {
        // With no normal tasks, Critical can use all slots.
        let gov = PriorityResourceGovernor::new(test_config(4));

        let c1 = gov.request_resources(
            ResourceRequest::single("c1", VerificationPriority::Critical),
        ).expect("c1");
        let c2 = gov.request_resources(
            ResourceRequest::single("c2", VerificationPriority::Critical),
        ).expect("c2");
        let c3 = gov.request_resources(
            ResourceRequest::single("c3", VerificationPriority::Critical),
        ).expect("c3");
        let c4 = gov.request_resources(
            ResourceRequest::single("c4", VerificationPriority::Critical),
        ).expect("c4");
        assert_eq!(gov.active_slots(), 4);

        drop(c1);
        drop(c2);
        drop(c3);
        drop(c4);
    }

    // -----------------------------------------------------------------------
    // Backpressure
    // -----------------------------------------------------------------------

    #[test]
    fn test_backpressure_none_when_empty() {
        let gov = PriorityResourceGovernor::new(test_config(10));
        assert_eq!(gov.backpressure(), BackpressureSignal::None);
        assert!(!gov.backpressure().should_reduce());
        assert!(!gov.backpressure().should_defer_non_critical());
    }

    #[test]
    fn test_backpressure_moderate_at_60_percent() {
        let gov = PriorityResourceGovernor::new(test_config(10));

        // Fill 6 of 10 slots (60% utilization) with Critical to bypass reservation.
        let _grants: Vec<_> = (0..6)
            .map(|i| {
                gov.request_resources(
                    ResourceRequest::single(format!("c{i}"), VerificationPriority::Critical),
                ).expect("slot")
            })
            .collect();

        let bp = gov.backpressure();
        assert!(matches!(bp, BackpressureSignal::Moderate { .. }));
        assert!(bp.should_reduce());
        assert!(!bp.should_defer_non_critical());
    }

    #[test]
    fn test_backpressure_high_at_80_percent() {
        let gov = PriorityResourceGovernor::new(test_config(10));

        let _grants: Vec<_> = (0..8)
            .map(|i| {
                gov.request_resources(
                    ResourceRequest::single(format!("c{i}"), VerificationPriority::Critical),
                ).expect("slot")
            })
            .collect();

        let bp = gov.backpressure();
        assert_eq!(bp, BackpressureSignal::High);
        assert!(bp.should_defer_non_critical());
    }

    #[test]
    fn test_backpressure_overloaded_at_95_percent() {
        // Use 20 slots so 95% = 19.
        let gov = PriorityResourceGovernor::new(test_config(20));

        let _grants: Vec<_> = (0..19)
            .map(|i| {
                gov.request_resources(
                    ResourceRequest::single(format!("c{i}"), VerificationPriority::Critical),
                ).expect("slot")
            })
            .collect();

        assert_eq!(gov.backpressure(), BackpressureSignal::Overloaded);
    }

    // -----------------------------------------------------------------------
    // Statistics
    // -----------------------------------------------------------------------

    #[test]
    fn test_statistics_initially_zero() {
        let gov = PriorityResourceGovernor::new(test_config(4));
        let stats = gov.statistics();

        assert_eq!(stats.total_requests, 0);
        assert_eq!(stats.total_grants, 0);
        assert_eq!(stats.total_denials, 0);
        assert_eq!(stats.current_active_slots, 0);
        assert_eq!(stats.peak_active_slots, 0);
        assert_eq!(stats.current_utilization, 0.0);
    }

    #[test]
    fn test_statistics_after_grants() {
        let gov = PriorityResourceGovernor::new(test_config(4));

        let g1 = gov.request_resources(
            ResourceRequest::single("c1", VerificationPriority::Critical),
        ).expect("grant");
        let g2 = gov.request_resources(
            ResourceRequest::single("n1", VerificationPriority::Normal),
        ).expect("grant");

        let stats = gov.statistics();
        assert_eq!(stats.total_requests, 2);
        assert_eq!(stats.total_grants, 2);
        assert_eq!(stats.total_denials, 0);
        assert_eq!(stats.current_active_slots, 2);
        assert_eq!(stats.current_utilization, 0.5); // 2/4
        assert_eq!(stats.grants_by_priority[0], 1); // Critical
        assert_eq!(stats.grants_by_priority[1], 1); // Normal

        drop(g1);
        drop(g2);

        let stats2 = gov.statistics();
        assert_eq!(stats2.current_active_slots, 0);
        assert_eq!(stats2.peak_active_slots, 2);
    }

    #[test]
    fn test_statistics_denial_counted() {
        let gov = PriorityResourceGovernor::new(PriorityGovernorConfig {
            base: GovernorConfig {
                max_concurrent_solvers: 1,
                total_timeout_budget: Duration::ZERO,
                acquire_timeout: None,
                ..GovernorConfig::default()
            },
            reserved_critical_fraction: 0.0,
        });

        let _g1 = gov.request_resources(
            ResourceRequest::single("c1", VerificationPriority::Normal),
        ).expect("grant");

        // Try-acquire should fail (no slots).
        let result = gov.try_request_resources(
            ResourceRequest::single("c2", VerificationPriority::Low),
        );
        assert!(result.is_err());

        let stats = gov.statistics();
        assert_eq!(stats.total_requests, 2);
        assert_eq!(stats.total_grants, 1);
        assert_eq!(stats.total_denials, 1);
        assert_eq!(stats.denials_by_priority[2], 1); // Low
    }

    #[test]
    fn test_statistics_peak_tracks_high_water_mark() {
        let gov = PriorityResourceGovernor::new(test_config(4));

        let g1 = gov.request_resources(
            ResourceRequest::single("c1", VerificationPriority::Critical),
        ).expect("g1");
        let g2 = gov.request_resources(
            ResourceRequest::single("c2", VerificationPriority::Critical),
        ).expect("g2");
        let g3 = gov.request_resources(
            ResourceRequest::single("c3", VerificationPriority::Critical),
        ).expect("g3");

        assert_eq!(gov.statistics().peak_active_slots, 3);

        drop(g1);
        drop(g2);
        drop(g3);

        // Peak should not decrease.
        assert_eq!(gov.statistics().peak_active_slots, 3);
        assert_eq!(gov.statistics().current_active_slots, 0);
    }

    // -----------------------------------------------------------------------
    // Shutdown
    // -----------------------------------------------------------------------

    #[test]
    fn test_shutdown_denies_new_requests() {
        let gov = PriorityResourceGovernor::new(test_config(4));
        gov.shutdown();

        let result = gov.request_resources(
            ResourceRequest::single("vc_1", VerificationPriority::Critical),
        );
        assert!(matches!(result, Err(GovernorError::Shutdown)));
    }

    #[test]
    fn test_shutdown_wakes_blocked_waiter() {
        let gov = PriorityResourceGovernor::new(PriorityGovernorConfig {
            base: GovernorConfig {
                max_concurrent_solvers: 1,
                total_timeout_budget: Duration::ZERO,
                acquire_timeout: None,
                ..GovernorConfig::default()
            },
            reserved_critical_fraction: 0.0,
        });

        // Fill the single slot.
        let _g1 = gov.request_resources(
            ResourceRequest::single("c1", VerificationPriority::Critical),
        ).expect("g1");

        let gov_clone = gov.clone();
        let handle = thread::spawn(move || {
            gov_clone.request_resources(
                ResourceRequest::single("c2", VerificationPriority::Critical),
            )
        });

        thread::sleep(Duration::from_millis(50));
        gov.shutdown();

        let result = handle.join().expect("thread should not panic");
        assert!(matches!(result, Err(GovernorError::Shutdown)));
    }

    // -----------------------------------------------------------------------
    // Timeout budget
    // -----------------------------------------------------------------------

    #[test]
    fn test_budget_exhaustion_denies_request() {
        let gov = PriorityResourceGovernor::new(PriorityGovernorConfig {
            base: GovernorConfig {
                max_concurrent_solvers: 4,
                total_timeout_budget: Duration::from_millis(30),
                acquire_timeout: None,
                ..GovernorConfig::default()
            },
            reserved_critical_fraction: 0.25,
        });

        thread::sleep(Duration::from_millis(40));

        let result = gov.request_resources(
            ResourceRequest::single("vc_1", VerificationPriority::Critical),
        );
        assert!(matches!(result, Err(GovernorError::TimeoutBudgetExhausted { .. })));
    }

    // -----------------------------------------------------------------------
    // Grant metadata
    // -----------------------------------------------------------------------

    #[test]
    fn test_grant_metadata() {
        let gov = PriorityResourceGovernor::new(test_config(4));

        let grant = gov.request_resources(
            ResourceRequest::single("vc_42", VerificationPriority::Critical)
                .with_memory(1024),
        ).expect("grant");

        assert_eq!(grant.task_id, "vc_42");
        assert_eq!(grant.priority, VerificationPriority::Critical);
        assert_eq!(grant.slots_granted, 1);
        assert_eq!(grant.memory_budget, 1024);
        // Wait time should be very small for an uncontested acquisition.
        assert!(grant.wait_time < Duration::from_millis(100));
    }

    #[test]
    fn test_grant_budget_check() {
        let gov = PriorityResourceGovernor::new(PriorityGovernorConfig {
            base: GovernorConfig {
                max_concurrent_solvers: 4,
                total_timeout_budget: Duration::from_secs(60),
                acquire_timeout: None,
                ..GovernorConfig::default()
            },
            reserved_critical_fraction: 0.25,
        });

        let grant = gov.request_resources(
            ResourceRequest::single("vc_1", VerificationPriority::Normal),
        ).expect("grant");

        assert!(!grant.budget_exhausted());
        assert!(grant.remaining_budget().is_some());
    }

    // -----------------------------------------------------------------------
    // Concurrent access stress test
    // -----------------------------------------------------------------------

    #[test]
    fn test_concurrent_mixed_priorities() {
        let gov = PriorityResourceGovernor::new(PriorityGovernorConfig {
            base: GovernorConfig {
                max_concurrent_solvers: 4,
                total_timeout_budget: Duration::ZERO,
                acquire_timeout: Some(Duration::from_secs(10)),
                ..GovernorConfig::default()
            },
            reserved_critical_fraction: 0.25,
        });

        let handles: Vec<_> = (0..12)
            .map(|i| {
                let gov = gov.clone();
                thread::spawn(move || {
                    let priority = match i % 3 {
                        0 => VerificationPriority::Critical,
                        1 => VerificationPriority::Normal,
                        _ => VerificationPriority::Low,
                    };
                    let grant = gov.request_resources(
                        ResourceRequest::single(format!("vc_{i}"), priority),
                    ).expect("should eventually grant");
                    assert!(gov.active_slots() <= 4);
                    thread::sleep(Duration::from_millis(5));
                    drop(grant);
                })
            })
            .collect();

        for h in handles {
            h.join().expect("thread should not panic");
        }

        assert_eq!(gov.active_slots(), 0);
        let stats = gov.statistics();
        assert_eq!(stats.total_grants, 12);
        assert_eq!(stats.total_denials, 0);
        assert_eq!(stats.current_active_slots, 0);
        assert!(stats.peak_active_slots <= 4);
    }

    // -----------------------------------------------------------------------
    // GovernoredPortfolioRacer
    // -----------------------------------------------------------------------

    #[test]
    fn test_governored_racer_basic() {
        let gov = PriorityResourceGovernor::new(test_config(4));
        let racer = crate::portfolio_racer::PortfolioRacer::new(vec![
            Arc::new(crate::mock_backend::MockBackend),
        ]);
        let governed = GovernoredPortfolioRacer::new(racer, gov.clone());

        let vc = test_vc();
        let config = crate::portfolio_racer::RaceConfig::default()
            .with_max_solvers(1)
            .with_timeout(Duration::from_secs(5));

        let result = governed.governed_race(&vc, &config, VerificationPriority::Normal)
            .expect("should race");

        assert!(result.result.is_proved());
        assert_eq!(gov.active_slots(), 0);
    }

    #[test]
    fn test_governored_racer_reduces_under_pressure() {
        // Create a governor with 4 slots and fill 3.
        let gov = PriorityResourceGovernor::new(test_config(4));

        let _g1 = gov.request_resources(
            ResourceRequest::single("g1", VerificationPriority::Critical),
        ).expect("g1");
        let _g2 = gov.request_resources(
            ResourceRequest::single("g2", VerificationPriority::Critical),
        ).expect("g2");
        let _g3 = gov.request_resources(
            ResourceRequest::single("g3", VerificationPriority::Critical),
        ).expect("g3");

        // 3/4 = 75% utilization. With only 1 slot remaining, both High
        // backpressure and the reservation check will limit the race to 1 solver.
        let racer = crate::portfolio_racer::PortfolioRacer::new(vec![
            Arc::new(crate::mock_backend::MockBackend),
        ]);
        let governed = GovernoredPortfolioRacer::new(racer, gov.clone());

        let vc = test_vc();
        let config = crate::portfolio_racer::RaceConfig::default()
            .with_max_solvers(1)
            .with_timeout(Duration::from_secs(5));

        let result = governed.governed_race(&vc, &config, VerificationPriority::Critical)
            .expect("should race with reduced solvers");

        assert!(result.result.is_proved());
    }

    #[test]
    fn test_governored_racer_governor_accessor() {
        let gov = PriorityResourceGovernor::new(test_config(4));
        let racer = crate::portfolio_racer::PortfolioRacer::new(vec![]);
        let governed = GovernoredPortfolioRacer::new(racer, gov);

        assert_eq!(governed.governor().max_concurrent(), 4);
    }

    // -----------------------------------------------------------------------
    // BackpressureSignal
    // -----------------------------------------------------------------------

    #[test]
    fn test_backpressure_signal_none() {
        let bp = BackpressureSignal::None;
        assert!(!bp.should_reduce());
        assert!(!bp.should_defer_non_critical());
    }

    #[test]
    fn test_backpressure_signal_moderate() {
        let bp = BackpressureSignal::Moderate { recommended_solvers: 2 };
        assert!(bp.should_reduce());
        assert!(!bp.should_defer_non_critical());
    }

    #[test]
    fn test_backpressure_signal_high() {
        let bp = BackpressureSignal::High;
        assert!(bp.should_reduce());
        assert!(bp.should_defer_non_critical());
    }

    #[test]
    fn test_backpressure_signal_overloaded() {
        let bp = BackpressureSignal::Overloaded;
        assert!(bp.should_reduce());
        assert!(bp.should_defer_non_critical());
    }

    // -----------------------------------------------------------------------
    // Config defaults
    // -----------------------------------------------------------------------

    #[test]
    fn test_priority_governor_config_default() {
        let config = PriorityGovernorConfig::default();
        assert!(config.base.max_concurrent_solvers >= 1);
        assert_eq!(config.reserved_critical_fraction, 0.25);
    }

    #[test]
    fn test_priority_governor_config_from_jobserver() {
        let config = PriorityGovernorConfig::from_jobserver();
        assert!(config.base.max_concurrent_solvers >= 1);
    }

    #[test]
    fn test_max_concurrent_accessor() {
        let gov = PriorityResourceGovernor::new(test_config(7));
        assert_eq!(gov.max_concurrent(), 7);
    }

    #[test]
    fn test_config_accessor() {
        let gov = PriorityResourceGovernor::new(test_config(5));
        assert_eq!(gov.config().max_concurrent_solvers, 5);
    }

    // -----------------------------------------------------------------------
    // Grant debug formatting
    // -----------------------------------------------------------------------

    #[test]
    fn test_grant_debug() {
        let gov = PriorityResourceGovernor::new(test_config(4));
        let grant = gov.request_resources(
            ResourceRequest::single("vc_1", VerificationPriority::Normal),
        ).expect("grant");

        let debug = format!("{grant:?}");
        assert!(debug.contains("vc_1"));
        assert!(debug.contains("Normal"));
    }
}
