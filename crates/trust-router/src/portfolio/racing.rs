// trust-router/portfolio/racing.rs: Portfolio race function and PortfolioRacer/Runner
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex, mpsc};
use std::thread;
use std::time::Instant;

use trust_cache::proof_replay::{ProofStrategy, ReplayCache, ReplayResult, StrategyKey};
use trust_types::{VerificationCondition, VerificationResult};

use crate::VerificationBackend;
use crate::classifier::QueryClass;

use super::strategy::{classify_and_select_strategies, select_strategies};
use super::types::{
    DispatchMode, PortfolioLane, PortfolioResult, PortfolioStrategy, StateSpaceEstimate,
    no_backend_result,
};

// ---------------------------------------------------------------------------
// tRust #476: Helper to convert a PortfolioStrategy name to a ProofStrategy
// ---------------------------------------------------------------------------

/// tRust #476: Build a `ProofStrategy` from a portfolio race winner.
fn to_proof_strategy(strategy: PortfolioStrategy, solver_name: &str, time_ms: u64) -> ProofStrategy {
    ProofStrategy::new(solver_name, time_ms)
        .with_hint(format!("portfolio:{}", strategy.name()))
}

/// tRust #476: Build a `StrategyKey` from a VC for replay cache lookups.
///
/// Uses VcKind name, a simple structure hash from the formula Debug repr,
/// and formula metadata. This is a best-effort structural fingerprint.
#[must_use]
pub fn vc_to_strategy_key(vc: &VerificationCondition) -> StrategyKey {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};

    let kind = format!("{:?}", vc.kind);
    let mut hasher = DefaultHasher::new();
    format!("{:?}", vc.formula).hash(&mut hasher);
    let structure_hash = hasher.finish();

    // tRust #476: Approximate var_count and depth from formula Debug length.
    // A proper implementation would walk the formula tree, but this is
    // sufficient for cache keying since structure_hash captures the full shape.
    let formula_debug = format!("{:?}", vc.formula);
    let var_count = formula_debug.matches("Var(").count();
    let depth = formula_debug.matches('(').count().min(255);

    StrategyKey::new(kind, structure_hash, var_count, depth)
}

/// tRust #476: Map a cached `ProofStrategy` solver hint back to a `PortfolioStrategy`.
///
/// Looks for `portfolio:<name>` hints in the cached strategy. Returns `None`
/// if no matching strategy is found.
#[must_use]
fn hint_to_portfolio_strategy(strategy: &ProofStrategy) -> Option<PortfolioStrategy> {
    for hint in &strategy.hints {
        if let Some(name) = hint.strip_prefix("portfolio:") {
            return match name {
                "bmc" => Some(PortfolioStrategy::Bmc),
                "bfs" => Some(PortfolioStrategy::Bfs),
                "ic3pdr" => Some(PortfolioStrategy::Ic3Pdr),
                "k-induction" => Some(PortfolioStrategy::KInduction),
                "structural" => Some(PortfolioStrategy::Structural),
                "sp" => Some(PortfolioStrategy::StrongestPostcondition),
                _ => None,
            };
        }
    }
    None
}

/// tRust: Race multiple verification strategies in parallel for a single VC.
///
/// Spawns one thread per lane. The first definitive result (Proved or
/// Counterexample) wins and all other threads are signalled to cancel via
/// a shared `AtomicBool`. If no definitive result arrives, the best
/// non-definitive result is returned.
///
/// Returns `None` only if `lanes` is empty.
#[must_use]
pub fn race(
    vc: &VerificationCondition,
    lanes: Vec<PortfolioLane>,
) -> Option<PortfolioResult> {
    if lanes.is_empty() {
        return None;
    }

    let total_lanes = lanes.len();
    let start = Instant::now();
    let cancelled = Arc::new(AtomicBool::new(false));
    let (tx, rx) = mpsc::channel();

    let mut handles = Vec::with_capacity(lanes.len());

    for lane in lanes {
        let vc = vc.clone();
        let cancelled = Arc::clone(&cancelled);
        let tx = tx.clone();

        let handle = thread::spawn(move || {
            // tRust: Check cancellation before starting work.
            if cancelled.load(Ordering::Relaxed) {
                return;
            }

            let result = lane.backend.verify(&vc);

            // Send result regardless — the receiver decides what to keep.
            let _ = tx.send((lane.strategy, result));
        });

        handles.push(handle);
    }

    // Drop our copy of the sender so the channel closes when all threads finish.
    drop(tx);

    let mut best: Option<(PortfolioStrategy, VerificationResult)> = None;

    for (strategy, result) in rx {
        let is_definitive = result.is_proved() || result.is_failed();

        if is_definitive {
            // tRust: First definitive result wins — cancel remaining strategies.
            cancelled.store(true, Ordering::Relaxed);
            best = Some((strategy, result));
            break;
        }

        // Keep the first non-definitive result as fallback.
        if best.is_none() {
            best = Some((strategy, result));
        }
    }

    // tRust: Join all threads to avoid resource leaks.
    for handle in handles {
        let _ = handle.join();
    }

    let race_time_ms = start.elapsed().as_millis() as u64;

    best.map(|(winning_strategy, result)| PortfolioResult {
        result,
        winning_strategy,
        race_time_ms,
        total_lanes,
        replay_hit: None,
    })
}

/// tRust #476: Race with proof replay cache integration.
///
/// Before racing, looks up the VC in the replay cache. If a cached strategy
/// is found, front-loads it as the first lane. After a successful proof,
/// records the winning strategy in the cache. After a failed replay, calls
/// `record_failure()`.
///
/// Returns `None` only if `lanes` is empty.
#[must_use]
pub(crate) fn race_with_replay(
    vc: &VerificationCondition,
    mut lanes: Vec<PortfolioLane>,
    replay_cache: &Arc<Mutex<ReplayCache>>,
) -> Option<PortfolioResult> {
    if lanes.is_empty() {
        return None;
    }

    let key = vc_to_strategy_key(vc);

    // tRust #476: Step 1 — Look up cached strategy and front-load it.
    let cached_strategy = if let Ok(mut cache) = replay_cache.lock() {
        match cache.lookup(&key) {
            ReplayResult::ExactMatch(ps) | ReplayResult::PartialMatch(ps) => {
                hint_to_portfolio_strategy(&ps)
            }
            ReplayResult::Miss => None,
        }
    } else {
        None
    };

    // tRust #476: If we have a cached strategy, move it to the front of lanes.
    if let Some(preferred) = cached_strategy
        && let Some(pos) = lanes.iter().position(|l| l.strategy == preferred)
            && pos > 0 {
                let lane = lanes.remove(pos);
                lanes.insert(0, lane);
            }

    let had_cache_hint = cached_strategy.is_some();

    // tRust #476: Step 2 — Race with reordered lanes.
    let mut result = race(vc, lanes)?;

    let is_definitive = result.result.is_proved() || result.result.is_failed();

    // tRust #476: Step 3 — Record outcome in replay cache.
    if let Ok(mut cache) = replay_cache.lock() {
        if result.result.is_proved() {
            // Record the winning strategy for future lookups.
            let proof_strategy = to_proof_strategy(
                result.winning_strategy,
                result.result.solver_name(),
                result.race_time_ms,
            );
            cache.record(key, proof_strategy);
        } else if had_cache_hint && !is_definitive {
            // tRust #476: The cached strategy was tried but didn't produce a
            // definitive result — record failure to degrade its success rate.
            cache.record_failure(&key);
        }
    }

    // tRust #476: Set replay_hit based on whether the cached strategy won.
    result.replay_hit = if had_cache_hint {
        Some(cached_strategy == Some(result.winning_strategy) && is_definitive)
    } else {
        None
    };

    Some(result)
}

/// tRust: Portfolio racer with reusable configuration.
///
/// Wraps a set of backends mapped to strategies. Call `race()` to verify
/// a single VC, or `race_all()` to verify multiple VCs sequentially
/// (each gets its own parallel race).
///
/// tRust #476: Optionally integrates with a `ReplayCache` to front-load
/// previously successful strategies and record new wins.
pub struct PortfolioRacer {
    lanes: Vec<(PortfolioStrategy, Arc<dyn VerificationBackend>)>,
    /// tRust #476: Optional proof replay cache for strategy reuse across VCs.
    replay_cache: Option<Arc<Mutex<ReplayCache>>>,
}

impl PortfolioRacer {
    /// Create a racer with explicit strategy-to-backend mappings.
    #[must_use]
    pub fn new(lanes: Vec<(PortfolioStrategy, Arc<dyn VerificationBackend>)>) -> Self {
        Self { lanes, replay_cache: None }
    }

    /// tRust #476: Create a racer with a proof replay cache.
    ///
    /// The replay cache is consulted before each race to front-load
    /// previously successful strategies. After each successful proof,
    /// the winning strategy is recorded.
    #[must_use]
    pub fn with_replay_cache(
        lanes: Vec<(PortfolioStrategy, Arc<dyn VerificationBackend>)>,
        replay_cache: Arc<Mutex<ReplayCache>>,
    ) -> Self {
        Self { lanes, replay_cache: Some(replay_cache) }
    }

    /// Create a racer that uses adaptive strategy selection.
    ///
    /// Maps each strategy in the selection to the provided backend. All
    /// strategies share the same backend (useful when the backend is a
    /// general-purpose solver like z4 that supports multiple modes).
    #[must_use]
    pub fn adaptive(
        estimate: StateSpaceEstimate,
        backend: Arc<dyn VerificationBackend>,
    ) -> Self {
        let strategies = select_strategies(estimate);
        let lanes = strategies.into_iter().map(|s| (s, Arc::clone(&backend))).collect();
        Self { lanes, replay_cache: None }
    }

    /// tRust #446: Create a racer with strategy ordering based on `QueryClass`.
    ///
    /// Classifies the VC's formula to determine the query type (linear
    /// arithmetic, bitvector, quantified, etc.) and orders strategies
    /// accordingly. All strategies share the same backend.
    ///
    /// Returns both the racer and the detected `QueryClass` for logging.
    #[must_use]
    pub fn classified(
        vc: &VerificationCondition,
        backend: Arc<dyn VerificationBackend>,
    ) -> (Self, QueryClass) {
        let (class, strategies) = classify_and_select_strategies(vc);
        let lanes = strategies.into_iter().map(|s| (s, Arc::clone(&backend))).collect();
        (Self { lanes, replay_cache: None }, class)
    }

    /// Race all configured strategies for a single VC.
    ///
    /// tRust #476: If a replay cache is attached, consults it before racing
    /// and records the outcome after.
    #[must_use]
    pub fn race(&self, vc: &VerificationCondition) -> Option<PortfolioResult> {
        let lanes: Vec<PortfolioLane> = self
            .lanes
            .iter()
            .map(|(strategy, backend)| PortfolioLane {
                strategy: *strategy,
                backend: Arc::clone(backend),
            })
            .collect();

        // tRust #476: Use replay-aware race if cache is available.
        if let Some(ref cache) = self.replay_cache {
            race_with_replay(vc, lanes, cache)
        } else {
            race(vc, lanes)
        }
    }

    /// Race strategies for each VC sequentially. Each VC gets its own
    /// parallel race across all configured strategies.
    #[must_use]
    pub fn race_all(
        &self,
        vcs: &[VerificationCondition],
    ) -> Vec<(VerificationCondition, PortfolioResult)> {
        vcs.iter()
            .filter_map(|vc| self.race(vc).map(|result| (vc.clone(), result)))
            .collect()
    }

    /// Number of configured lanes.
    #[must_use]
    pub fn lane_count(&self) -> usize {
        self.lanes.len()
    }

    /// tRust #476: Whether a replay cache is attached.
    #[must_use]
    pub fn has_replay_cache(&self) -> bool {
        self.replay_cache.is_some()
    }
}

/// tRust: Portfolio runner that dispatches VCs using a configurable strategy.
///
/// Wraps multiple `Arc<dyn VerificationBackend>` and a `DispatchMode`.
/// Call `verify()` for a single VC, or `verify_all()` for a batch.
pub struct PortfolioRunner {
    backends: Vec<Arc<dyn VerificationBackend>>,
    mode: DispatchMode,
}

impl PortfolioRunner {
    /// Create a runner with the given backends and dispatch mode.
    #[must_use]
    pub fn new(backends: Vec<Arc<dyn VerificationBackend>>, mode: DispatchMode) -> Self {
        Self { backends, mode }
    }

    /// The dispatch mode in use.
    #[must_use]
    pub fn mode(&self) -> DispatchMode {
        self.mode
    }

    /// Number of backends available.
    #[must_use]
    pub fn backend_count(&self) -> usize {
        self.backends.len()
    }

    /// Verify a single VC according to the dispatch mode.
    #[must_use]
    pub fn verify(&self, vc: &VerificationCondition) -> VerificationResult {
        match self.mode {
            DispatchMode::Race => self.verify_race(vc),
            DispatchMode::Cascade => self.verify_cascade(vc),
            DispatchMode::Selective => self.verify_selective(vc),
        }
    }

    /// Verify a batch of VCs, returning paired results.
    #[must_use]
    pub fn verify_all(
        &self,
        vcs: &[VerificationCondition],
    ) -> Vec<(VerificationCondition, VerificationResult)> {
        vcs.iter().map(|vc| (vc.clone(), self.verify(vc))).collect()
    }

    /// tRust: Race mode — spawn all backends in parallel, first conclusive wins.
    fn verify_race(&self, vc: &VerificationCondition) -> VerificationResult {
        if self.backends.is_empty() {
            return no_backend_result();
        }

        let cancelled = Arc::new(AtomicBool::new(false));
        let (tx, rx) = mpsc::channel();

        let mut handles = Vec::with_capacity(self.backends.len());
        for backend in &self.backends {
            let backend = Arc::clone(backend);
            let vc = vc.clone();
            let cancelled = Arc::clone(&cancelled);
            let tx = tx.clone();

            handles.push(thread::spawn(move || {
                if cancelled.load(Ordering::Relaxed) {
                    return;
                }
                let result = backend.verify(&vc);
                let _ = tx.send(result);
            }));
        }
        drop(tx);

        let mut best: Option<VerificationResult> = None;
        for result in rx {
            let is_conclusive = result.is_proved() || result.is_failed();
            if is_conclusive {
                cancelled.store(true, Ordering::Relaxed);
                best = Some(result);
                break;
            }
            if best.is_none() {
                best = Some(result);
            }
        }

        for handle in handles {
            let _ = handle.join();
        }

        best.unwrap_or_else(no_backend_result)
    }

    /// tRust: Cascade mode — try backends in order, stop on conclusive result.
    fn verify_cascade(&self, vc: &VerificationCondition) -> VerificationResult {
        let mut last_result: Option<VerificationResult> = None;

        for backend in &self.backends {
            if !backend.can_handle(vc) {
                continue;
            }
            let result = backend.verify(vc);
            let is_conclusive = result.is_proved() || result.is_failed();
            if is_conclusive {
                return result;
            }
            if last_result.is_none() {
                last_result = Some(result);
            }
        }

        last_result.unwrap_or_else(no_backend_result)
    }

    /// tRust: Selective mode — pick the best backend for this VC's kind.
    ///
    /// Uses the router's `BackendRole` preference ranking via
    /// `crate::select_backend`.
    fn verify_selective(&self, vc: &VerificationCondition) -> VerificationResult {
        if let Some(backend) = crate::select_backend(&self.backends, vc) {
            return backend.verify(vc);
        }
        no_backend_result()
    }
}
