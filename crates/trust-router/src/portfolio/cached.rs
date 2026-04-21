// trust-router/portfolio/cached.rs: CachedPortfolioRacer and TimeoutFallbackChain
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex, mpsc};
use std::thread;
use std::time::{Duration, Instant};

use trust_types::{VerificationCondition, VerificationResult};

use crate::VerificationBackend;
use crate::query_cache::QueryCache;

use super::types::no_backend_result;

/// tRust: Configuration for a single backend in a portfolio race.
///
/// Each backend has a name (for diagnostics) and a per-solver timeout.
/// The timeout is enforced cooperatively: the racing thread checks an
/// `AtomicBool` cancellation flag after the solver returns, and the
/// overall timeout thread sets the flag if the deadline expires.
#[derive(Debug, Clone)]
pub struct BackendConfig {
    /// Human-readable backend name (e.g., "z4", "zani", "lean5").
    pub name: String,
    /// Per-solver timeout in milliseconds. 0 means no per-solver timeout
    /// (the solver runs until the overall timeout or completion).
    pub timeout_ms: u64,
}

impl BackendConfig {
    /// Create a new backend config.
    #[must_use]
    pub fn new(name: impl Into<String>, timeout_ms: u64) -> Self {
        Self { name: name.into(), timeout_ms }
    }
}

/// tRust: Portfolio racer with per-solver timeouts, overall timeout,
/// cancellation via `AtomicBool`, and result caching via `QueryCache`.
///
/// Spawns one `std::thread` per backend. The first successful (Proved or
/// Disproved) result wins; remaining threads are signalled to cancel.
/// An overall timeout kills all tasks if none complete in time.
///
/// Before racing, checks `QueryCache` for a cached result. After a race
/// produces a definitive result, inserts it into the cache.
pub struct CachedPortfolioRacer {
    /// Backend configs paired with their implementations.
    backends: Vec<(BackendConfig, Arc<dyn VerificationBackend>)>,
    /// Overall timeout in milliseconds. 0 means no overall timeout.
    overall_timeout_ms: u64,
    /// Shared query cache (wrapped in Mutex for thread safety).
    cache: Arc<Mutex<QueryCache>>,
}

impl CachedPortfolioRacer {
    /// Create a new cached portfolio racer.
    #[must_use]
    pub fn new(
        backends: Vec<(BackendConfig, Arc<dyn VerificationBackend>)>,
        overall_timeout_ms: u64,
        cache: Arc<Mutex<QueryCache>>,
    ) -> Self {
        Self { backends, overall_timeout_ms, cache }
    }

    /// Number of configured backends.
    #[must_use]
    pub fn backend_count(&self) -> usize {
        self.backends.len()
    }

    /// Race all backends on a single VC, returning the best result.
    ///
    /// 1. Check cache — return immediately on hit.
    /// 2. Spawn threads for each backend with per-solver timeout.
    /// 3. Spawn overall timeout watchdog thread.
    /// 4. First definitive result wins, cancels others.
    /// 5. Insert definitive results into cache.
    #[must_use]
    pub fn race(&self, vc: &VerificationCondition) -> VerificationResult {
        // tRust: Step 1 — check cache before racing.
        if let Ok(mut cache) = self.cache.lock()
            && let crate::query_cache::CacheLookupResult::Hit(result) = cache.lookup(&vc.formula) {
                return result;
            }

        if self.backends.is_empty() {
            return no_backend_result();
        }

        let cancelled = Arc::new(AtomicBool::new(false));
        let (tx, rx) = mpsc::channel();
        let mut handles = Vec::with_capacity(self.backends.len());

        // tRust: Step 2 — spawn one thread per backend.
        for (config, backend) in &self.backends {
            let backend = Arc::clone(backend);
            let vc = vc.clone();
            let cancelled = Arc::clone(&cancelled);
            let tx = tx.clone();
            let solver_timeout = if config.timeout_ms > 0 {
                Some(Duration::from_millis(config.timeout_ms))
            } else {
                None
            };
            let solver_name = config.name.clone();

            handles.push(thread::spawn(move || {
                if cancelled.load(Ordering::Relaxed) {
                    return;
                }

                let start = Instant::now();

                // tRust: Per-solver timeout via a watchdog thread that sets
                // a local cancel flag. The solver itself is not interrupted
                // (cooperative cancellation), but the result is discarded
                // if the timeout fires before the solver returns.
                let timed_out = Arc::new(AtomicBool::new(false));
                let _watchdog = if let Some(timeout) = solver_timeout {
                    let timed_out_clone = Arc::clone(&timed_out);
                    Some(thread::spawn(move || {
                        thread::sleep(timeout);
                        timed_out_clone.store(true, Ordering::Relaxed);
                    }))
                } else {
                    None
                };

                let result = backend.verify(&vc);
                let elapsed = start.elapsed().as_millis() as u64;

                // If this solver's timeout expired, report Timeout instead.
                if timed_out.load(Ordering::Relaxed) {
                    let _ = tx.send(VerificationResult::Timeout {
                        solver: solver_name,
                        timeout_ms: elapsed,
                    });
                } else {
                    let _ = tx.send(result);
                }
            }));
        }

        // tRust: Step 3 — overall timeout watchdog.
        let overall_cancelled = Arc::clone(&cancelled);
        let overall_timeout = self.overall_timeout_ms;
        let _overall_watchdog = if overall_timeout > 0 {
            Some(thread::spawn(move || {
                thread::sleep(Duration::from_millis(overall_timeout));
                overall_cancelled.store(true, Ordering::Relaxed);
            }))
        } else {
            None
        };

        // Drop our sender so the channel closes when all threads finish.
        drop(tx);

        // tRust: Step 4 — collect results, first definitive wins.
        let mut best: Option<VerificationResult> = None;

        for result in rx {
            let is_definitive = result.is_proved() || result.is_failed();

            if is_definitive {
                cancelled.store(true, Ordering::Relaxed);
                best = Some(result);
                break;
            }

            if best.is_none() {
                best = Some(result);
            }
        }

        // Join all solver threads to avoid resource leaks.
        for handle in handles {
            let _ = handle.join();
        }

        let result = best.unwrap_or_else(|| {
            if overall_timeout > 0 {
                VerificationResult::Unknown {
                    solver: "portfolio".to_string(),
                    time_ms: overall_timeout,
                    reason: "all solvers timed out".to_string(),
                }
            } else {
                no_backend_result()
            }
        });

        // tRust: Step 5 — cache definitive results.
        if (result.is_proved() || result.is_failed())
            && let Ok(mut cache) = self.cache.lock() {
                cache.store(&vc.formula, result.clone());
            }

        result
    }
}

/// tRust: Sequential fallback chain with per-solver timeouts.
///
/// Tries backends in order (e.g., z4 -> zani -> lean5). Moves to the next
/// backend only on timeout or Unknown result. Returns the first definitive
/// result (Proved or Disproved).
pub struct TimeoutFallbackChain {
    /// Ordered backends with their configs.
    backends: Vec<(BackendConfig, Arc<dyn VerificationBackend>)>,
    /// Shared query cache.
    cache: Arc<Mutex<QueryCache>>,
}

impl TimeoutFallbackChain {
    /// Create a new timeout fallback chain.
    #[must_use]
    pub fn new(
        backends: Vec<(BackendConfig, Arc<dyn VerificationBackend>)>,
        cache: Arc<Mutex<QueryCache>>,
    ) -> Self {
        Self { backends, cache }
    }

    /// Execute the fallback chain on a VC.
    ///
    /// Checks cache first. Tries each backend sequentially. A backend that
    /// returns Proved or Disproved stops the chain. Timeout or Unknown moves
    /// to the next backend. The result is cached on success.
    #[must_use]
    pub fn execute(&self, vc: &VerificationCondition) -> VerificationResult {
        // tRust: Check cache before trying any backend.
        if let Ok(mut cache) = self.cache.lock()
            && let crate::query_cache::CacheLookupResult::Hit(result) = cache.lookup(&vc.formula) {
                return result;
            }

        let mut last_result: Option<VerificationResult> = None;

        for (config, backend) in &self.backends {
            let timeout = if config.timeout_ms > 0 {
                Some(Duration::from_millis(config.timeout_ms))
            } else {
                None
            };

            // tRust: Run the solver in a thread so we can enforce timeout.
            // A cancellation flag prevents the thread from doing further work
            // after a timeout (#425).
            let backend = Arc::clone(backend);
            let vc_clone = vc.clone();
            let solver_name = config.name.clone();
            let cancelled = Arc::new(AtomicBool::new(false));
            let cancelled_clone = Arc::clone(&cancelled);

            let (tx, rx) = mpsc::channel();
            let handle = thread::spawn(move || {
                if cancelled_clone.load(Ordering::Relaxed) {
                    return;
                }
                let result = backend.verify(&vc_clone);
                // tRust: Only send the result if we haven't been cancelled.
                if !cancelled_clone.load(Ordering::Relaxed) {
                    let _ = tx.send(result);
                }
            });

            let result = if let Some(timeout_dur) = timeout {
                match rx.recv_timeout(timeout_dur) {
                    Ok(r) => r,
                    Err(_) => {
                        // tRust #425: Signal cancellation before detaching.
                        // This prevents the thread from sending stale results
                        // and marks it for early exit if it hasn't started yet.
                        cancelled.store(true, Ordering::Relaxed);
                        drop(handle);
                        let timeout_result = VerificationResult::Timeout {
                            solver: solver_name.clone(),
                            timeout_ms: config.timeout_ms,
                        };
                        last_result = Some(timeout_result);
                        continue;
                    }
                }
            } else {
                rx.recv().unwrap_or_else(|_| VerificationResult::Unknown {
                    solver: solver_name.clone(),
                    time_ms: 0,
                    reason: "solver thread panicked".to_string(),
                })
            };

            let _ = handle.join();

            let is_definitive = result.is_proved() || result.is_failed();
            if is_definitive {
                // Cache and return.
                if let Ok(mut cache) = self.cache.lock() {
                    cache.store(&vc.formula, result.clone());
                }
                return result;
            }

            // Timeout or Unknown — continue to next backend.
            last_result = Some(result);
        }

        last_result.unwrap_or_else(no_backend_result)
    }
}
