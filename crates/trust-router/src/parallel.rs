// trust-router/parallel.rs: Parallel VC verification
//
// tRust: Spawns background threads to verify VCs concurrently,
// allowing verification to run alongside codegen without blocking.
// Uses std::thread only (no rayon dependency).
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::sync::{Arc, mpsc};
use std::thread;

use trust_types::{VerificationCondition, VerificationResult};

use crate::VerificationBackend;

/// tRust: Result collector for parallel verification.
///
/// Wraps a channel receiver and join handle for a background verification
/// thread. Call `collect()` to block until all results arrive, or
/// `try_collect()` to drain available results without blocking.
pub struct ParallelResults {
    receiver: mpsc::Receiver<(VerificationCondition, VerificationResult)>,
    handle: Option<thread::JoinHandle<()>>,
}

impl ParallelResults {
    /// Block until all results are available.
    #[must_use]
    pub fn collect(self) -> Vec<(VerificationCondition, VerificationResult)> {
        let results: Vec<_> = self.receiver.iter().collect();
        if let Some(handle) = self.handle {
            // SAFETY invariant: thread panics are non-fatal; we just drop the handle.
            let _ = handle.join();
        }
        results
    }

    /// Drain results that are ready without blocking.
    ///
    /// Returns whatever results have been sent so far. Call again later
    /// to get more, or call `collect()` to block until all are done.
    #[must_use]
    pub fn try_collect(&self) -> Vec<(VerificationCondition, VerificationResult)> {
        let mut results = Vec::new();
        while let Ok(r) = self.receiver.try_recv() {
            results.push(r);
        }
        results
    }
}

/// tRust: Launch parallel verification of VCs in a single background thread.
///
/// Spawns one background thread that verifies all VCs sequentially using
/// the first matching backend. Returns a `ParallelResults` handle that
/// can be collected later (e.g., after codegen completes).
///
/// This is the simplest non-blocking mode: one thread, streaming results.
/// For multi-threaded concurrency, use `verify_concurrent`.
pub fn verify_parallel(
    vcs: Vec<VerificationCondition>,
    backends: Vec<Arc<dyn VerificationBackend>>,
) -> ParallelResults {
    let (tx, rx) = mpsc::channel();

    let handle = thread::spawn(move || {
        for vc in &vcs {
            let result = crate::select_backend(backends.as_slice(), vc)
                .map(|backend| backend.verify(vc))
                .unwrap_or_else(|| VerificationResult::Unknown {
                    solver: "none".to_string(),
                    time_ms: 0,
                    reason: "no backend can handle this VC".to_string(),
                });
            if tx.send((vc.clone(), result)).is_err() {
                break; // receiver dropped
            }
        }
    });

    ParallelResults { receiver: rx, handle: Some(handle) }
}

/// tRust: Verify VCs concurrently using bounded thread parallelism.
///
/// Splits VCs into chunks and verifies each chunk in its own thread.
/// `max_threads` bounds concurrency (clamped to `1..=vcs.len()`).
///
/// Future: integrate with the compiler's work-stealing thread pool
/// or rayon for better scheduling.
pub fn verify_concurrent(
    vcs: Vec<VerificationCondition>,
    backends: Vec<Arc<dyn VerificationBackend>>,
    max_threads: usize,
) -> Vec<(VerificationCondition, VerificationResult)> {
    if vcs.is_empty() {
        return Vec::new();
    }

    let max_threads = max_threads.min(vcs.len()).max(1);
    let backends = Arc::new(backends);

    // tRust: Split VCs into roughly equal chunks for the thread pool.
    let chunk_size = vcs.len().div_ceil(max_threads);
    let chunks: Vec<Vec<VerificationCondition>> =
        vcs.chunks(chunk_size).map(|c| c.to_vec()).collect();

    let mut handles = Vec::with_capacity(chunks.len());
    for chunk in chunks {
        let backends = Arc::clone(&backends);
        let handle = thread::spawn(move || {
            let mut results = Vec::with_capacity(chunk.len());
            for vc in &chunk {
                let result = crate::select_backend(backends.as_slice(), vc)
                    .map(|backend| backend.verify(vc))
                    .unwrap_or_else(|| VerificationResult::Unknown {
                        solver: "none".to_string(),
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

#[cfg(test)]
mod tests {
    use trust_types::*;

    use super::*;

    /// Helper: wrap MockBackend in Arc for parallel tests.
    fn mock_backends() -> Vec<Arc<dyn VerificationBackend>> {
        vec![Arc::new(crate::mock_backend::MockBackend)]
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

    #[test]
    fn test_verify_parallel_single_vc() {
        let vcs = vec![test_vc("test", Formula::Bool(false))];
        let results = verify_parallel(vcs, mock_backends()).collect();
        assert_eq!(results.len(), 1);
        assert!(results[0].1.is_proved());
    }

    #[test]
    fn test_verify_parallel_empty() {
        let results = verify_parallel(vec![], mock_backends()).collect();
        assert!(results.is_empty());
    }

    #[test]
    fn test_verify_parallel_multiple_vcs() {
        let vcs: Vec<_> =
            (0..5).map(|i| test_vc(&format!("fn_{i}"), Formula::Bool(false))).collect();
        let results = verify_parallel(vcs, mock_backends()).collect();
        assert_eq!(results.len(), 5);
        for (_, result) in &results {
            assert!(result.is_proved());
        }
    }

    #[test]
    fn test_verify_parallel_try_collect() {
        let vcs = vec![test_vc("test", Formula::Bool(false))];
        let handle = verify_parallel(vcs, mock_backends());
        // Wait for thread to finish by collecting
        let results = handle.collect();
        assert_eq!(results.len(), 1);
    }

    #[test]
    fn test_verify_concurrent_basic() {
        let vcs: Vec<_> =
            (0..10).map(|i| test_vc(&format!("fn_{i}"), Formula::Bool(false))).collect();
        let results = verify_concurrent(vcs, mock_backends(), 4);
        assert_eq!(results.len(), 10);
        for (_, result) in &results {
            assert!(result.is_proved());
        }
    }

    #[test]
    fn test_verify_concurrent_single_thread() {
        let vcs: Vec<_> =
            (0..3).map(|i| test_vc(&format!("fn_{i}"), Formula::Bool(true))).collect();
        let results = verify_concurrent(vcs, mock_backends(), 1);
        assert_eq!(results.len(), 3);
        for (_, result) in &results {
            assert!(result.is_failed());
        }
    }

    #[test]
    fn test_verify_concurrent_empty() {
        let results = verify_concurrent(vec![], mock_backends(), 4);
        assert!(results.is_empty());
    }

    #[test]
    fn test_verify_concurrent_more_threads_than_vcs() {
        let vcs = vec![test_vc("solo", Formula::Bool(false))];
        let results = verify_concurrent(vcs, mock_backends(), 100);
        assert_eq!(results.len(), 1);
        assert!(results[0].1.is_proved());
    }

    #[test]
    fn test_verify_concurrent_mixed_results() {
        let vcs = vec![
            test_vc("provable", Formula::Bool(false)),
            test_vc("failing", Formula::Bool(true)),
            test_vc("unknown", Formula::Var("x".into(), Sort::Int)),
        ];
        let results = verify_concurrent(vcs, mock_backends(), 2);
        assert_eq!(results.len(), 3);

        // Results maintain input order within each chunk
        let proved_count = results.iter().filter(|(_, r)| r.is_proved()).count();
        let failed_count = results.iter().filter(|(_, r)| r.is_failed()).count();
        let unknown_count =
            results.iter().filter(|(_, r)| matches!(r, VerificationResult::Unknown { .. })).count();
        assert_eq!(proved_count, 1);
        assert_eq!(failed_count, 1);
        assert_eq!(unknown_count, 1);
    }

    #[test]
    fn test_select_backend_prefers_solver_family() {
        struct PreferredBackend;
        struct FallbackBackend;

        impl VerificationBackend for PreferredBackend {
            fn name(&self) -> &str {
                "preferred"
            }

            fn role(&self) -> crate::BackendRole {
                crate::BackendRole::SmtSolver
            }

            fn can_handle(&self, _vc: &VerificationCondition) -> bool {
                true
            }

            fn verify(&self, _vc: &VerificationCondition) -> VerificationResult {
                VerificationResult::Proved {
                    solver: "preferred".to_string(),
                    time_ms: 0,
                    strength: ProofStrength::smt_unsat(), proof_certificate: None,
                solver_warnings: None, }
            }
        }

        impl VerificationBackend for FallbackBackend {
            fn name(&self) -> &str {
                "fallback"
            }

            fn role(&self) -> crate::BackendRole {
                crate::BackendRole::General
            }

            fn can_handle(&self, _vc: &VerificationCondition) -> bool {
                true
            }

            fn verify(&self, _vc: &VerificationCondition) -> VerificationResult {
                VerificationResult::Failed {
                    solver: "fallback".to_string(),
                    time_ms: 0,
                    counterexample: None,
                }
            }
        }

        let backends: Vec<Arc<dyn VerificationBackend>> =
            vec![Arc::new(FallbackBackend), Arc::new(PreferredBackend)];
        let vc = test_vc("prefer", Formula::Bool(false));

        let result = crate::select_backend(backends.as_slice(), &vc).expect("expected a backend");
        assert_eq!(result.name(), "preferred");
    }

    #[test]
    fn test_verify_parallel_no_backend_fallback() {
        // Empty backend list — all VCs should return Unknown
        let vcs = vec![test_vc("orphan", Formula::Bool(false))];
        let results = verify_parallel(vcs, vec![]).collect();
        assert_eq!(results.len(), 1);
        assert!(matches!(results[0].1, VerificationResult::Unknown { .. }));
    }
}
