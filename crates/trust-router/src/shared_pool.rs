// trust-router/shared_pool.rs: Shared rayon thread pool for verification pipeline
//
// tRust #676: Creates a single rayon ThreadPool at pipeline startup and reuses
// it across dispatch_parallel() and PortfolioRacer::race() via pool.install().
// Eliminates per-invocation pool creation overhead (0.5-2ms each).
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::sync::Arc;

/// tRust #676: Create a shared rayon thread pool for reuse across the
/// verification pipeline.
///
/// Returns an `Arc<rayon::ThreadPool>` that can be passed to
/// `ParallelDispatchConfig::with_pool()` and `PortfolioRacer::with_pool()`.
/// Rayon's `pool.install()` is designed for this pattern: work submitted
/// via `install()` runs on the pool's threads using work-stealing.
///
/// # Arguments
/// * `num_threads` - Number of threads in the pool. Clamped to at least 1.
///
/// # Panics
/// Panics if rayon fails to create the thread pool (should not happen with
/// valid thread count).
#[must_use]
pub fn create_shared_pool(num_threads: usize) -> Arc<rayon::ThreadPool> {
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(num_threads.max(1))
        .build()
        // tRust #734: rayon pool creation failure is a real system-level error.
        .expect("rayon thread pool creation failed");
    Arc::new(pool)
}

/// tRust #676: Create a shared rayon thread pool sized from environment.
///
/// Reads `TRUST_THREADS` environment variable for thread count. Falls back
/// to the number of available CPUs if the variable is unset or invalid.
#[must_use]
pub fn create_default_shared_pool() -> Arc<rayon::ThreadPool> {
    let num_threads = thread_count_from_env();
    create_shared_pool(num_threads)
}

/// tRust #676: Read thread count from `TRUST_THREADS` env var.
///
/// Returns the parsed value if set and valid (>= 1), otherwise returns
/// the number of available CPUs (or 4 if that cannot be determined).
#[must_use]
pub fn thread_count_from_env() -> usize {
    if let Ok(val) = std::env::var("TRUST_THREADS")
        && let Ok(n) = val.parse::<usize>()
            && n >= 1 {
                return n;
            }
    std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(4)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_create_shared_pool() {
        let pool = create_shared_pool(2);
        assert_eq!(pool.current_num_threads(), 2);
    }

    #[test]
    fn test_create_shared_pool_clamps_to_one() {
        let pool = create_shared_pool(0);
        assert_eq!(pool.current_num_threads(), 1);
    }

    #[test]
    fn test_create_default_shared_pool() {
        let pool = create_default_shared_pool();
        assert!(pool.current_num_threads() >= 1);
    }

    #[test]
    fn test_shared_pool_can_execute_work() {
        use rayon::prelude::*;

        let pool = create_shared_pool(2);
        let result: Vec<i32> = pool.install(|| {
            (0..10).into_par_iter().map(|x| x * 2).collect()
        });
        assert_eq!(result.len(), 10);
        assert_eq!(result[5], 10);
    }

    #[test]
    fn test_shared_pool_arc_cloning() {
        let pool = create_shared_pool(2);
        let pool2 = Arc::clone(&pool);
        // Both references point to the same pool.
        assert_eq!(pool.current_num_threads(), pool2.current_num_threads());
    }

    #[test]
    fn test_thread_count_from_env_default() {
        // When TRUST_THREADS is not set, should return available parallelism.
        // We can't guarantee the exact value, but it should be >= 1.
        let count = thread_count_from_env();
        assert!(count >= 1);
    }
}
