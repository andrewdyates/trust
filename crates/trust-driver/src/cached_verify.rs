// trust-driver/cached_verify.rs: Incremental verification wrapper
//
// Wraps a VerifyPhase to skip re-verification of unchanged functions.
// Uses IncrementalCache to track content hashes and cached outcomes.
// Persists cache to .trust-cache/ directory between runs.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;
use std::path::{Path, PathBuf};
use std::sync::Mutex;
use std::time::{Duration, Instant};

use crate::incremental::{
    CachedVerificationOutcome, ContentHash, IncrementalState,
    compute_function_hash,
};
use crate::{ProofFrontier, VerifyOutput, VerifyPhase};

// ---------------------------------------------------------------------------
// Cache directory conventions
// ---------------------------------------------------------------------------

/// Default cache directory name, relative to the project root.
const CACHE_DIR: &str = ".trust-cache";
/// File within the cache directory for the incremental state.
const STATE_FILE: &str = "incremental_state.txt";

// ---------------------------------------------------------------------------
// CacheConfig
// ---------------------------------------------------------------------------

/// Configuration for the incremental verification cache.
#[derive(Debug, Clone)]
pub(crate) struct CacheConfig {
    /// Whether caching is enabled. When false, every function is re-verified.
    pub enabled: bool,
    /// Directory to persist the cache. Defaults to `.trust-cache/` in the
    /// project root.
    pub cache_dir: PathBuf,
}

impl Default for CacheConfig {
    fn default() -> Self {
        Self {
            enabled: true,
            cache_dir: PathBuf::from(CACHE_DIR),
        }
    }
}

impl CacheConfig {
    /// Create a config with caching disabled (equivalent to `--no-cache`).
    #[must_use]
    pub(crate) fn disabled() -> Self {
        Self {
            enabled: false,
            ..Self::default()
        }
    }

    /// Path to the state file within the cache directory.
    #[must_use]
    pub(crate) fn state_file_path(&self) -> PathBuf {
        self.cache_dir.join(STATE_FILE)
    }
}

// ---------------------------------------------------------------------------
// CacheStats
// ---------------------------------------------------------------------------

/// Statistics about cache usage during a verification run.
#[derive(Debug, Clone, Default)]
pub(crate) struct CacheStats {
    /// Number of functions that hit the cache (skipped verification).
    pub hits: usize,
    /// Number of functions that missed the cache (re-verified).
    pub misses: usize,
    /// Total time saved by cache hits (estimated from cached elapsed times).
    pub time_saved: Duration,
}

impl CacheStats {
    /// Total functions processed (hits + misses).
    #[must_use]
    pub(crate) fn total(&self) -> usize {
        self.hits + self.misses
    }

    /// Cache hit rate as a fraction in [0.0, 1.0].
    #[must_use]
    pub(crate) fn hit_rate(&self) -> f64 {
        let total = self.total();
        if total == 0 {
            return 0.0;
        }
        self.hits as f64 / total as f64
    }
}

// ---------------------------------------------------------------------------
// CachedVerifyPhase
// ---------------------------------------------------------------------------

/// A `VerifyPhase` wrapper that skips re-verification of unchanged functions.
///
/// On each `verify()` call:
/// 1. Computes a content hash of the source file.
/// 2. Checks the `IncrementalCache` for a matching entry.
/// 3. On cache hit: returns a synthetic `VerifyOutput` from the cached outcome.
/// 4. On cache miss: delegates to the inner `VerifyPhase`, then caches the result.
///
/// The cache state can be persisted to disk between runs via `save()` / `load()`.
pub(crate) struct CachedVerifyPhase<'a> {
    inner: &'a dyn VerifyPhase,
    state: Mutex<IncrementalState>,
    config: CacheConfig,
    stats: Mutex<CacheStats>,
}

impl<'a> CachedVerifyPhase<'a> {
    /// Create a new cached verify phase wrapping the given inner phase.
    #[must_use]
    pub(crate) fn new(inner: &'a dyn VerifyPhase, config: CacheConfig) -> Self {
        let state = if config.enabled {
            load_state_from_disk(&config).unwrap_or_default()
        } else {
            IncrementalState::new()
        };

        Self {
            inner,
            state: Mutex::new(state),
            config,
            stats: Mutex::new(CacheStats::default()),
        }
    }

    /// Create with an explicit pre-loaded state (useful for testing).
    #[must_use]
    pub(crate) fn with_state(
        inner: &'a dyn VerifyPhase,
        config: CacheConfig,
        state: IncrementalState,
    ) -> Self {
        Self {
            inner,
            state: Mutex::new(state),
            config,
            stats: Mutex::new(CacheStats::default()),
        }
    }

    /// Return a snapshot of cache statistics.
    #[must_use]
    pub(crate) fn stats(&self) -> CacheStats {
        // SAFETY: mutex poisoning means a thread panicked while holding the lock;
        // propagating the panic is the correct behavior for this invariant violation.
        self.stats.lock().expect("stats mutex poisoned").clone()
    }

    /// Persist the current cache state to disk.
    ///
    /// Creates the cache directory if it does not exist. Returns an error
    /// if the write fails.
    pub(crate) fn save(&self) -> Result<(), crate::incremental::IncrementalError> {
        if !self.config.enabled {
            return Ok(());
        }
        let state = self.state.lock().expect("state mutex poisoned");
        let path = self.config.state_file_path();
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent)
                .map_err(crate::incremental::IncrementalError::Io)?;
        }
        state.save_state(&path)
    }

    /// Return a snapshot of the current incremental state.
    #[must_use]
    pub(crate) fn incremental_state(&self) -> IncrementalState {
        self.state.lock().expect("state mutex poisoned").clone()
    }

    /// Return the current content hashes tracked by the cache.
    #[must_use]
    pub(crate) fn cached_function_count(&self) -> usize {
        self.state.lock().expect("state mutex poisoned").cache.len()
    }

    /// Compute the content hash for a source file.
    ///
    /// Uses the file contents as the body and an empty spec (specs will be
    /// extracted in a future iteration; for now, file content is sufficient
    /// for change detection).
    fn compute_source_hash(source_path: &Path) -> Option<ContentHash> {
        let body = std::fs::read(source_path).ok()?;
        Some(compute_function_hash(&body, b""))
    }

    /// Build a `VerifyOutput` from a cached result.
    ///
    // tRust: F13 fix -- uses stored frontier counts when available, falling
    // back to synthetic single-VC output for legacy cache entries.
    fn output_from_cached(cached: &crate::incremental::CachedResult) -> VerifyOutput {
        if let Some(ref frontier) = cached.frontier {
            // Full-fidelity cache hit: restore exact counts.
            return VerifyOutput {
                frontier: frontier.clone(),
                fingerprint: Some("cached".to_string()),
                vcs_dispatched: cached.vcs_dispatched,
                vcs_failed: cached.vcs_failed,
                detailed_results: None,
            };
        }

        // Legacy fallback: no stored frontier, synthesize from outcome.
        match cached.result {
            CachedVerificationOutcome::Proved => VerifyOutput {
                frontier: ProofFrontier {
                    trusted: 1,
                    certified: 0,
                    runtime_checked: 0,
                    failed: 0,
                    unknown: 0,
                },
                fingerprint: Some("cached".to_string()),
                vcs_dispatched: 1,
                vcs_failed: 0,
                detailed_results: None,
            },
            CachedVerificationOutcome::Failed => VerifyOutput {
                frontier: ProofFrontier {
                    trusted: 0,
                    certified: 0,
                    runtime_checked: 0,
                    failed: 1,
                    unknown: 0,
                },
                fingerprint: Some("cached".to_string()),
                vcs_dispatched: 1,
                vcs_failed: 1,
                detailed_results: None,
            },
            CachedVerificationOutcome::Unknown | CachedVerificationOutcome::Timeout => {
                VerifyOutput {
                    frontier: ProofFrontier {
                        trusted: 0,
                        certified: 0,
                        runtime_checked: 0,
                        failed: 0,
                        unknown: 1,
                    },
                    fingerprint: Some("cached".to_string()),
                    vcs_dispatched: 1,
                    vcs_failed: 0,
                    detailed_results: None,
                }
            }
        }
    }

    /// Convert a `VerifyOutput` to a `CachedVerificationOutcome` for storage.
    fn outcome_from_output(output: &VerifyOutput) -> CachedVerificationOutcome {
        if output.vcs_failed == 0 && output.vcs_dispatched > 0 {
            CachedVerificationOutcome::Proved
        } else if output.vcs_failed > 0 {
            CachedVerificationOutcome::Failed
        } else {
            CachedVerificationOutcome::Unknown
        }
    }
}

impl VerifyPhase for CachedVerifyPhase<'_> {
    fn verify(&self, source_path: &Path) -> VerifyOutput {
        // If caching is disabled, delegate directly.
        if !self.config.enabled {
            return self.inner.verify(source_path);
        }

        // Compute content hash for the source.
        let hash = match Self::compute_source_hash(source_path) {
            Some(h) => h,
            None => {
                // Cannot read source file — fall through to inner verify.
                return self.inner.verify(source_path);
            }
        };

        let source_key = source_path.to_string_lossy().to_string();

        // Check cache under lock.
        {
            let state = self.state.lock().expect("state mutex poisoned");
            if !state.should_reverify(&source_key, &hash) {
                // tRust: F13 fix -- pass full CachedResult so frontier is restored.
                if let Some(cached) = state.cache.get(&source_key) {
                    let mut stats = self.stats.lock().expect("stats mutex poisoned");
                    stats.hits += 1;
                    stats.time_saved += cached.elapsed;
                    return Self::output_from_cached(cached);
                }
            }
        }

        // Cache miss: run verification.
        let start = Instant::now();
        let output = self.inner.verify(source_path);
        let elapsed = start.elapsed();

        // tRust: F13 fix -- store frontier counts alongside outcome.
        let outcome = Self::outcome_from_output(&output);
        {
            let mut state = self.state.lock().expect("state mutex poisoned");
            state.cache.mark_verified_with_frontier(
                &source_key,
                hash,
                outcome,
                elapsed,
                output.frontier.clone(),
                output.vcs_dispatched,
                output.vcs_failed,
            );
        }

        {
            let mut stats = self.stats.lock().expect("stats mutex poisoned");
            stats.misses += 1;
        }

        output
    }
}

// ---------------------------------------------------------------------------
// Persistence helpers
// ---------------------------------------------------------------------------

/// Attempt to load incremental state from the cache directory.
///
/// Returns `None` if the file does not exist or cannot be parsed.
fn load_state_from_disk(config: &CacheConfig) -> Option<IncrementalState> {
    let path = config.state_file_path();
    if !path.exists() {
        return None;
    }
    IncrementalState::load_state(&path).ok()
}

/// Compute content hashes for all source files in a directory.
///
/// Walks the directory tree and hashes each `.rs` file. Returns a map from
/// file path to content hash. Useful for building the `current_hashes` map
/// needed by `IncrementalCache::stale_results`.
#[must_use]
pub(crate) fn hash_source_files(dir: &Path) -> FxHashMap<String, ContentHash> {
    let mut hashes = FxHashMap::default();
    if let Ok(entries) = walk_rs_files(dir) {
        for entry in entries {
            if let Ok(body) = std::fs::read(&entry) {
                let hash = compute_function_hash(&body, b"");
                hashes.insert(entry.to_string_lossy().to_string(), hash);
            }
        }
    }
    hashes
}

/// Recursively find all `.rs` files under a directory.
fn walk_rs_files(dir: &Path) -> std::io::Result<Vec<PathBuf>> {
    let mut files = Vec::new();
    if dir.is_dir() {
        for entry in std::fs::read_dir(dir)? {
            let entry = entry?;
            let path = entry.path();
            if path.is_dir() {
                files.extend(walk_rs_files(&path)?);
            } else if path.extension().is_some_and(|ext| ext == "rs") {
                files.push(path);
            }
        }
    }
    Ok(files)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::Cell;

    // -- Mock verify phase that counts calls --

    struct CountingVerify {
        call_count: Cell<usize>,
        output: VerifyOutput,
    }

    impl CountingVerify {
        fn new(output: VerifyOutput) -> Self {
            Self {
                call_count: Cell::new(0),
                output,
            }
        }

        fn calls(&self) -> usize {
            self.call_count.get()
        }
    }

    impl VerifyPhase for CountingVerify {
        fn verify(&self, _: &Path) -> VerifyOutput {
            self.call_count.set(self.call_count.get() + 1);
            self.output.clone()
        }
    }

    fn proved_output() -> VerifyOutput {
        VerifyOutput {
            frontier: ProofFrontier {
                trusted: 3,
                certified: 0,
                runtime_checked: 0,
                failed: 0,
                unknown: 0,
            },
            fingerprint: None,
            vcs_dispatched: 3,
            vcs_failed: 0,
            detailed_results: None,
        }
    }

    fn failed_output() -> VerifyOutput {
        VerifyOutput {
            frontier: ProofFrontier {
                trusted: 1,
                certified: 0,
                runtime_checked: 0,
                failed: 2,
                unknown: 0,
            },
            fingerprint: None,
            vcs_dispatched: 3,
            vcs_failed: 2,
            detailed_results: None,
        }
    }

    // -- Test: cache miss on first call, cache hit on second call --

    #[test]
    fn test_cache_miss_then_hit() {
        let tmp = tempfile::TempDir::new().expect("create temp dir");
        let source = tmp.path().join("test.rs");
        std::fs::write(&source, "fn main() { 1 + 1 }").expect("write source");

        let inner = CountingVerify::new(proved_output());
        let config = CacheConfig {
            enabled: true,
            cache_dir: tmp.path().join(".trust-cache"),
        };
        let cached = CachedVerifyPhase::new(&inner, config);

        // First call: cache miss, delegates to inner.
        let out1 = cached.verify(&source);
        assert_eq!(inner.calls(), 1);
        assert_eq!(out1.frontier.trusted, 3);

        // Second call: same file, cache hit, skips inner.
        // tRust: F13 fix -- cache now preserves full frontier counts.
        let out2 = cached.verify(&source);
        assert_eq!(inner.calls(), 1); // NOT incremented
        assert_eq!(out2.frontier.trusted, 3); // F13 fix: preserved from original output
        assert_eq!(out2.vcs_dispatched, 3); // F13 fix: preserved VC count
        assert_eq!(out2.fingerprint, Some("cached".to_string()));

        let stats = cached.stats();
        assert_eq!(stats.hits, 1);
        assert_eq!(stats.misses, 1);
        assert!(stats.hit_rate() > 0.4);
    }

    // -- Test: file change invalidates cache --

    #[test]
    fn test_file_change_invalidates_cache() {
        let tmp = tempfile::TempDir::new().expect("create temp dir");
        let source = tmp.path().join("test.rs");
        std::fs::write(&source, "fn main() { 1 + 1 }").expect("write v1");

        let inner = CountingVerify::new(proved_output());
        let config = CacheConfig {
            enabled: true,
            cache_dir: tmp.path().join(".trust-cache"),
        };
        let cached = CachedVerifyPhase::new(&inner, config);

        // First call: cache miss.
        cached.verify(&source);
        assert_eq!(inner.calls(), 1);

        // Modify the file.
        std::fs::write(&source, "fn main() { 2 + 2 }").expect("write v2");

        // Second call: cache miss due to hash change.
        cached.verify(&source);
        assert_eq!(inner.calls(), 2);

        let stats = cached.stats();
        assert_eq!(stats.hits, 0);
        assert_eq!(stats.misses, 2);
    }

    // -- Test: cache disabled passes through --

    #[test]
    fn test_cache_disabled_always_delegates() {
        let tmp = tempfile::TempDir::new().expect("create temp dir");
        let source = tmp.path().join("test.rs");
        std::fs::write(&source, "fn main() {}").expect("write source");

        let inner = CountingVerify::new(proved_output());
        let config = CacheConfig::disabled();
        let cached = CachedVerifyPhase::new(&inner, config);

        // Both calls delegate to inner.
        cached.verify(&source);
        cached.verify(&source);
        assert_eq!(inner.calls(), 2);

        let stats = cached.stats();
        assert_eq!(stats.hits, 0);
        assert_eq!(stats.misses, 0); // Not tracked when disabled
    }

    // -- Test: cache persistence --

    #[test]
    fn test_cache_persistence_save_and_load() {
        let tmp = tempfile::TempDir::new().expect("create temp dir");
        let source = tmp.path().join("test.rs");
        std::fs::write(&source, "fn main() { verified() }").expect("write source");
        let cache_dir = tmp.path().join(".trust-cache");

        // Run 1: verify and save.
        {
            let inner = CountingVerify::new(proved_output());
            let config = CacheConfig {
                enabled: true,
                cache_dir: cache_dir.clone(),
            };
            let cached = CachedVerifyPhase::new(&inner, config);
            cached.verify(&source);
            assert_eq!(inner.calls(), 1);
            cached.save().expect("save should succeed");
        }

        // Verify the state file was created.
        assert!(cache_dir.join(STATE_FILE).exists());

        // Run 2: load from disk. Same file -> cache hit.
        {
            let inner = CountingVerify::new(proved_output());
            let config = CacheConfig {
                enabled: true,
                cache_dir: cache_dir.clone(),
            };
            let cached = CachedVerifyPhase::new(&inner, config);
            let out = cached.verify(&source);
            assert_eq!(inner.calls(), 0); // Cache hit from persisted state!
            assert_eq!(out.fingerprint, Some("cached".to_string()));

            let stats = cached.stats();
            assert_eq!(stats.hits, 1);
            assert_eq!(stats.misses, 0);
        }
    }

    // -- Test: failed verification is also cached --

    #[test]
    fn test_failed_result_cached() {
        let tmp = tempfile::TempDir::new().expect("create temp dir");
        let source = tmp.path().join("test.rs");
        std::fs::write(&source, "fn buggy() { panic!() }").expect("write source");

        let inner = CountingVerify::new(failed_output());
        let config = CacheConfig {
            enabled: true,
            cache_dir: tmp.path().join(".trust-cache"),
        };
        let cached = CachedVerifyPhase::new(&inner, config);

        // First call: cache miss.
        let out1 = cached.verify(&source);
        assert_eq!(out1.vcs_failed, 2);
        assert_eq!(inner.calls(), 1);

        // Second call: cache hit returns Failed outcome.
        // tRust: F13 fix -- cache now preserves full frontier counts.
        let out2 = cached.verify(&source);
        assert_eq!(inner.calls(), 1);
        assert_eq!(out2.frontier.failed, 2); // F13 fix: preserved from original output
        assert_eq!(out2.frontier.trusted, 1); // F13 fix: preserved from original output
        assert_eq!(out2.vcs_failed, 2); // F13 fix: preserved VC count
        assert_eq!(out2.vcs_dispatched, 3); // F13 fix: preserved VC count
    }

    // -- Test: CacheStats --

    #[test]
    fn test_cache_stats_hit_rate() {
        let stats = CacheStats {
            hits: 3,
            misses: 1,
            time_saved: Duration::from_secs(10),
        };
        assert_eq!(stats.total(), 4);
        assert!((stats.hit_rate() - 0.75).abs() < f64::EPSILON);
    }

    #[test]
    fn test_cache_stats_empty() {
        let stats = CacheStats::default();
        assert_eq!(stats.total(), 0);
        assert_eq!(stats.hit_rate(), 0.0);
    }

    // -- Test: CacheConfig --

    #[test]
    fn test_cache_config_default() {
        let config = CacheConfig::default();
        assert!(config.enabled);
        assert_eq!(config.cache_dir, PathBuf::from(".trust-cache"));
        assert_eq!(
            config.state_file_path(),
            PathBuf::from(".trust-cache/incremental_state.txt")
        );
    }

    #[test]
    fn test_cache_config_disabled() {
        let config = CacheConfig::disabled();
        assert!(!config.enabled);
    }

    // -- Test: hash_source_files utility --

    #[test]
    fn test_hash_source_files() {
        let tmp = tempfile::TempDir::new().expect("create temp dir");
        let f1 = tmp.path().join("a.rs");
        let f2 = tmp.path().join("b.rs");
        let f3 = tmp.path().join("c.txt"); // not .rs

        std::fs::write(&f1, "fn a() {}").expect("write a.rs");
        std::fs::write(&f2, "fn b() {}").expect("write b.rs");
        std::fs::write(&f3, "not rust").expect("write c.txt");

        let hashes = hash_source_files(tmp.path());
        assert_eq!(hashes.len(), 2); // Only .rs files
        assert!(hashes.contains_key(&f1.to_string_lossy().to_string()));
        assert!(hashes.contains_key(&f2.to_string_lossy().to_string()));
        assert!(!hashes.contains_key(&f3.to_string_lossy().to_string()));
    }

    // -- Test: with_state constructor --

    #[test]
    fn test_with_state_preloaded() {
        let tmp = tempfile::TempDir::new().expect("create temp dir");
        let source = tmp.path().join("test.rs");
        std::fs::write(&source, "fn main() {}").expect("write source");

        // Compute the hash for this file content.
        let body = std::fs::read(&source).expect("read source");
        let hash = compute_function_hash(&body, b"");

        // Pre-populate cache with a Proved result for this source.
        let mut state = IncrementalState::new();
        state.mark_verified(
            &source.to_string_lossy(),
            hash,
            CachedVerificationOutcome::Proved,
            Duration::from_millis(50),
        );

        let inner = CountingVerify::new(proved_output());
        let config = CacheConfig {
            enabled: true,
            cache_dir: tmp.path().join(".trust-cache"),
        };
        let cached = CachedVerifyPhase::with_state(&inner, config, state);

        // Should hit cache immediately.
        let out = cached.verify(&source);
        assert_eq!(inner.calls(), 0);
        assert_eq!(out.fingerprint, Some("cached".to_string()));
    }

    // -- Test: nonexistent source file falls through --

    #[test]
    fn test_nonexistent_source_falls_through() {
        let inner = CountingVerify::new(proved_output());
        let config = CacheConfig {
            enabled: true,
            cache_dir: PathBuf::from("/tmp/.trust-cache-test-nonexistent"),
        };
        let cached = CachedVerifyPhase::new(&inner, config);

        // Source does not exist -> cannot compute hash -> delegates to inner.
        let _out = cached.verify(Path::new("/nonexistent/path/test.rs"));
        assert_eq!(inner.calls(), 1);
    }

    // -- Test: F13 fix -- cache hit preserves accurate VC counts --

    #[test]
    fn test_cache_hit_preserves_vc_counts() {
        let tmp = tempfile::TempDir::new().expect("create temp dir");
        let source = tmp.path().join("test.rs");
        std::fs::write(&source, "fn verified() { complex_logic() }").expect("write source");

        // Inner returns a rich frontier: 50 trusted, 3 certified, 2 runtime_checked, 5 failed, 1 unknown.
        let rich_output = VerifyOutput {
            frontier: ProofFrontier {
                trusted: 50,
                certified: 3,
                runtime_checked: 2,
                failed: 5,
                unknown: 1,
            },
            fingerprint: None,
            vcs_dispatched: 61,
            vcs_failed: 5,
            detailed_results: None,
        };
        let inner = CountingVerify::new(rich_output);
        let config = CacheConfig {
            enabled: true,
            cache_dir: tmp.path().join(".trust-cache"),
        };
        let cached = CachedVerifyPhase::new(&inner, config);

        // First call: cache miss, delegates to inner.
        let out1 = cached.verify(&source);
        assert_eq!(inner.calls(), 1);
        assert_eq!(out1.frontier.trusted, 50);
        assert_eq!(out1.frontier.certified, 3);
        assert_eq!(out1.frontier.runtime_checked, 2);
        assert_eq!(out1.frontier.failed, 5);
        assert_eq!(out1.frontier.unknown, 1);
        assert_eq!(out1.vcs_dispatched, 61);
        assert_eq!(out1.vcs_failed, 5);

        // Second call: cache hit — all frontier fields must be preserved.
        let out2 = cached.verify(&source);
        assert_eq!(inner.calls(), 1); // NOT incremented
        assert_eq!(out2.frontier.trusted, 50);
        assert_eq!(out2.frontier.certified, 3);
        assert_eq!(out2.frontier.runtime_checked, 2);
        assert_eq!(out2.frontier.failed, 5);
        assert_eq!(out2.frontier.unknown, 1);
        assert_eq!(out2.vcs_dispatched, 61);
        assert_eq!(out2.vcs_failed, 5);
        assert_eq!(out2.fingerprint, Some("cached".to_string()));
    }

    // -- Test: F13 fix -- cache persistence preserves frontier counts --

    #[test]
    fn test_cache_persistence_preserves_frontier() {
        let tmp = tempfile::TempDir::new().expect("create temp dir");
        let source = tmp.path().join("test.rs");
        std::fs::write(&source, "fn persistent() { lots_of_vcs() }").expect("write source");
        let cache_dir = tmp.path().join(".trust-cache");

        let rich_output = VerifyOutput {
            frontier: ProofFrontier {
                trusted: 42,
                certified: 7,
                runtime_checked: 0,
                failed: 3,
                unknown: 0,
            },
            fingerprint: None,
            vcs_dispatched: 52,
            vcs_failed: 3,
            detailed_results: None,
        };

        // Run 1: verify and save.
        {
            let inner = CountingVerify::new(rich_output);
            let config = CacheConfig {
                enabled: true,
                cache_dir: cache_dir.clone(),
            };
            let cached = CachedVerifyPhase::new(&inner, config);
            cached.verify(&source);
            cached.save().expect("save should succeed");
        }

        // Run 2: load from disk, cache hit should restore exact frontier.
        {
            let inner = CountingVerify::new(proved_output()); // won't be called
            let config = CacheConfig {
                enabled: true,
                cache_dir: cache_dir.clone(),
            };
            let cached = CachedVerifyPhase::new(&inner, config);
            let out = cached.verify(&source);
            assert_eq!(inner.calls(), 0);
            assert_eq!(out.frontier.trusted, 42);
            assert_eq!(out.frontier.certified, 7);
            assert_eq!(out.frontier.failed, 3);
            assert_eq!(out.vcs_dispatched, 52);
            assert_eq!(out.vcs_failed, 3);
        }
    }
}
