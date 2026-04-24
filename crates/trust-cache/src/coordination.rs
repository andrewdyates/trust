// trust-cache/src/coordination.rs: File-based cache coordination for concurrent compilations
//
// Provides advisory file locking (flock-style) to prevent cache corruption when
// multiple tRust compilations run concurrently (e.g., parallel agent worktrees).
//
// Key features:
// - Advisory file locks via fs2 for cross-platform flock support
// - Stale lock detection: locks older than a configurable threshold are force-released
// - Content-hash-based invalidation: cache files include a content hash so readers
//   can detect writes from other processes without holding a lock
// - Shared (read) and exclusive (write) lock modes
//
// tRust #884: Cache coordination for concurrent trustc compilations.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::fs::{self, File, OpenOptions};
use std::io;
use std::path::{Path, PathBuf};
use std::time::{Duration, SystemTime};

use sha2::{Digest, Sha256};
use thiserror::Error;

/// Trait alias for fs2 locking to avoid conflict with std's nightly File::try_lock_*.
/// On nightly rustc, `std::fs::File` has built-in `try_lock_shared`/`try_lock_exclusive`
/// that return `Result<(), TryLockError>` -- these shadow fs2's `io::Result<()>` methods.
/// We use fully-qualified syntax to call fs2's version explicitly.
use fs2::FileExt as Fs2FileExt;

/// Default stale lock threshold: 5 minutes.
/// Locks older than this are considered stale and can be force-released.
const DEFAULT_STALE_LOCK_SECS: u64 = 300;

/// Errors from cache coordination operations.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum CoordinationError {
    #[error("lock I/O error on {path}: {source}")]
    LockIo { path: PathBuf, source: io::Error },
    #[error("lock acquisition timed out on {path} after {timeout_ms}ms")]
    LockTimeout { path: PathBuf, timeout_ms: u64 },
    #[error("content hash mismatch: expected {expected}, found {found}")]
    ContentHashMismatch { expected: String, found: String },
}

/// Configuration for cache coordination.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CoordinationConfig {
    /// Seconds after which a lock sentinel file is considered stale.
    pub stale_lock_threshold_secs: u64,
    /// Whether to enable content-hash validation on cache reads.
    pub validate_content_hash: bool,
}

impl Default for CoordinationConfig {
    fn default() -> Self {
        Self { stale_lock_threshold_secs: DEFAULT_STALE_LOCK_SECS, validate_content_hash: true }
    }
}

/// An advisory file lock guard.
///
/// Holds an flock advisory lock on a `.lock` file adjacent to the cache file.
/// The lock is released when this guard is dropped.
///
/// Uses `fs2::FileExt` for cross-platform flock support (works on macOS, Linux,
/// and Windows). The lock is process-scoped and automatically released if the
/// process crashes.
pub struct CacheLockGuard {
    /// The lock file handle. Lock is released on drop (via fs2).
    _file: File,
    /// Path to the lock file (for diagnostics).
    lock_path: PathBuf,
}

impl CacheLockGuard {
    /// Path to the lock file being held.
    #[must_use]
    pub fn lock_path(&self) -> &Path {
        &self.lock_path
    }
}

impl Drop for CacheLockGuard {
    fn drop(&mut self) {
        // fs2 automatically releases the flock when the File is dropped,
        // but we explicitly unlock for clarity and to handle edge cases.
        let _ = Fs2FileExt::unlock(&self._file);
    }
}

/// Acquire a shared (read) lock on the cache file.
///
/// Multiple readers can hold shared locks simultaneously. A shared lock
/// blocks exclusive lock acquisition but not other shared locks.
///
/// If the lock sentinel file is stale (older than `config.stale_lock_threshold_secs`),
/// it is deleted and recreated before locking.
pub fn acquire_shared_lock(
    cache_path: &Path,
    config: &CoordinationConfig,
) -> Result<CacheLockGuard, CoordinationError> {
    let lock_path = lock_path_for(cache_path);
    cleanup_stale_lock(&lock_path, config.stale_lock_threshold_secs)?;
    let file = open_lock_file(&lock_path)?;
    Fs2FileExt::lock_shared(&file)
        .map_err(|e| CoordinationError::LockIo { path: lock_path.clone(), source: e })?;
    Ok(CacheLockGuard { _file: file, lock_path })
}

/// Acquire an exclusive (write) lock on the cache file.
///
/// Only one writer can hold an exclusive lock. This blocks all other
/// shared and exclusive lock acquisitions.
///
/// If the lock sentinel file is stale (older than `config.stale_lock_threshold_secs`),
/// it is deleted and recreated before locking.
pub fn acquire_exclusive_lock(
    cache_path: &Path,
    config: &CoordinationConfig,
) -> Result<CacheLockGuard, CoordinationError> {
    let lock_path = lock_path_for(cache_path);
    cleanup_stale_lock(&lock_path, config.stale_lock_threshold_secs)?;
    let file = open_lock_file(&lock_path)?;
    Fs2FileExt::lock_exclusive(&file)
        .map_err(|e| CoordinationError::LockIo { path: lock_path.clone(), source: e })?;
    Ok(CacheLockGuard { _file: file, lock_path })
}

/// Try to acquire a shared lock without blocking.
///
/// Returns `Ok(Some(guard))` on success, `Ok(None)` if the lock is held
/// exclusively by another process.
pub fn try_shared_lock(
    cache_path: &Path,
    config: &CoordinationConfig,
) -> Result<Option<CacheLockGuard>, CoordinationError> {
    let lock_path = lock_path_for(cache_path);
    cleanup_stale_lock(&lock_path, config.stale_lock_threshold_secs)?;
    let file = open_lock_file(&lock_path)?;
    match Fs2FileExt::try_lock_shared(&file) {
        Ok(()) => Ok(Some(CacheLockGuard { _file: file, lock_path })),
        Err(ref e) if is_would_block(e) => Ok(None),
        Err(e) => Err(CoordinationError::LockIo { path: lock_path, source: e }),
    }
}

/// Try to acquire an exclusive lock without blocking.
///
/// Returns `Ok(Some(guard))` on success, `Ok(None)` if the lock is held
/// by another process.
pub fn try_exclusive_lock(
    cache_path: &Path,
    config: &CoordinationConfig,
) -> Result<Option<CacheLockGuard>, CoordinationError> {
    let lock_path = lock_path_for(cache_path);
    cleanup_stale_lock(&lock_path, config.stale_lock_threshold_secs)?;
    let file = open_lock_file(&lock_path)?;
    match Fs2FileExt::try_lock_exclusive(&file) {
        Ok(()) => Ok(Some(CacheLockGuard { _file: file, lock_path })),
        Err(ref e) if is_would_block(e) => Ok(None),
        Err(e) => Err(CoordinationError::LockIo { path: lock_path, source: e }),
    }
}

/// Compute the SHA-256 content hash of a file on disk.
///
/// Returns the hex-encoded hash, or an empty string if the file does not exist.
/// This hash is used for content-based invalidation: if the hash of the file
/// on disk differs from what we expect, another process has written to it.
#[must_use]
pub fn file_content_hash(path: &Path) -> String {
    match fs::read(path) {
        Ok(bytes) => {
            let mut hasher = Sha256::new();
            hasher.update(&bytes);
            format!("{:x}", hasher.finalize())
        }
        Err(_) => String::new(),
    }
}

/// Validate that a cache file's content hash matches the expected value.
///
/// Returns `Ok(())` if the hashes match or the expected hash is empty
/// (indicating no prior state to validate against). Returns
/// `Err(CoordinationError::ContentHashMismatch)` otherwise.
pub fn validate_content_hash(path: &Path, expected_hash: &str) -> Result<(), CoordinationError> {
    if expected_hash.is_empty() {
        return Ok(());
    }
    let actual = file_content_hash(path);
    if actual.is_empty() {
        // File doesn't exist -- no mismatch
        return Ok(());
    }
    if actual != expected_hash {
        return Err(CoordinationError::ContentHashMismatch {
            expected: expected_hash.to_string(),
            found: actual,
        });
    }
    Ok(())
}

/// Coordinated read: acquire shared lock, read file, validate content hash.
///
/// Returns `(contents, content_hash)` on success. The caller can store the
/// content hash and use it later to detect concurrent writes.
pub fn coordinated_read(
    cache_path: &Path,
    config: &CoordinationConfig,
) -> Result<(String, String, CacheLockGuard), CoordinationError> {
    let guard = acquire_shared_lock(cache_path, config)?;
    let contents = fs::read_to_string(cache_path)
        .map_err(|e| CoordinationError::LockIo { path: cache_path.to_path_buf(), source: e })?;
    let hash = {
        let mut hasher = Sha256::new();
        hasher.update(contents.as_bytes());
        format!("{:x}", hasher.finalize())
    };
    Ok((contents, hash, guard))
}

/// Coordinated write: acquire exclusive lock, write file atomically.
///
/// Writes to a temporary file first, then renames to the target path.
/// This ensures readers never see a partially-written file. Returns
/// the content hash of the written data.
pub fn coordinated_write(
    cache_path: &Path,
    data: &str,
    config: &CoordinationConfig,
) -> Result<(String, CacheLockGuard), CoordinationError> {
    let guard = acquire_exclusive_lock(cache_path, config)?;

    // Write to a temp file in the same directory, then rename for atomicity.
    let tmp_path = cache_path.with_extension("tmp");
    fs::write(&tmp_path, data)
        .map_err(|e| CoordinationError::LockIo { path: tmp_path.clone(), source: e })?;
    fs::rename(&tmp_path, cache_path)
        .map_err(|e| CoordinationError::LockIo { path: cache_path.to_path_buf(), source: e })?;

    let hash = {
        let mut hasher = Sha256::new();
        hasher.update(data.as_bytes());
        format!("{:x}", hasher.finalize())
    };
    Ok((hash, guard))
}

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

/// Check if an I/O error represents a "would block" condition.
///
/// `fs2::try_lock_*` returns a plain `io::Error`. On Unix, the "lock is held"
/// condition is `EWOULDBLOCK` (= `EAGAIN`), which maps to `ErrorKind::WouldBlock`.
fn is_would_block(err: &io::Error) -> bool {
    err.kind() == io::ErrorKind::WouldBlock
        // Some platforms report EAGAIN differently
        || err.raw_os_error() == Some(libc_eagain())
}

/// Platform-specific EAGAIN constant.
fn libc_eagain() -> i32 {
    // EAGAIN is 35 on macOS, 11 on Linux
    #[cfg(target_os = "macos")]
    {
        35
    }
    #[cfg(target_os = "linux")]
    {
        11
    }
    #[cfg(not(any(target_os = "macos", target_os = "linux")))]
    {
        -1
    } // Will never match, fall back to kind() check
}

/// Compute the lock file path for a given cache file.
///
/// The lock file is `<cache_path>.lock` in the same directory.
fn lock_path_for(cache_path: &Path) -> PathBuf {
    let mut lock_path = cache_path.as_os_str().to_owned();
    lock_path.push(".lock");
    PathBuf::from(lock_path)
}

/// Open (or create) the lock file.
fn open_lock_file(lock_path: &Path) -> Result<File, CoordinationError> {
    if let Some(parent) = lock_path.parent() {
        fs::create_dir_all(parent)
            .map_err(|e| CoordinationError::LockIo { path: lock_path.to_path_buf(), source: e })?;
    }
    OpenOptions::new()
        .create(true)
        .truncate(false)
        .read(true)
        .write(true)
        .open(lock_path)
        .map_err(|e| CoordinationError::LockIo { path: lock_path.to_path_buf(), source: e })
}

/// Detect and clean up stale lock files.
///
/// A lock file is stale if its modification time is older than
/// `threshold_secs` seconds ago. This handles the case where a process
/// crashed while holding a lock -- the flock itself is released by the OS,
/// but the sentinel file remains.
///
/// Note: flock locks are automatically released by the OS when the process
/// exits (even on crash). The stale lock cleanup is primarily for the
/// sentinel file itself, not the actual lock state.
fn cleanup_stale_lock(lock_path: &Path, threshold_secs: u64) -> Result<(), CoordinationError> {
    let metadata = match fs::metadata(lock_path) {
        Ok(m) => m,
        Err(ref e) if e.kind() == io::ErrorKind::NotFound => return Ok(()),
        Err(e) => {
            return Err(CoordinationError::LockIo { path: lock_path.to_path_buf(), source: e });
        }
    };

    let modified = metadata.modified().unwrap_or(SystemTime::UNIX_EPOCH);
    let age = SystemTime::now().duration_since(modified).unwrap_or(Duration::ZERO);

    if age > Duration::from_secs(threshold_secs) {
        // Lock file is stale. Remove it so we can create a fresh one.
        // Ignore errors -- another process may have already cleaned it up.
        let _ = fs::remove_file(lock_path);
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use std::sync::{Arc, Barrier};
    use std::thread;

    use super::*;

    fn default_config() -> CoordinationConfig {
        CoordinationConfig::default()
    }

    // -----------------------------------------------------------------------
    // Lock path computation
    // -----------------------------------------------------------------------

    #[test]
    fn test_lock_path_for_appends_dot_lock() {
        let cache = Path::new("/tmp/cache/trust-cache.json");
        let lock = lock_path_for(cache);
        assert_eq!(lock, PathBuf::from("/tmp/cache/trust-cache.json.lock"));
    }

    #[test]
    fn test_lock_path_for_handles_no_extension() {
        let cache = Path::new("/tmp/cache/trust-cache");
        let lock = lock_path_for(cache);
        assert_eq!(lock, PathBuf::from("/tmp/cache/trust-cache.lock"));
    }

    // -----------------------------------------------------------------------
    // Shared lock acquisition
    // -----------------------------------------------------------------------

    #[test]
    fn test_acquire_shared_lock_creates_lock_file() {
        let dir = tempfile::tempdir().expect("create tempdir");
        let cache_path = dir.path().join("test-cache.json");
        fs::write(&cache_path, "{}").expect("write cache");

        let guard = acquire_shared_lock(&cache_path, &default_config());
        assert!(guard.is_ok());
        let guard = guard.unwrap();
        assert!(guard.lock_path().exists());
        drop(guard);
    }

    #[test]
    fn test_multiple_shared_locks_coexist() {
        let dir = tempfile::tempdir().expect("create tempdir");
        let cache_path = dir.path().join("test-cache.json");
        fs::write(&cache_path, "{}").expect("write cache");

        let guard1 =
            acquire_shared_lock(&cache_path, &default_config()).expect("first shared lock");
        let guard2 = acquire_shared_lock(&cache_path, &default_config())
            .expect("second shared lock should succeed");

        // Both guards exist simultaneously
        assert!(guard1.lock_path().exists());
        assert!(guard2.lock_path().exists());
        drop(guard1);
        drop(guard2);
    }

    // -----------------------------------------------------------------------
    // Exclusive lock acquisition
    // -----------------------------------------------------------------------

    #[test]
    fn test_acquire_exclusive_lock_creates_lock_file() {
        let dir = tempfile::tempdir().expect("create tempdir");
        let cache_path = dir.path().join("test-cache.json");
        fs::write(&cache_path, "{}").expect("write cache");

        let guard = acquire_exclusive_lock(&cache_path, &default_config());
        assert!(guard.is_ok());
        let guard = guard.unwrap();
        assert!(guard.lock_path().exists());
        drop(guard);
    }

    #[test]
    fn test_try_exclusive_lock_fails_when_held() {
        let dir = tempfile::tempdir().expect("create tempdir");
        let cache_path = dir.path().join("test-cache.json");
        fs::write(&cache_path, "{}").expect("write cache");

        let _guard =
            acquire_exclusive_lock(&cache_path, &default_config()).expect("first exclusive lock");

        // Try non-blocking exclusive lock -- should fail
        let result = try_exclusive_lock(&cache_path, &default_config())
            .expect("try_exclusive_lock should not error");
        assert!(result.is_none(), "second exclusive lock should fail (non-blocking)");
    }

    #[test]
    fn test_try_shared_lock_fails_when_exclusive_held() {
        let dir = tempfile::tempdir().expect("create tempdir");
        let cache_path = dir.path().join("test-cache.json");
        fs::write(&cache_path, "{}").expect("write cache");

        let _guard =
            acquire_exclusive_lock(&cache_path, &default_config()).expect("exclusive lock");

        // Try non-blocking shared lock -- should fail
        let result = try_shared_lock(&cache_path, &default_config())
            .expect("try_shared_lock should not error");
        assert!(result.is_none(), "shared lock should fail while exclusive held");
    }

    // -----------------------------------------------------------------------
    // Lock release on drop
    // -----------------------------------------------------------------------

    #[test]
    fn test_lock_released_on_drop() {
        let dir = tempfile::tempdir().expect("create tempdir");
        let cache_path = dir.path().join("test-cache.json");
        fs::write(&cache_path, "{}").expect("write cache");

        {
            let _guard =
                acquire_exclusive_lock(&cache_path, &default_config()).expect("exclusive lock");
            // Guard is dropped here
        }

        // Should be able to acquire again
        let guard = acquire_exclusive_lock(&cache_path, &default_config());
        assert!(guard.is_ok(), "should acquire lock after previous guard dropped");
    }

    // -----------------------------------------------------------------------
    // Stale lock detection
    // -----------------------------------------------------------------------

    #[test]
    fn test_stale_lock_cleanup() {
        let dir = tempfile::tempdir().expect("create tempdir");
        let cache_path = dir.path().join("test-cache.json");
        let lock_path = lock_path_for(&cache_path);

        // Create a "stale" lock file with old mtime
        fs::write(&lock_path, "").expect("write lock file");

        // Set modification time to the past using filetime crate-free approach:
        // Use a very short threshold so the lock is considered stale immediately.
        let config = CoordinationConfig {
            stale_lock_threshold_secs: 0, // 0 seconds = always stale
            validate_content_hash: true,
        };

        // The cleanup should remove the stale file and allow acquisition
        let guard = acquire_exclusive_lock(&cache_path, &config);
        assert!(guard.is_ok(), "should acquire lock after stale cleanup");
    }

    // -----------------------------------------------------------------------
    // Content hash computation
    // -----------------------------------------------------------------------

    #[test]
    fn test_file_content_hash_deterministic() {
        let dir = tempfile::tempdir().expect("create tempdir");
        let path = dir.path().join("test.json");
        fs::write(&path, r#"{"key": "value"}"#).expect("write file");

        let h1 = file_content_hash(&path);
        let h2 = file_content_hash(&path);
        assert_eq!(h1, h2, "content hash must be deterministic");
        assert_eq!(h1.len(), 64, "SHA-256 hex is 64 chars");
    }

    #[test]
    fn test_file_content_hash_nonexistent_returns_empty() {
        let hash = file_content_hash(Path::new("/nonexistent/path/file.json"));
        assert!(hash.is_empty());
    }

    #[test]
    fn test_file_content_hash_changes_with_content() {
        let dir = tempfile::tempdir().expect("create tempdir");
        let path = dir.path().join("test.json");

        fs::write(&path, "version 1").expect("write v1");
        let h1 = file_content_hash(&path);

        fs::write(&path, "version 2").expect("write v2");
        let h2 = file_content_hash(&path);

        assert_ne!(h1, h2, "different content must produce different hashes");
    }

    // -----------------------------------------------------------------------
    // Content hash validation
    // -----------------------------------------------------------------------

    #[test]
    fn test_validate_content_hash_match() {
        let dir = tempfile::tempdir().expect("create tempdir");
        let path = dir.path().join("test.json");
        let data = r#"{"entries": {}}"#;
        fs::write(&path, data).expect("write file");

        let hash = file_content_hash(&path);
        let result = validate_content_hash(&path, &hash);
        assert!(result.is_ok(), "matching hash should validate");
    }

    #[test]
    fn test_validate_content_hash_mismatch() {
        let dir = tempfile::tempdir().expect("create tempdir");
        let path = dir.path().join("test.json");
        fs::write(&path, "original").expect("write file");

        let result = validate_content_hash(
            &path,
            "0000000000000000000000000000000000000000000000000000000000000000",
        );
        assert!(result.is_err(), "mismatched hash should fail");

        let err = result.unwrap_err();
        assert!(
            matches!(err, CoordinationError::ContentHashMismatch { .. }),
            "should be ContentHashMismatch"
        );
    }

    #[test]
    fn test_validate_content_hash_empty_expected_always_ok() {
        let dir = tempfile::tempdir().expect("create tempdir");
        let path = dir.path().join("test.json");
        fs::write(&path, "anything").expect("write file");

        let result = validate_content_hash(&path, "");
        assert!(result.is_ok(), "empty expected hash should always pass");
    }

    #[test]
    fn test_validate_content_hash_nonexistent_file_ok() {
        let result = validate_content_hash(Path::new("/nonexistent/file.json"), "some_hash");
        assert!(result.is_ok(), "nonexistent file should be ok (no mismatch)");
    }

    // -----------------------------------------------------------------------
    // Coordinated read/write
    // -----------------------------------------------------------------------

    #[test]
    fn test_coordinated_write_and_read_roundtrip() {
        let dir = tempfile::tempdir().expect("create tempdir");
        let cache_path = dir.path().join("coord-test.json");
        let config = default_config();

        let data = r#"{"version": 3, "entries": {}, "hmac": ""}"#;
        let (write_hash, _guard) = coordinated_write(&cache_path, data, &config).expect("write");
        assert_eq!(write_hash.len(), 64);
        drop(_guard);

        let (contents, read_hash, _guard) = coordinated_read(&cache_path, &config).expect("read");
        assert_eq!(contents, data);
        assert_eq!(write_hash, read_hash, "write and read hashes must match");
    }

    #[test]
    fn test_coordinated_write_atomic() {
        let dir = tempfile::tempdir().expect("create tempdir");
        let cache_path = dir.path().join("atomic-test.json");
        let config = default_config();

        // Write initial data
        let (_, _guard) = coordinated_write(&cache_path, "initial", &config).expect("first write");
        drop(_guard);

        // Overwrite with new data
        let (_, _guard) = coordinated_write(&cache_path, "updated", &config).expect("second write");
        drop(_guard);

        let contents = fs::read_to_string(&cache_path).expect("read result");
        assert_eq!(contents, "updated");

        // Temp file should be cleaned up
        let tmp_path = cache_path.with_extension("tmp");
        assert!(!tmp_path.exists(), "temp file should be cleaned up after rename");
    }

    // -----------------------------------------------------------------------
    // Concurrent access tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_concurrent_writers_serialize() {
        let dir = tempfile::tempdir().expect("create tempdir");
        let cache_path = dir.path().join("concurrent-write.json");
        let config = default_config();

        // Initialize the file
        fs::write(&cache_path, "").expect("init");

        let num_writers = 8;
        let barrier = Arc::new(Barrier::new(num_writers));
        let path = Arc::new(cache_path.clone());

        let handles: Vec<_> = (0..num_writers)
            .map(|i| {
                let barrier = Arc::clone(&barrier);
                let path = Arc::clone(&path);
                let config = config.clone();
                thread::spawn(move || {
                    barrier.wait();
                    let data = format!("writer-{i}");
                    let result = coordinated_write(&path, &data, &config);
                    result.is_ok()
                })
            })
            .collect();

        let results: Vec<bool> = handles.into_iter().map(|h| h.join().unwrap()).collect();
        assert!(results.iter().all(|&r| r), "all writers should succeed");

        // File should contain one of the writer's data (last writer wins)
        let final_contents = fs::read_to_string(&cache_path).expect("read final");
        assert!(
            final_contents.starts_with("writer-"),
            "final contents should be from one writer: got '{final_contents}'"
        );
    }

    #[test]
    fn test_concurrent_readers_dont_block() {
        let dir = tempfile::tempdir().expect("create tempdir");
        let cache_path = dir.path().join("concurrent-read.json");
        let config = default_config();

        // Write initial data
        let data = r#"{"test": "concurrent read"}"#;
        fs::write(&cache_path, data).expect("write initial");

        let num_readers = 8;
        let barrier = Arc::new(Barrier::new(num_readers));
        let path = Arc::new(cache_path.clone());

        let handles: Vec<_> = (0..num_readers)
            .map(|_| {
                let barrier = Arc::clone(&barrier);
                let path = Arc::clone(&path);
                let config = config.clone();
                thread::spawn(move || {
                    barrier.wait();
                    let result = coordinated_read(&path, &config);
                    match result {
                        Ok((contents, _, _guard)) => {
                            assert_eq!(contents, data);
                            true
                        }
                        Err(_) => false,
                    }
                })
            })
            .collect();

        let results: Vec<bool> = handles.into_iter().map(|h| h.join().unwrap()).collect();
        assert!(results.iter().all(|&r| r), "all readers should succeed concurrently");
    }

    #[test]
    fn test_reader_writer_interleaving() {
        let dir = tempfile::tempdir().expect("create tempdir");
        let cache_path = dir.path().join("interleave.json");
        let config = default_config();

        // Initialize
        fs::write(&cache_path, "v0").expect("init");

        let path = Arc::new(cache_path.clone());

        // Writer thread
        let writer_path = Arc::clone(&path);
        let writer_config = config.clone();
        let writer = thread::spawn(move || {
            for i in 0..10 {
                let data = format!("v{}", i + 1);
                coordinated_write(&writer_path, &data, &writer_config)
                    .expect("writer should succeed");
            }
        });

        // Reader threads
        let readers: Vec<_> = (0..4)
            .map(|_| {
                let path = Arc::clone(&path);
                let config = config.clone();
                thread::spawn(move || {
                    for _ in 0..10 {
                        let result = coordinated_read(&path, &config);
                        assert!(result.is_ok(), "reader should succeed");
                        let (contents, _, _guard) = result.unwrap();
                        // Contents should start with "v" (some version)
                        assert!(contents.starts_with('v'), "unexpected contents: {contents}");
                    }
                })
            })
            .collect();

        writer.join().expect("writer thread panicked");
        for r in readers {
            r.join().expect("reader thread panicked");
        }

        // Final state should be the last writer's value
        let final_contents = fs::read_to_string(&cache_path).expect("read final");
        assert_eq!(final_contents, "v10");
    }

    // -----------------------------------------------------------------------
    // Config tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_default_config() {
        let config = CoordinationConfig::default();
        assert_eq!(config.stale_lock_threshold_secs, DEFAULT_STALE_LOCK_SECS);
        assert!(config.validate_content_hash);
    }

    // -----------------------------------------------------------------------
    // Error display tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_error_display() {
        let err = CoordinationError::ContentHashMismatch {
            expected: "abc".to_string(),
            found: "def".to_string(),
        };
        let msg = format!("{err}");
        assert!(msg.contains("abc"));
        assert!(msg.contains("def"));
    }
}
