//! Rollback capabilities for source rewrites.
//!
//! Creates checkpoints of file state before rewrites and supports reverting
//! to the checkpoint if rewrites cause problems (e.g., test failures).
//! Uses SHA-256 hashes to verify rollback integrity.
//!
//! Author: Andrew Yates <andrew@andrewdyates.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;
use std::io::Write;
use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use thiserror::Error;

/// Errors from checkpoint and rollback operations.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum RollbackError {
    /// An I/O error reading or writing a file during checkpoint/rollback.
    #[error("I/O error on `{path}`: {source}")]
    Io {
        path: String,
        source: std::io::Error,
    },
    /// The file hash after rollback does not match the checkpoint.
    #[error("rollback verification failed for `{path}`: expected hash {expected}, got {actual}")]
    VerificationFailed {
        path: String,
        expected: String,
        actual: String,
    },
    /// The checkpoint file could not be deserialized.
    #[error("checkpoint deserialization failed: {0}")]
    Deserialize(String),
    /// The checkpoint file could not be serialized.
    #[error("checkpoint serialization failed: {0}")]
    Serialize(String),
}

/// Snapshot of a single file's state at checkpoint time.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FileSnapshot {
    /// The file path (absolute or relative to project root).
    pub path: PathBuf,
    /// The file contents at checkpoint time.
    pub contents: String,
    /// SHA-256 hash of the contents for integrity verification.
    pub hash: String,
}

/// A checkpoint capturing the state of one or more files before rewriting.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RewriteCheckpoint {
    /// Unique identifier for this checkpoint.
    pub id: String,
    /// When the checkpoint was created (ISO 8601 timestamp or epoch seconds).
    pub created_at: String,
    /// Snapshots of each file at checkpoint time.
    pub snapshots: Vec<FileSnapshot>,
}

impl RewriteCheckpoint {
    /// Number of files in this checkpoint.
    #[must_use]
    pub fn file_count(&self) -> usize {
        self.snapshots.len()
    }

    /// Whether this checkpoint is empty (no files).
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.snapshots.is_empty()
    }

    /// Get the snapshot for a specific file path, if it exists.
    #[must_use]
    pub fn get_snapshot(&self, path: &Path) -> Option<&FileSnapshot> {
        self.snapshots.iter().find(|s| s.path == path)
    }
}

/// Persistent store for checkpoints, backed by a directory on disk.
#[derive(Debug, Clone)]
pub struct CheckpointStore {
    /// Directory where checkpoint files are stored.
    store_dir: PathBuf,
}

impl CheckpointStore {
    /// Create a new checkpoint store at the given directory.
    ///
    /// Creates the directory if it does not exist.
    ///
    /// # Errors
    ///
    /// Returns `RollbackError::Io` if the directory cannot be created.
    pub fn new(store_dir: impl AsRef<Path>) -> Result<Self, RollbackError> {
        let dir = store_dir.as_ref().to_path_buf();
        std::fs::create_dir_all(&dir).map_err(|e| RollbackError::Io {
            path: dir.display().to_string(),
            source: e,
        })?;
        Ok(Self { store_dir: dir })
    }

    /// Save a checkpoint to the store atomically.
    ///
    /// Uses the tempfile + rename pattern so a crash mid-write never
    /// corrupts an existing checkpoint file.
    ///
    /// # Errors
    ///
    /// Returns `RollbackError::Serialize` or `RollbackError::Io` on failure.
    pub fn save(&self, checkpoint: &RewriteCheckpoint) -> Result<PathBuf, RollbackError> {
        let json = serde_json::to_string_pretty(checkpoint)
            .map_err(|e| RollbackError::Serialize(e.to_string()))?;
        let file_path = self.store_dir.join(format!("{}.json", checkpoint.id));

        let mut tmp =
            tempfile::NamedTempFile::new_in(&self.store_dir).map_err(|e| RollbackError::Io {
                path: file_path.display().to_string(),
                source: e,
            })?;
        tmp.write_all(json.as_bytes())
            .map_err(|e| RollbackError::Io {
                path: file_path.display().to_string(),
                source: e,
            })?;
        tmp.flush().map_err(|e| RollbackError::Io {
            path: file_path.display().to_string(),
            source: e,
        })?;
        tmp.persist(&file_path)
            .map_err(|e| RollbackError::Io {
                path: file_path.display().to_string(),
                source: e.error,
            })?;

        Ok(file_path)
    }

    /// Load a checkpoint from the store by ID.
    ///
    /// # Errors
    ///
    /// Returns `RollbackError::Io` if the file cannot be read, or
    /// `RollbackError::Deserialize` if it cannot be parsed.
    pub fn load(&self, id: &str) -> Result<RewriteCheckpoint, RollbackError> {
        let file_path = self.store_dir.join(format!("{id}.json"));
        let json = std::fs::read_to_string(&file_path).map_err(|e| RollbackError::Io {
            path: file_path.display().to_string(),
            source: e,
        })?;
        serde_json::from_str(&json).map_err(|e| RollbackError::Deserialize(e.to_string()))
    }

    /// List all checkpoint IDs in the store.
    ///
    /// # Errors
    ///
    /// Returns `RollbackError::Io` if the store directory cannot be read.
    pub fn list(&self) -> Result<Vec<String>, RollbackError> {
        let mut ids = Vec::new();
        let entries = std::fs::read_dir(&self.store_dir).map_err(|e| RollbackError::Io {
            path: self.store_dir.display().to_string(),
            source: e,
        })?;
        for entry in entries {
            let entry = entry.map_err(|e| RollbackError::Io {
                path: self.store_dir.display().to_string(),
                source: e,
            })?;
            if let Some(name) = entry.path().file_stem()
                && entry.path().extension().is_some_and(|ext| ext == "json") {
                    ids.push(name.to_string_lossy().into_owned());
                }
        }
        ids.sort();
        Ok(ids)
    }

    /// Delete a checkpoint from the store.
    ///
    /// # Errors
    ///
    /// Returns `RollbackError::Io` if the file cannot be removed.
    pub fn delete(&self, id: &str) -> Result<(), RollbackError> {
        let file_path = self.store_dir.join(format!("{id}.json"));
        std::fs::remove_file(&file_path).map_err(|e| RollbackError::Io {
            path: file_path.display().to_string(),
            source: e,
        })
    }
}

/// Compute the SHA-256 hash of a string, returning a hex-encoded digest.
#[must_use]
pub fn sha256_hex(content: &str) -> String {
    let mut hasher = Sha256::new();
    hasher.update(content.as_bytes());
    format!("{:x}", hasher.finalize())
}

/// Create a checkpoint from a list of file paths.
///
/// Reads each file, computes its SHA-256 hash, and stores a snapshot.
/// The checkpoint ID is derived from the current timestamp.
///
/// # Errors
///
/// Returns `RollbackError::Io` if any file cannot be read.
pub fn create_checkpoint(files: &[PathBuf]) -> Result<RewriteCheckpoint, RollbackError> {
    let mut snapshots = Vec::with_capacity(files.len());

    for path in files {
        let contents = std::fs::read_to_string(path).map_err(|e| RollbackError::Io {
            path: path.display().to_string(),
            source: e,
        })?;
        let hash = sha256_hex(&contents);
        snapshots.push(FileSnapshot {
            path: path.clone(),
            contents,
            hash,
        });
    }

    // Generate a unique ID from hash of all file paths + a counter.
    let id = generate_checkpoint_id(&snapshots);

    Ok(RewriteCheckpoint {
        id,
        created_at: format!("{}", std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap_or_default()
            .as_secs()),
        snapshots,
    })
}

/// Rollback files to their state at checkpoint time.
///
/// Writes each file's snapshot contents back to disk, then verifies that
/// the resulting file hash matches the checkpoint hash.
///
/// # Errors
///
/// Returns `RollbackError::Io` if a file cannot be written, or
/// `RollbackError::VerificationFailed` if the hash does not match after write.
pub fn rollback(checkpoint: &RewriteCheckpoint) -> Result<(), RollbackError> {
    // Phase 1: Write all files atomically (tempfile + rename)
    for snapshot in &checkpoint.snapshots {
        let parent = snapshot
            .path
            .parent()
            .unwrap_or(Path::new("."));
        let mut tmp =
            tempfile::NamedTempFile::new_in(parent).map_err(|e| RollbackError::Io {
                path: snapshot.path.display().to_string(),
                source: e,
            })?;
        tmp.write_all(snapshot.contents.as_bytes())
            .map_err(|e| RollbackError::Io {
                path: snapshot.path.display().to_string(),
                source: e,
            })?;
        tmp.flush().map_err(|e| RollbackError::Io {
            path: snapshot.path.display().to_string(),
            source: e,
        })?;
        tmp.persist(&snapshot.path)
            .map_err(|e| RollbackError::Io {
                path: snapshot.path.display().to_string(),
                source: e.error,
            })?;
    }

    // Phase 2: Verify all files
    for snapshot in &checkpoint.snapshots {
        let actual_contents =
            std::fs::read_to_string(&snapshot.path).map_err(|e| RollbackError::Io {
                path: snapshot.path.display().to_string(),
                source: e,
            })?;
        let actual_hash = sha256_hex(&actual_contents);
        if actual_hash != snapshot.hash {
            return Err(RollbackError::VerificationFailed {
                path: snapshot.path.display().to_string(),
                expected: snapshot.hash.clone(),
                actual: actual_hash,
            });
        }
    }

    Ok(())
}

/// Check whether any files have changed since the checkpoint was created.
///
/// Returns a map of changed file paths to their current hash.
/// Files that cannot be read are included with hash `"<unreadable>"`.
#[must_use]
pub fn changed_since_checkpoint(checkpoint: &RewriteCheckpoint) -> FxHashMap<PathBuf, String> {
    let mut changed = FxHashMap::default();
    for snapshot in &checkpoint.snapshots {
        match std::fs::read_to_string(&snapshot.path) {
            Ok(contents) => {
                let current_hash = sha256_hex(&contents);
                if current_hash != snapshot.hash {
                    changed.insert(snapshot.path.clone(), current_hash);
                }
            }
            Err(_) => {
                changed.insert(snapshot.path.clone(), "<unreadable>".into());
            }
        }
    }
    changed
}

/// Generate a checkpoint ID from the snapshots (deterministic for same input).
fn generate_checkpoint_id(snapshots: &[FileSnapshot]) -> String {
    let mut hasher = Sha256::new();
    for snapshot in snapshots {
        hasher.update(snapshot.path.display().to_string().as_bytes());
        hasher.update(snapshot.hash.as_bytes());
    }
    let digest = hasher.finalize();
    format!("ckpt-{:x}", &digest[..8].iter().fold(0u64, |acc, &b| acc << 8 | b as u64))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    fn setup_temp_dir(name: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!("trust_backprop_rollback_{name}"));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).unwrap();
        dir
    }

    fn write_test_file(dir: &Path, name: &str, content: &str) -> PathBuf {
        let path = dir.join(name);
        fs::write(&path, content).unwrap();
        path
    }

    fn cleanup(dir: &Path) {
        let _ = fs::remove_dir_all(dir);
    }

    // --- sha256_hex tests ---

    #[test]
    fn test_sha256_hex_deterministic() {
        let h1 = sha256_hex("hello world");
        let h2 = sha256_hex("hello world");
        assert_eq!(h1, h2);
    }

    #[test]
    fn test_sha256_hex_different_inputs() {
        let h1 = sha256_hex("hello");
        let h2 = sha256_hex("world");
        assert_ne!(h1, h2);
    }

    #[test]
    fn test_sha256_hex_known_value() {
        // SHA-256 of empty string is well-known
        let hash = sha256_hex("");
        assert_eq!(
            hash,
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );
    }

    // --- create_checkpoint tests ---

    #[test]
    fn test_create_checkpoint_single_file() {
        let dir = setup_temp_dir("ckpt_single");
        let f1 = write_test_file(&dir, "a.rs", "fn a() {}\n");

        let ckpt = create_checkpoint(&[f1]).unwrap();
        assert_eq!(ckpt.file_count(), 1);
        assert!(!ckpt.is_empty());
        assert_eq!(ckpt.snapshots[0].contents, "fn a() {}\n");
        assert_eq!(ckpt.snapshots[0].hash, sha256_hex("fn a() {}\n"));

        cleanup(&dir);
    }

    #[test]
    fn test_create_checkpoint_multiple_files() {
        let dir = setup_temp_dir("ckpt_multi");
        let f1 = write_test_file(&dir, "a.rs", "fn a() {}\n");
        let f2 = write_test_file(&dir, "b.rs", "fn b() {}\n");

        let ckpt = create_checkpoint(&[f1, f2]).unwrap();
        assert_eq!(ckpt.file_count(), 2);

        cleanup(&dir);
    }

    #[test]
    fn test_create_checkpoint_empty_files_list() {
        let ckpt = create_checkpoint(&[]).unwrap();
        assert!(ckpt.is_empty());
        assert_eq!(ckpt.file_count(), 0);
    }

    #[test]
    fn test_create_checkpoint_nonexistent_file() {
        let result = create_checkpoint(&[PathBuf::from("/nonexistent/file.rs")]);
        assert!(result.is_err());
        assert!(matches!(result.unwrap_err(), RollbackError::Io { .. }));
    }

    #[test]
    fn test_checkpoint_get_snapshot() {
        let dir = setup_temp_dir("ckpt_get_snap");
        let f1 = write_test_file(&dir, "x.rs", "fn x() {}\n");

        let ckpt = create_checkpoint(std::slice::from_ref(&f1)).unwrap();
        let snap = ckpt.get_snapshot(&f1);
        assert!(snap.is_some());
        assert_eq!(snap.unwrap().contents, "fn x() {}\n");

        assert!(ckpt.get_snapshot(Path::new("/no/such/file")).is_none());

        cleanup(&dir);
    }

    // --- rollback tests ---

    #[test]
    fn test_rollback_restores_original_content() {
        let dir = setup_temp_dir("rb_restore");
        let f1 = write_test_file(&dir, "a.rs", "fn original() {}\n");

        let ckpt = create_checkpoint(std::slice::from_ref(&f1)).unwrap();

        // Modify the file
        fs::write(&f1, "fn modified() {}\n").unwrap();
        assert_eq!(fs::read_to_string(&f1).unwrap(), "fn modified() {}\n");

        // Rollback
        rollback(&ckpt).unwrap();
        assert_eq!(fs::read_to_string(&f1).unwrap(), "fn original() {}\n");

        cleanup(&dir);
    }

    #[test]
    fn test_rollback_multiple_files() {
        let dir = setup_temp_dir("rb_multi");
        let f1 = write_test_file(&dir, "a.rs", "fn a() {}\n");
        let f2 = write_test_file(&dir, "b.rs", "fn b() {}\n");

        let ckpt = create_checkpoint(&[f1.clone(), f2.clone()]).unwrap();

        // Modify both
        fs::write(&f1, "fn a_changed() {}\n").unwrap();
        fs::write(&f2, "fn b_changed() {}\n").unwrap();

        rollback(&ckpt).unwrap();

        assert_eq!(fs::read_to_string(&f1).unwrap(), "fn a() {}\n");
        assert_eq!(fs::read_to_string(&f2).unwrap(), "fn b() {}\n");

        cleanup(&dir);
    }

    #[test]
    fn test_rollback_idempotent() {
        let dir = setup_temp_dir("rb_idempotent");
        let f1 = write_test_file(&dir, "a.rs", "fn a() {}\n");

        let ckpt = create_checkpoint(std::slice::from_ref(&f1)).unwrap();

        // Rollback twice should be fine
        rollback(&ckpt).unwrap();
        rollback(&ckpt).unwrap();
        assert_eq!(fs::read_to_string(&f1).unwrap(), "fn a() {}\n");

        cleanup(&dir);
    }

    // --- changed_since_checkpoint tests ---

    #[test]
    fn test_changed_since_no_changes() {
        let dir = setup_temp_dir("changed_none");
        let f1 = write_test_file(&dir, "a.rs", "fn a() {}\n");

        let ckpt = create_checkpoint(&[f1]).unwrap();
        let changed = changed_since_checkpoint(&ckpt);
        assert!(changed.is_empty());

        cleanup(&dir);
    }

    #[test]
    fn test_changed_since_with_modification() {
        let dir = setup_temp_dir("changed_mod");
        let f1 = write_test_file(&dir, "a.rs", "fn a() {}\n");

        let ckpt = create_checkpoint(std::slice::from_ref(&f1)).unwrap();

        fs::write(&f1, "fn a_changed() {}\n").unwrap();
        let changed = changed_since_checkpoint(&ckpt);
        assert_eq!(changed.len(), 1);
        assert!(changed.contains_key(&f1));

        cleanup(&dir);
    }

    #[test]
    fn test_changed_since_file_deleted() {
        let dir = setup_temp_dir("changed_del");
        let f1 = write_test_file(&dir, "a.rs", "fn a() {}\n");

        let ckpt = create_checkpoint(std::slice::from_ref(&f1)).unwrap();

        fs::remove_file(&f1).unwrap();
        let changed = changed_since_checkpoint(&ckpt);
        assert_eq!(changed.len(), 1);
        assert_eq!(changed[&f1], "<unreadable>");

        cleanup(&dir);
    }

    // --- CheckpointStore tests ---

    #[test]
    fn test_store_save_and_load() {
        let dir = setup_temp_dir("store_save_load");
        let store_dir = dir.join("checkpoints");
        let store = CheckpointStore::new(&store_dir).unwrap();

        let src_dir = dir.join("src");
        fs::create_dir_all(&src_dir).unwrap();
        let f1 = write_test_file(&src_dir, "a.rs", "fn a() {}\n");

        let ckpt = create_checkpoint(&[f1]).unwrap();
        let saved_path = store.save(&ckpt).unwrap();
        assert!(saved_path.exists());

        let loaded = store.load(&ckpt.id).unwrap();
        assert_eq!(loaded.file_count(), 1);
        assert_eq!(loaded.snapshots[0].contents, "fn a() {}\n");

        cleanup(&dir);
    }

    #[test]
    fn test_store_list() {
        let dir = setup_temp_dir("store_list");
        let store_dir = dir.join("checkpoints");
        let store = CheckpointStore::new(&store_dir).unwrap();

        // Create and save two checkpoints
        let src_dir = dir.join("src");
        fs::create_dir_all(&src_dir).unwrap();
        let f1 = write_test_file(&src_dir, "a.rs", "fn a() {}\n");
        let f2 = write_test_file(&src_dir, "b.rs", "fn b() {}\n");

        let ckpt1 = create_checkpoint(&[f1]).unwrap();
        let ckpt2 = create_checkpoint(&[f2]).unwrap();
        store.save(&ckpt1).unwrap();
        store.save(&ckpt2).unwrap();

        let ids = store.list().unwrap();
        assert_eq!(ids.len(), 2);

        cleanup(&dir);
    }

    #[test]
    fn test_store_delete() {
        let dir = setup_temp_dir("store_delete");
        let store_dir = dir.join("checkpoints");
        let store = CheckpointStore::new(&store_dir).unwrap();

        let src_dir = dir.join("src");
        fs::create_dir_all(&src_dir).unwrap();
        let f1 = write_test_file(&src_dir, "a.rs", "fn a() {}\n");

        let ckpt = create_checkpoint(&[f1]).unwrap();
        store.save(&ckpt).unwrap();

        store.delete(&ckpt.id).unwrap();
        let ids = store.list().unwrap();
        assert!(ids.is_empty());

        cleanup(&dir);
    }

    #[test]
    fn test_store_load_nonexistent() {
        let dir = setup_temp_dir("store_nonexist");
        let store = CheckpointStore::new(&dir).unwrap();
        let result = store.load("nonexistent-id");
        assert!(result.is_err());

        cleanup(&dir);
    }

    // --- RewriteCheckpoint tests ---

    #[test]
    fn test_checkpoint_id_deterministic_for_same_input() {
        let dir = setup_temp_dir("ckpt_deterministic");
        let f1 = write_test_file(&dir, "a.rs", "fn a() {}\n");

        let ckpt1 = create_checkpoint(std::slice::from_ref(&f1)).unwrap();
        let ckpt2 = create_checkpoint(&[f1]).unwrap();
        assert_eq!(ckpt1.id, ckpt2.id);

        cleanup(&dir);
    }

    #[test]
    fn test_checkpoint_serialization_roundtrip() {
        let dir = setup_temp_dir("ckpt_serde");
        let f1 = write_test_file(&dir, "a.rs", "fn a() {}\n");

        let ckpt = create_checkpoint(&[f1]).unwrap();
        let json = serde_json::to_string(&ckpt).unwrap();
        let deserialized: RewriteCheckpoint = serde_json::from_str(&json).unwrap();
        assert_eq!(deserialized.id, ckpt.id);
        assert_eq!(deserialized.file_count(), ckpt.file_count());

        cleanup(&dir);
    }

    // --- Integration: checkpoint + modify + rollback ---

    #[test]
    fn test_full_checkpoint_modify_rollback_cycle() {
        let dir = setup_temp_dir("full_cycle");
        let f1 = write_test_file(&dir, "lib.rs", "pub fn get_midpoint(a: u64, b: u64) -> u64 {\n    (a + b) / 2\n}\n");
        let f2 = write_test_file(&dir, "util.rs", "fn helper() -> bool { true }\n");

        // Step 1: Checkpoint
        let ckpt = create_checkpoint(&[f1.clone(), f2.clone()]).unwrap();
        assert_eq!(ckpt.file_count(), 2);
        assert!(changed_since_checkpoint(&ckpt).is_empty());

        // Step 2: Simulate rewrites
        fs::write(&f1, "#[requires(\"a + b < u64::MAX\")]\npub fn get_midpoint(a: u64, b: u64) -> u64 {\n    (a + b) / 2\n}\n").unwrap();
        fs::write(&f2, "#[ensures(\"result == true\")]\nfn helper() -> bool { true }\n").unwrap();

        // Step 3: Verify changes detected
        let changed = changed_since_checkpoint(&ckpt);
        assert_eq!(changed.len(), 2);

        // Step 4: Rollback
        rollback(&ckpt).unwrap();

        // Step 5: Verify restored
        assert_eq!(
            fs::read_to_string(&f1).unwrap(),
            "pub fn get_midpoint(a: u64, b: u64) -> u64 {\n    (a + b) / 2\n}\n"
        );
        assert_eq!(
            fs::read_to_string(&f2).unwrap(),
            "fn helper() -> bool { true }\n"
        );
        assert!(changed_since_checkpoint(&ckpt).is_empty());

        cleanup(&dir);
    }

    #[test]
    fn test_store_full_workflow() {
        let dir = setup_temp_dir("store_workflow");
        let store_dir = dir.join(".trust-checkpoints");
        let store = CheckpointStore::new(&store_dir).unwrap();

        let f1 = write_test_file(&dir, "main.rs", "fn main() {}\n");

        // Save checkpoint
        let ckpt = create_checkpoint(std::slice::from_ref(&f1)).unwrap();
        store.save(&ckpt).unwrap();

        // Modify file
        fs::write(&f1, "fn main() { panic!() }\n").unwrap();

        // Load and rollback
        let ids = store.list().unwrap();
        let loaded = store.load(&ids[0]).unwrap();
        rollback(&loaded).unwrap();

        assert_eq!(fs::read_to_string(&f1).unwrap(), "fn main() {}\n");

        // Clean up checkpoint
        store.delete(&ids[0]).unwrap();
        assert!(store.list().unwrap().is_empty());

        cleanup(&dir);
    }
}
