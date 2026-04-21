// trust-convergence/snapshot.rs: Source file snapshot tracking per iteration.
//
// Stores file contents at each iteration so the loop can roll back source
// changes when monotonicity is violated.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;
use std::path::{Path, PathBuf};

use thiserror::Error;

/// Errors that can occur during snapshot operations.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum SnapshotError {
    #[error("no snapshots to roll back to")]
    NoHistory,
    #[error("rollback index {index} out of range (history length: {len})")]
    IndexOutOfRange { index: usize, len: usize },
}

/// A snapshot of source file contents at one iteration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SourceSnapshot {
    files: FxHashMap<PathBuf, String>,
    iteration: u32,
}

impl SourceSnapshot {
    /// Create a new snapshot for the given iteration.
    #[must_use]
    pub fn new(iteration: u32) -> Self {
        Self { files: FxHashMap::default(), iteration }
    }

    /// Create a snapshot from an existing file map.
    #[must_use]
    pub fn from_files(iteration: u32, files: FxHashMap<PathBuf, String>) -> Self {
        Self { files, iteration }
    }

    /// Record the contents of a single file.
    pub fn add_file(&mut self, path: impl Into<PathBuf>, contents: impl Into<String>) {
        self.files.insert(path.into(), contents.into());
    }

    /// Retrieve the contents of a file, if present.
    #[must_use]
    pub fn get_file(&self, path: &Path) -> Option<&str> {
        self.files.get(path).map(String::as_str)
    }

    /// All files tracked in this snapshot.
    #[must_use]
    pub fn files(&self) -> &FxHashMap<PathBuf, String> {
        &self.files
    }

    /// The iteration number for this snapshot.
    #[must_use]
    pub fn iteration(&self) -> u32 {
        self.iteration
    }

    /// Number of files in this snapshot.
    #[must_use]
    pub fn file_count(&self) -> usize {
        self.files.len()
    }

    /// True if this snapshot tracks no files.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.files.is_empty()
    }
}

/// History of source snapshots across iterations with rollback support.
#[derive(Debug, Clone)]
pub(crate) struct SnapshotHistory {
    snapshots: Vec<SourceSnapshot>,
}

impl SnapshotHistory {
    /// Create an empty history.
    #[must_use]
    pub fn new() -> Self {
        Self { snapshots: Vec::new() }
    }

    /// Record a new snapshot.
    pub fn push(&mut self, snapshot: SourceSnapshot) {
        self.snapshots.push(snapshot);
    }

    /// Number of snapshots stored.
    #[must_use]
    pub fn len(&self) -> usize {
        self.snapshots.len()
    }

    /// True if no snapshots have been recorded.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.snapshots.is_empty()
    }

    /// The most recent snapshot, if any.
    #[must_use]
    pub fn latest(&self) -> Option<&SourceSnapshot> {
        self.snapshots.last()
    }

    /// The snapshot immediately before the latest, if any.
    #[must_use]
    pub fn previous(&self) -> Option<&SourceSnapshot> {
        if self.snapshots.len() >= 2 {
            Some(&self.snapshots[self.snapshots.len() - 2])
        } else {
            None
        }
    }

    /// Get a snapshot by index (0 = first recorded).
    #[must_use]
    pub fn get(&self, index: usize) -> Option<&SourceSnapshot> {
        self.snapshots.get(index)
    }

    /// Roll back to the previous snapshot, removing the latest.
    ///
    /// Returns the snapshot that was rolled back to (now the new latest).
    pub fn rollback(&mut self) -> Result<&SourceSnapshot, SnapshotError> {
        if self.snapshots.len() < 2 {
            return Err(SnapshotError::NoHistory);
        }
        self.snapshots.pop();
        // SAFETY: We checked len >= 2 above and popped one, so len >= 1.
        Ok(self.snapshots.last()
            .unwrap_or_else(|| unreachable!("snapshot vec empty after pop with len >= 2")))
    }

    /// Roll back to a specific snapshot by index, removing all later snapshots.
    ///
    /// Returns the snapshot at the target index (now the new latest).
    pub fn rollback_to(&mut self, index: usize) -> Result<&SourceSnapshot, SnapshotError> {
        if index >= self.snapshots.len() {
            return Err(SnapshotError::IndexOutOfRange {
                index,
                len: self.snapshots.len(),
            });
        }
        self.snapshots.truncate(index + 1);
        // SAFETY: We validated index < len, so truncate(index+1) leaves at least 1 element.
        Ok(self.snapshots.last()
            .unwrap_or_else(|| unreachable!("snapshot vec empty after truncate to valid index")))
    }

    /// All snapshots in chronological order.
    #[must_use]
    pub fn history(&self) -> &[SourceSnapshot] {
        &self.snapshots
    }
}

impl Default for SnapshotHistory {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_source_snapshot_empty() {
        let snap = SourceSnapshot::new(0);
        assert!(snap.is_empty());
        assert_eq!(snap.file_count(), 0);
        assert_eq!(snap.iteration(), 0);
    }

    #[test]
    fn test_source_snapshot_add_and_get() {
        let mut snap = SourceSnapshot::new(1);
        snap.add_file("src/main.rs", "fn main() {}");
        snap.add_file("src/lib.rs", "pub mod foo;");

        assert_eq!(snap.file_count(), 2);
        assert!(!snap.is_empty());
        assert_eq!(snap.get_file(Path::new("src/main.rs")), Some("fn main() {}"));
        assert_eq!(snap.get_file(Path::new("src/lib.rs")), Some("pub mod foo;"));
        assert_eq!(snap.get_file(Path::new("nonexistent.rs")), None);
    }

    #[test]
    fn test_source_snapshot_from_files() {
        let mut files = FxHashMap::default();
        files.insert(PathBuf::from("a.rs"), "a".to_string());
        files.insert(PathBuf::from("b.rs"), "b".to_string());

        let snap = SourceSnapshot::from_files(5, files);
        assert_eq!(snap.iteration(), 5);
        assert_eq!(snap.file_count(), 2);
        assert_eq!(snap.get_file(Path::new("a.rs")), Some("a"));
    }

    #[test]
    fn test_snapshot_history_push_and_latest() {
        let mut history = SnapshotHistory::new();
        assert!(history.is_empty());
        assert!(history.latest().is_none());

        let snap0 = SourceSnapshot::new(0);
        history.push(snap0);
        assert_eq!(history.len(), 1);
        assert_eq!(history.latest().expect("latest").iteration(), 0);
        assert!(history.previous().is_none());

        let snap1 = SourceSnapshot::new(1);
        history.push(snap1);
        assert_eq!(history.len(), 2);
        assert_eq!(history.latest().expect("latest").iteration(), 1);
        assert_eq!(history.previous().expect("previous").iteration(), 0);
    }

    #[test]
    fn test_snapshot_history_rollback() {
        let mut history = SnapshotHistory::new();
        let mut snap0 = SourceSnapshot::new(0);
        snap0.add_file("a.rs", "version0");
        history.push(snap0);

        let mut snap1 = SourceSnapshot::new(1);
        snap1.add_file("a.rs", "version1");
        history.push(snap1);

        assert_eq!(history.len(), 2);
        let rolled_back = history.rollback().expect("rollback");
        assert_eq!(rolled_back.iteration(), 0);
        assert_eq!(rolled_back.get_file(Path::new("a.rs")), Some("version0"));
        assert_eq!(history.len(), 1);
    }

    #[test]
    fn test_snapshot_history_rollback_no_history() {
        let mut history = SnapshotHistory::new();
        assert!(matches!(history.rollback(), Err(SnapshotError::NoHistory)));

        history.push(SourceSnapshot::new(0));
        assert!(matches!(history.rollback(), Err(SnapshotError::NoHistory)));
    }

    #[test]
    fn test_snapshot_history_rollback_to() {
        let mut history = SnapshotHistory::new();
        for i in 0..5 {
            let mut snap = SourceSnapshot::new(i);
            snap.add_file("a.rs", format!("v{i}"));
            history.push(snap);
        }
        assert_eq!(history.len(), 5);

        let target = history.rollback_to(2).expect("rollback_to");
        assert_eq!(target.iteration(), 2);
        assert_eq!(target.get_file(Path::new("a.rs")), Some("v2"));
        assert_eq!(history.len(), 3);
    }

    #[test]
    fn test_snapshot_history_rollback_to_out_of_range() {
        let mut history = SnapshotHistory::new();
        history.push(SourceSnapshot::new(0));
        assert!(matches!(
            history.rollback_to(5),
            Err(SnapshotError::IndexOutOfRange { index: 5, len: 1 })
        ));
    }

    #[test]
    fn test_snapshot_history_get_by_index() {
        let mut history = SnapshotHistory::new();
        history.push(SourceSnapshot::new(10));
        history.push(SourceSnapshot::new(20));

        assert_eq!(history.get(0).expect("get 0").iteration(), 10);
        assert_eq!(history.get(1).expect("get 1").iteration(), 20);
        assert!(history.get(2).is_none());
    }
}
