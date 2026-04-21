// trust-convergence/persistence.rs: Verification state persistence for incremental verification.
//
// Saves and loads verification state between runs so the loop can resume from
// a previous checkpoint and only re-verify functions whose VCs changed.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;
use std::path::Path;

use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::export::{ConvergenceProof, SerializableFrontier};
use crate::integration::VcStatus;
use trust_types::fx::FxHashSet;

/// Errors that can occur during persistence operations.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum PersistenceError {
    #[error("I/O error: {0}")]
    Io(#[from] std::io::Error),
    #[error("serialization error: {0}")]
    Serialization(#[from] serde_json::Error),
    #[error("state file not found: {path}")]
    NotFound { path: String },
    #[error("state version mismatch: expected {expected}, found {found}")]
    VersionMismatch { expected: u32, found: u32 },
}

/// Current state file format version.
const STATE_VERSION: u32 = 1;

/// Serializable VC status for persistence.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub(crate) enum PersistedVcStatus {
    Proved,
    Failed,
    Unknown,
    Timeout,
}

impl From<VcStatus> for PersistedVcStatus {
    fn from(status: VcStatus) -> Self {
        match status {
            VcStatus::Proved => Self::Proved,
            VcStatus::Failed => Self::Failed,
            VcStatus::Unknown => Self::Unknown,
            VcStatus::Timeout => Self::Timeout,
        }
    }
}

impl From<PersistedVcStatus> for VcStatus {
    fn from(status: PersistedVcStatus) -> Self {
        match status {
            PersistedVcStatus::Proved => Self::Proved,
            PersistedVcStatus::Failed => Self::Failed,
            PersistedVcStatus::Unknown => Self::Unknown,
            PersistedVcStatus::Timeout => Self::Timeout,
        }
    }
}

/// Per-function verification state for persistence.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct FunctionState {
    /// Function path (e.g., "crate::module::function").
    pub function_path: String,
    /// Hash of the function's VCs (for change detection).
    pub vc_hash: String,
    /// Per-VC results from the last run.
    pub vc_results: FxHashMap<String, PersistedVcStatus>,
}

/// Full verification state snapshot for persistence between runs.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub(crate) struct VerificationState {
    /// Format version for forward compatibility.
    pub version: u32,
    /// Last completed iteration number.
    pub last_iteration: u32,
    /// Aggregate frontier at the last completed iteration.
    pub frontier: SerializableFrontier,
    /// Per-function verification results.
    pub functions: Vec<FunctionState>,
    /// Convergence proof from the last run (if available).
    pub proof: Option<ConvergenceProof>,
    /// Convergence score at the last iteration (proved / total).
    pub convergence_score: Option<f64>,
}

impl VerificationState {
    /// Create a new, empty verification state.
    #[must_use]
    pub fn new() -> Self {
        Self {
            version: STATE_VERSION,
            last_iteration: 0,
            frontier: SerializableFrontier {
                trusted: 0,
                certified: 0,
                runtime_checked: 0,
                failed: 0,
                unknown: 0,
            },
            functions: Vec::new(),
            proof: None,
            convergence_score: None,
        }
    }

    /// Number of functions tracked.
    #[must_use]
    pub fn function_count(&self) -> usize {
        self.functions.len()
    }

    /// Look up a function by path.
    #[must_use]
    pub fn find_function(&self, path: &str) -> Option<&FunctionState> {
        self.functions.iter().find(|f| f.function_path == path)
    }
}

impl Default for VerificationState {
    fn default() -> Self {
        Self::new()
    }
}

/// Save verification state to a JSON file.
///
/// Creates parent directories if they do not exist.
///
/// # Errors
///
/// Returns an error if the file cannot be written or serialization fails.
pub(crate) fn save_state(path: &Path, state: &VerificationState) -> Result<(), PersistenceError> {
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent)?;
    }
    let json = serde_json::to_string_pretty(state)?;
    std::fs::write(path, json)?;
    Ok(())
}

/// Load verification state from a JSON file.
///
/// # Errors
///
/// Returns an error if:
/// - The file does not exist
/// - The file cannot be read
/// - The JSON is malformed
/// - The state version is incompatible
pub(crate) fn load_state(path: &Path) -> Result<VerificationState, PersistenceError> {
    if !path.exists() {
        return Err(PersistenceError::NotFound { path: path.display().to_string() });
    }
    let json = std::fs::read_to_string(path)?;
    let state: VerificationState = serde_json::from_str(&json)?;

    if state.version != STATE_VERSION {
        return Err(PersistenceError::VersionMismatch {
            expected: STATE_VERSION,
            found: state.version,
        });
    }

    Ok(state)
}

/// What changed between a saved state and a current set of function hashes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct StateDelta {
    /// Functions whose VC hash changed (need re-verification).
    pub changed: Vec<String>,
    /// Functions that are new (not in the saved state).
    pub added: Vec<String>,
    /// Functions that were in the saved state but are no longer present.
    pub removed: Vec<String>,
    /// Functions whose VC hash is unchanged (can skip re-verification).
    pub unchanged: Vec<String>,
}

impl StateDelta {
    /// True if nothing changed (all functions unchanged, none added or removed).
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.changed.is_empty() && self.added.is_empty() && self.removed.is_empty()
    }

    /// Total number of functions that need re-verification.
    #[must_use]
    pub fn reverify_count(&self) -> usize {
        self.changed.len() + self.added.len()
    }
}

/// Compare a saved state with current function hashes to determine what changed.
///
/// `current_hashes` maps function path to its current VC hash.
#[must_use]
pub(crate) fn compute_delta(
    saved: &VerificationState,
    current_hashes: &FxHashMap<String, String>,
) -> StateDelta {
    let saved_map: FxHashMap<&str, &str> = saved
        .functions
        .iter()
        .map(|f| (f.function_path.as_str(), f.vc_hash.as_str()))
        .collect();

    let mut changed = Vec::new();
    let mut added = Vec::new();
    let mut unchanged = Vec::new();

    for (path, current_hash) in current_hashes {
        match saved_map.get(path.as_str()) {
            Some(&saved_hash) if saved_hash == current_hash => {
                unchanged.push(path.clone());
            }
            Some(_) => {
                changed.push(path.clone());
            }
            None => {
                added.push(path.clone());
            }
        }
    }

    let current_paths: FxHashSet<&str> =
        current_hashes.keys().map(String::as_str).collect();
    let mut removed: Vec<String> = saved
        .functions
        .iter()
        .filter(|f| !current_paths.contains(f.function_path.as_str()))
        .map(|f| f.function_path.clone())
        .collect();

    // Sort all vectors for deterministic output.
    changed.sort();
    added.sort();
    removed.sort();
    unchanged.sort();

    StateDelta { changed, added, removed, unchanged }
}

/// Strategy for incremental verification based on a state delta.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct IncrementalStrategy {
    /// Functions to re-verify (changed + added).
    pub to_verify: Vec<String>,
    /// Functions to skip (unchanged from saved state).
    pub to_skip: Vec<String>,
    /// Functions removed since the last run (informational).
    pub removed: Vec<String>,
    /// Whether this is a full reverification (no saved state or everything changed).
    pub is_full_reverification: bool,
}

impl IncrementalStrategy {
    /// True if there is nothing to verify.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.to_verify.is_empty()
    }
}

/// Build an incremental verification strategy from a state delta.
///
/// If the delta shows no changes, returns a strategy with an empty to_verify list.
/// If there is no saved state (all functions are "added"), marks as full reverification.
#[must_use]
pub(crate) fn incremental_strategy(delta: &StateDelta) -> IncrementalStrategy {
    let mut to_verify: Vec<String> = delta
        .changed
        .iter()
        .chain(delta.added.iter())
        .cloned()
        .collect();
    to_verify.sort();

    let is_full = delta.unchanged.is_empty() && !to_verify.is_empty();

    IncrementalStrategy {
        to_verify,
        to_skip: delta.unchanged.clone(),
        removed: delta.removed.clone(),
        is_full_reverification: is_full,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_state(functions: Vec<(&str, &str)>) -> VerificationState {
        let mut state = VerificationState::new();
        for (path, hash) in functions {
            state.functions.push(FunctionState {
                function_path: path.to_string(),
                vc_hash: hash.to_string(),
                vc_results: FxHashMap::default(),
            });
        }
        state
    }

    // -- VerificationState tests --

    #[test]
    fn test_new_state_is_empty() {
        let state = VerificationState::new();
        assert_eq!(state.version, STATE_VERSION);
        assert_eq!(state.last_iteration, 0);
        assert_eq!(state.function_count(), 0);
        assert!(state.proof.is_none());
        assert!(state.convergence_score.is_none());
    }

    #[test]
    fn test_find_function() {
        let state = make_state(vec![("foo::bar", "abc123"), ("baz::qux", "def456")]);
        assert!(state.find_function("foo::bar").is_some());
        assert!(state.find_function("baz::qux").is_some());
        assert!(state.find_function("nonexistent").is_none());
    }

    // -- Persistence I/O tests --

    #[test]
    fn test_save_and_load_state() {
        let dir = std::env::temp_dir().join("trust_convergence_test_save_load");
        let _ = std::fs::remove_dir_all(&dir);
        let path = dir.join("state.json");

        let mut state = make_state(vec![("foo::bar", "abc123")]);
        state.last_iteration = 5;
        state.convergence_score = Some(0.75);

        save_state(&path, &state).expect("save");
        let loaded = load_state(&path).expect("load");

        assert_eq!(loaded.version, state.version);
        assert_eq!(loaded.last_iteration, 5);
        assert_eq!(loaded.function_count(), 1);
        assert_eq!(loaded.find_function("foo::bar").expect("fn").vc_hash, "abc123");
        assert!((loaded.convergence_score.expect("score") - 0.75).abs() < f64::EPSILON);

        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_load_nonexistent_file() {
        let path = std::env::temp_dir().join("trust_convergence_nonexistent.json");
        let _ = std::fs::remove_file(&path);
        assert!(matches!(
            load_state(&path),
            Err(PersistenceError::NotFound { .. })
        ));
    }

    #[test]
    fn test_load_invalid_json() {
        let dir = std::env::temp_dir().join("trust_convergence_test_invalid_json");
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).expect("mkdir");
        let path = dir.join("state.json");
        std::fs::write(&path, "not valid json").expect("write");

        assert!(matches!(
            load_state(&path),
            Err(PersistenceError::Serialization(_))
        ));

        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_load_version_mismatch() {
        let dir = std::env::temp_dir().join("trust_convergence_test_version_mismatch");
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).expect("mkdir");
        let path = dir.join("state.json");

        let mut state = VerificationState::new();
        state.version = 999;
        let json = serde_json::to_string_pretty(&state).expect("serialize");
        std::fs::write(&path, json).expect("write");

        assert!(matches!(
            load_state(&path),
            Err(PersistenceError::VersionMismatch { expected: 1, found: 999 })
        ));

        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_save_creates_parent_directories() {
        let dir = std::env::temp_dir().join("trust_convergence_test_nested/sub/dir");
        let _ = std::fs::remove_dir_all(
            std::env::temp_dir().join("trust_convergence_test_nested"),
        );
        let path = dir.join("state.json");

        let state = VerificationState::new();
        save_state(&path, &state).expect("save with nested dirs");
        assert!(path.exists());

        let _ = std::fs::remove_dir_all(
            std::env::temp_dir().join("trust_convergence_test_nested"),
        );
    }

    // -- StateDelta tests --

    #[test]
    fn test_delta_no_changes() {
        let saved = make_state(vec![("foo::bar", "abc"), ("baz::qux", "def")]);
        let current: FxHashMap<String, String> = [
            ("foo::bar".to_string(), "abc".to_string()),
            ("baz::qux".to_string(), "def".to_string()),
        ]
        .into_iter()
        .collect();

        let delta = compute_delta(&saved, &current);
        assert!(delta.is_empty());
        assert!(delta.changed.is_empty());
        assert!(delta.added.is_empty());
        assert!(delta.removed.is_empty());
        assert_eq!(delta.unchanged.len(), 2);
        assert_eq!(delta.reverify_count(), 0);
    }

    #[test]
    fn test_delta_function_changed() {
        let saved = make_state(vec![("foo::bar", "abc")]);
        let current: FxHashMap<String, String> =
            [("foo::bar".to_string(), "xyz".to_string())].into_iter().collect();

        let delta = compute_delta(&saved, &current);
        assert_eq!(delta.changed, vec!["foo::bar"]);
        assert!(delta.added.is_empty());
        assert!(delta.removed.is_empty());
        assert!(delta.unchanged.is_empty());
        assert_eq!(delta.reverify_count(), 1);
    }

    #[test]
    fn test_delta_function_added() {
        let saved = make_state(vec![("foo::bar", "abc")]);
        let current: FxHashMap<String, String> = [
            ("foo::bar".to_string(), "abc".to_string()),
            ("new::func".to_string(), "new_hash".to_string()),
        ]
        .into_iter()
        .collect();

        let delta = compute_delta(&saved, &current);
        assert!(delta.changed.is_empty());
        assert_eq!(delta.added, vec!["new::func"]);
        assert!(delta.removed.is_empty());
        assert_eq!(delta.unchanged, vec!["foo::bar"]);
        assert_eq!(delta.reverify_count(), 1);
    }

    #[test]
    fn test_delta_function_removed() {
        let saved = make_state(vec![("foo::bar", "abc"), ("old::func", "old_hash")]);
        let current: FxHashMap<String, String> =
            [("foo::bar".to_string(), "abc".to_string())].into_iter().collect();

        let delta = compute_delta(&saved, &current);
        assert!(delta.changed.is_empty());
        assert!(delta.added.is_empty());
        assert_eq!(delta.removed, vec!["old::func"]);
        assert_eq!(delta.unchanged, vec!["foo::bar"]);
    }

    #[test]
    fn test_delta_mixed_changes() {
        let saved = make_state(vec![
            ("unchanged::func", "hash1"),
            ("changed::func", "old_hash"),
            ("removed::func", "hash3"),
        ]);
        let current: FxHashMap<String, String> = [
            ("unchanged::func".to_string(), "hash1".to_string()),
            ("changed::func".to_string(), "new_hash".to_string()),
            ("added::func".to_string(), "hash4".to_string()),
        ]
        .into_iter()
        .collect();

        let delta = compute_delta(&saved, &current);
        assert_eq!(delta.changed, vec!["changed::func"]);
        assert_eq!(delta.added, vec!["added::func"]);
        assert_eq!(delta.removed, vec!["removed::func"]);
        assert_eq!(delta.unchanged, vec!["unchanged::func"]);
        assert_eq!(delta.reverify_count(), 2);
        assert!(!delta.is_empty());
    }

    // -- IncrementalStrategy tests --

    #[test]
    fn test_strategy_no_changes() {
        let delta = StateDelta {
            changed: vec![],
            added: vec![],
            removed: vec![],
            unchanged: vec!["foo::bar".into()],
        };
        let strategy = incremental_strategy(&delta);
        assert!(strategy.is_empty());
        assert!(!strategy.is_full_reverification);
        assert_eq!(strategy.to_skip, vec!["foo::bar"]);
    }

    #[test]
    fn test_strategy_all_new() {
        let delta = StateDelta {
            changed: vec![],
            added: vec!["foo::bar".into(), "baz::qux".into()],
            removed: vec![],
            unchanged: vec![],
        };
        let strategy = incremental_strategy(&delta);
        assert_eq!(strategy.to_verify.len(), 2);
        assert!(strategy.is_full_reverification);
        assert!(strategy.to_skip.is_empty());
    }

    #[test]
    fn test_strategy_mixed() {
        let delta = StateDelta {
            changed: vec!["changed::func".into()],
            added: vec!["added::func".into()],
            removed: vec!["removed::func".into()],
            unchanged: vec!["unchanged::func".into()],
        };
        let strategy = incremental_strategy(&delta);
        assert_eq!(strategy.to_verify, vec!["added::func", "changed::func"]);
        assert_eq!(strategy.to_skip, vec!["unchanged::func"]);
        assert_eq!(strategy.removed, vec!["removed::func"]);
        assert!(!strategy.is_full_reverification);
    }

    // -- PersistedVcStatus tests --

    #[test]
    fn test_vc_status_roundtrip() {
        let statuses = vec![
            VcStatus::Proved,
            VcStatus::Failed,
            VcStatus::Unknown,
            VcStatus::Timeout,
        ];
        for status in statuses {
            let persisted = PersistedVcStatus::from(status);
            let back = VcStatus::from(persisted);
            assert_eq!(status, back);
        }
    }

    #[test]
    fn test_persisted_status_serde() {
        let status = PersistedVcStatus::Proved;
        let json = serde_json::to_string(&status).expect("serialize");
        let back: PersistedVcStatus = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(status, back);
    }

    // -- FunctionState tests --

    #[test]
    fn test_function_state_with_vc_results() {
        let mut vc_results = FxHashMap::default();
        vc_results.insert("div_by_zero".to_string(), PersistedVcStatus::Proved);
        vc_results.insert("index_bounds".to_string(), PersistedVcStatus::Failed);

        let fs = FunctionState {
            function_path: "foo::bar".to_string(),
            vc_hash: "abc123".to_string(),
            vc_results,
        };

        let json = serde_json::to_string(&fs).expect("serialize");
        let back: FunctionState = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(fs, back);
        assert_eq!(back.vc_results.len(), 2);
    }

    // -- Full state JSON roundtrip --

    #[test]
    fn test_full_state_json_roundtrip() {
        let mut state = make_state(vec![("foo::bar", "abc123"), ("baz::qux", "def456")]);
        state.last_iteration = 3;
        state.convergence_score = Some(0.85);

        let json = serde_json::to_string_pretty(&state).expect("serialize");
        let back: VerificationState = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(state, back);
    }
}
