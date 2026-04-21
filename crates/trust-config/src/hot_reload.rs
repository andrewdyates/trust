//! trust-config: Hot configuration reload without restart
//!
//! Watches a `trust.toml` file for changes (via mtime polling, no external
//! deps) and provides atomic config swaps, rollback history, and diff
//! computation between config versions.
//!
//! Author: Andrew Yates <andrew@andrewdyates.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};
use std::time::SystemTime;

use thiserror::Error;

use crate::TrustConfig;
use crate::validation::validate_config;

/// tRust: Errors from hot reload operations.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum HotReloadError {
    /// Config file could not be read.
    #[error("failed to read config file '{}': {source}", path.display())]
    Io { path: PathBuf, source: std::io::Error },
    /// Config file contains invalid TOML.
    #[error("failed to parse config file '{}': {source}", path.display())]
    Parse { path: PathBuf, source: toml::de::Error },
    /// New config failed validation.
    #[error("config validation failed: {0}")]
    Validation(String),
    /// Rollback target does not exist in history.
    #[error("rollback target {0} exceeds history depth {1}")]
    RollbackOutOfRange(usize, usize),
}

/// tRust: A single field change between two config versions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConfigChange {
    /// The config field that changed (e.g., "timeout_ms").
    pub key: String,
    /// String representation of the old value.
    pub old_value: String,
    /// String representation of the new value.
    pub new_value: String,
}

/// tRust: A timestamped config snapshot for history tracking.
#[derive(Debug, Clone)]
pub struct ConfigSnapshot {
    /// The config at this point in time.
    pub config: TrustConfig,
    /// When this config was recorded.
    pub timestamp: SystemTime,
}

/// tRust: Tracks config change history with bounded depth.
#[derive(Debug, Clone)]
pub struct ConfigHistory {
    snapshots: Vec<ConfigSnapshot>,
    max_depth: usize,
}

impl ConfigHistory {
    /// Create a new history with the given maximum depth.
    #[must_use]
    pub fn new(max_depth: usize) -> Self {
        Self { snapshots: Vec::new(), max_depth: max_depth.max(1) }
    }

    /// Record a config snapshot. Evicts the oldest entry if at capacity.
    pub fn push(&mut self, config: TrustConfig) {
        if self.snapshots.len() >= self.max_depth {
            self.snapshots.remove(0);
        }
        self.snapshots.push(ConfigSnapshot { config, timestamp: SystemTime::now() });
    }

    /// Number of snapshots currently stored.
    #[must_use]
    pub fn len(&self) -> usize {
        self.snapshots.len()
    }

    /// Whether the history is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.snapshots.is_empty()
    }

    /// Get the nth most recent snapshot (0 = most recent).
    #[must_use]
    pub fn get(&self, n: usize) -> Option<&ConfigSnapshot> {
        if n >= self.snapshots.len() {
            return None;
        }
        let idx = self.snapshots.len() - 1 - n;
        self.snapshots.get(idx)
    }

    /// Get all snapshots, oldest first.
    #[must_use]
    pub fn snapshots(&self) -> &[ConfigSnapshot] {
        &self.snapshots
    }
}

/// Callback type for config change notifications.
type ConfigCallback = Box<dyn Fn(&TrustConfig) + Send>;

/// tRust: Watches a config file for changes and provides atomic reload.
///
/// Uses mtime polling (no external file-watcher deps). The caller drives
/// polling via [`ConfigWatcher::poll_changes`].
pub struct ConfigWatcher {
    path: PathBuf,
    last_mtime: Option<SystemTime>,
    current: Arc<Mutex<TrustConfig>>,
    history: ConfigHistory,
    callbacks: Vec<ConfigCallback>,
}

impl std::fmt::Debug for ConfigWatcher {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ConfigWatcher")
            .field("path", &self.path)
            .field("last_mtime", &self.last_mtime)
            .field("history_len", &self.history.len())
            .field("callbacks_count", &self.callbacks.len())
            .finish()
    }
}

impl ConfigWatcher {
    /// Create a watcher for the given config file path.
    ///
    /// Loads the initial config from the file. If the file does not exist,
    /// starts with `TrustConfig::default()`.
    #[must_use]
    pub fn watch(config_path: &Path) -> Self {
        let (config, mtime) = load_with_mtime(config_path);
        Self {
            path: config_path.to_path_buf(),
            last_mtime: mtime,
            current: Arc::new(Mutex::new(config)),
            history: ConfigHistory::new(32),
            callbacks: Vec::new(),
        }
    }

    /// Create a watcher with a custom history depth.
    #[must_use]
    pub fn watch_with_history(config_path: &Path, history_depth: usize) -> Self {
        let (config, mtime) = load_with_mtime(config_path);
        Self {
            path: config_path.to_path_buf(),
            last_mtime: mtime,
            current: Arc::new(Mutex::new(config)),
            history: ConfigHistory::new(history_depth),
            callbacks: Vec::new(),
        }
    }

    /// Poll for file changes. Returns the new config if the file was modified
    /// since the last poll, or `None` if unchanged.
    ///
    /// On change: validates before applying, records history, fires callbacks.
    pub fn poll_changes(&mut self) -> Option<TrustConfig> {
        let current_mtime = file_mtime(&self.path);

        // No change if mtime is the same (or both absent)
        if current_mtime == self.last_mtime {
            return None;
        }

        // File was modified (or appeared/disappeared)
        let new_config = match load_from_file(&self.path) {
            Ok(cfg) => cfg,
            Err(e) => {
                eprintln!("warning: hot reload failed: {e}");
                return None;
            }
        };

        // Validate before applying
        if let Err(e) = validate_before_apply(&new_config) {
            eprintln!("warning: hot reload rejected: {e}");
            return None;
        }

        self.last_mtime = current_mtime;

        // Record old config in history before swap
        let old_config = {
            let guard = self.current.lock().unwrap_or_else(|e| e.into_inner());
            guard.clone()
        };
        self.history.push(old_config);

        // Atomic swap
        {
            let mut guard = self.current.lock().unwrap_or_else(|e| e.into_inner());
            *guard = new_config.clone();
        }

        // Fire callbacks
        for cb in &self.callbacks {
            cb(&new_config);
        }

        Some(new_config)
    }

    /// Get a clone of the current config.
    #[must_use]
    pub fn current(&self) -> TrustConfig {
        self.current.lock().unwrap_or_else(|e| e.into_inner()).clone()
    }

    /// Get a reference to the config history.
    #[must_use]
    pub fn history(&self) -> &ConfigHistory {
        &self.history
    }

    /// Rollback to the nth previous config (1 = previous, 2 = two ago, etc.).
    ///
    /// Records the current config in history before rolling back.
    pub fn rollback(&mut self, n: usize) -> Result<TrustConfig, HotReloadError> {
        if n == 0 || n > self.history.len() {
            return Err(HotReloadError::RollbackOutOfRange(n, self.history.len()));
        }

        // n=1 means most recent history entry = index 0 in get()
        let target = self
            .history
            .get(n - 1)
            .ok_or(HotReloadError::RollbackOutOfRange(n, self.history.len()))?
            .config
            .clone();

        // Record current in history before swap
        let old = {
            let guard = self.current.lock().unwrap_or_else(|e| e.into_inner());
            guard.clone()
        };
        self.history.push(old);

        // Swap to rollback target
        {
            let mut guard = self.current.lock().unwrap_or_else(|e| e.into_inner());
            *guard = target.clone();
        }

        // Fire callbacks
        for cb in &self.callbacks {
            cb(&target);
        }

        Ok(target)
    }

    /// Register a callback to be called whenever the config changes.
    ///
    /// Callbacks receive a reference to the new config after validation
    /// and atomic swap.
    pub fn on_change(&mut self, callback: impl Fn(&TrustConfig) + Send + 'static) {
        self.callbacks.push(Box::new(callback));
    }

    /// Atomically update the config to a new value. Validates first.
    ///
    /// Records the old config in history. Fires callbacks on success.
    pub fn atomic_update(&mut self, new_config: TrustConfig) -> Result<(), HotReloadError> {
        validate_before_apply(&new_config)?;

        let old = {
            let guard = self.current.lock().unwrap_or_else(|e| e.into_inner());
            guard.clone()
        };
        self.history.push(old);

        {
            let mut guard = self.current.lock().unwrap_or_else(|e| e.into_inner());
            *guard = new_config.clone();
        }

        for cb in &self.callbacks {
            cb(&new_config);
        }

        Ok(())
    }

    /// Get the watched file path.
    #[must_use]
    pub fn path(&self) -> &Path {
        &self.path
    }
}

/// tRust: Validate a config before applying it during hot reload.
///
/// Returns `Ok(())` if the config passes validation, or an error with
/// a description of the validation failures.
pub fn validate_before_apply(config: &TrustConfig) -> Result<(), HotReloadError> {
    if let Err(warnings) = validate_config(config) {
        let errors: Vec<_> =
            warnings.iter().filter(|w| w.severity == crate::validation::Severity::Error).collect();
        if !errors.is_empty() {
            let msg = errors
                .iter()
                .map(|w| format!("{}: {}", w.field, w.message))
                .collect::<Vec<_>>()
                .join("; ");
            return Err(HotReloadError::Validation(msg));
        }
    }
    Ok(())
}

/// tRust: Compute the differences between two configs.
///
/// Returns a list of [`ConfigChange`] entries, one per field that differs.
#[must_use]
pub fn diff_configs(old: &TrustConfig, new: &TrustConfig) -> Vec<ConfigChange> {
    let mut changes = Vec::new();

    if old.enabled != new.enabled {
        changes.push(ConfigChange {
            key: "enabled".to_string(),
            old_value: old.enabled.to_string(),
            new_value: new.enabled.to_string(),
        });
    }

    if old.level != new.level {
        changes.push(ConfigChange {
            key: "level".to_string(),
            old_value: old.level.clone(),
            new_value: new.level.clone(),
        });
    }

    if old.timeout_ms != new.timeout_ms {
        changes.push(ConfigChange {
            key: "timeout_ms".to_string(),
            old_value: old.timeout_ms.to_string(),
            new_value: new.timeout_ms.to_string(),
        });
    }

    if old.skip_functions != new.skip_functions {
        changes.push(ConfigChange {
            key: "skip_functions".to_string(),
            old_value: format!("{:?}", old.skip_functions),
            new_value: format!("{:?}", new.skip_functions),
        });
    }

    if old.verify_functions != new.verify_functions {
        changes.push(ConfigChange {
            key: "verify_functions".to_string(),
            old_value: format!("{:?}", old.verify_functions),
            new_value: format!("{:?}", new.verify_functions),
        });
    }

    if old.solver != new.solver {
        changes.push(ConfigChange {
            key: "solver".to_string(),
            old_value: format!("{:?}", old.solver),
            new_value: format!("{:?}", new.solver),
        });
    }

    if old.proof_level != new.proof_level {
        changes.push(ConfigChange {
            key: "proof_level".to_string(),
            old_value: format!("{:?}", old.proof_level),
            new_value: format!("{:?}", new.proof_level),
        });
    }

    if old.cache_dir != new.cache_dir {
        changes.push(ConfigChange {
            key: "cache_dir".to_string(),
            old_value: format!("{:?}", old.cache_dir),
            new_value: format!("{:?}", new.cache_dir),
        });
    }

    if old.parallel != new.parallel {
        changes.push(ConfigChange {
            key: "parallel".to_string(),
            old_value: format!("{:?}", old.parallel),
            new_value: format!("{:?}", new.parallel),
        });
    }

    if old.strengthen != new.strengthen {
        changes.push(ConfigChange {
            key: "strengthen".to_string(),
            old_value: old.strengthen.to_string(),
            new_value: new.strengthen.to_string(),
        });
    }

    if old.cegar != new.cegar {
        changes.push(ConfigChange {
            key: "cegar".to_string(),
            old_value: old.cegar.to_string(),
            new_value: new.cegar.to_string(),
        });
    }

    if old.certify != new.certify {
        changes.push(ConfigChange {
            key: "certify".to_string(),
            old_value: old.certify.to_string(),
            new_value: new.certify.to_string(),
        });
    }

    if old.tv != new.tv {
        changes.push(ConfigChange {
            key: "tv".to_string(),
            old_value: old.tv.to_string(),
            new_value: new.tv.to_string(),
        });
    }

    // tRust #622: Compare report_format field.
    if old.report_format != new.report_format {
        changes.push(ConfigChange {
            key: "report_format".to_string(),
            old_value: format!("{:?}", old.report_format),
            new_value: format!("{:?}", new.report_format),
        });
    }

    changes
}

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

/// Load config from file, returning a typed error on failure.
fn load_from_file(path: &Path) -> Result<TrustConfig, HotReloadError> {
    let content = std::fs::read_to_string(path)
        .map_err(|e| HotReloadError::Io { path: path.to_path_buf(), source: e })?;
    let config: TrustConfig = toml::from_str(&content)
        .map_err(|e| HotReloadError::Parse { path: path.to_path_buf(), source: e })?;
    Ok(config)
}

/// Get the mtime of a file, or `None` if the file doesn't exist / is unreadable.
fn file_mtime(path: &Path) -> Option<SystemTime> {
    std::fs::metadata(path).ok().and_then(|m| m.modified().ok())
}

/// Load config + mtime together for watcher initialization.
fn load_with_mtime(path: &Path) -> (TrustConfig, Option<SystemTime>) {
    let mtime = file_mtime(path);
    let config = load_from_file(path).unwrap_or_default();
    (config, mtime)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use std::thread;
    use std::time::Duration;

    // -- ConfigHistory tests --

    #[test]
    fn test_history_push_and_get() {
        let mut history = ConfigHistory::new(5);
        assert!(history.is_empty());

        let c1 = TrustConfig { timeout_ms: 1000, ..Default::default() };
        let c2 = TrustConfig { timeout_ms: 2000, ..Default::default() };
        history.push(c1);
        history.push(c2);

        assert_eq!(history.len(), 2);
        assert_eq!(history.get(0).unwrap().config.timeout_ms, 2000); // most recent
        assert_eq!(history.get(1).unwrap().config.timeout_ms, 1000); // older
        assert!(history.get(2).is_none());
    }

    #[test]
    fn test_history_eviction_at_max_depth() {
        let mut history = ConfigHistory::new(2);
        history.push(TrustConfig { timeout_ms: 100, ..Default::default() });
        history.push(TrustConfig { timeout_ms: 200, ..Default::default() });
        history.push(TrustConfig { timeout_ms: 300, ..Default::default() });

        assert_eq!(history.len(), 2);
        // Oldest (100) was evicted
        assert_eq!(history.get(0).unwrap().config.timeout_ms, 300);
        assert_eq!(history.get(1).unwrap().config.timeout_ms, 200);
    }

    #[test]
    fn test_history_min_depth_is_one() {
        let mut history = ConfigHistory::new(0); // should clamp to 1
        history.push(TrustConfig::default());
        history.push(TrustConfig { timeout_ms: 999, ..Default::default() });
        assert_eq!(history.len(), 1);
        assert_eq!(history.get(0).unwrap().config.timeout_ms, 999);
    }

    // -- diff_configs tests --

    #[test]
    fn test_diff_configs_identical() {
        let c = TrustConfig::default();
        let changes = diff_configs(&c, &c);
        assert!(changes.is_empty());
    }

    #[test]
    fn test_diff_configs_all_fields_changed() {
        let old = TrustConfig::default();
        let new = TrustConfig {
            enabled: false,
            level: "L2".to_string(),
            timeout_ms: 99999,
            skip_functions: vec!["skip_me".to_string()],
            verify_functions: vec!["verify_me".to_string()],
            solver: Some("zani".to_string()),
            proof_level: Some("L1".to_string()),
            cache_dir: Some(PathBuf::from("/tmp/cache")),
            parallel: Some(8),
            strengthen: false,
            cegar: false,
            certify: false,
            tv: false,
            report_format: Some("json".to_string()),
        };
        let changes = diff_configs(&old, &new);
        assert_eq!(changes.len(), 14);

        let keys: Vec<&str> = changes.iter().map(|c| c.key.as_str()).collect();
        assert!(keys.contains(&"enabled"));
        assert!(keys.contains(&"level"));
        assert!(keys.contains(&"timeout_ms"));
        assert!(keys.contains(&"skip_functions"));
        assert!(keys.contains(&"verify_functions"));
        assert!(keys.contains(&"solver"));
        assert!(keys.contains(&"proof_level"));
        assert!(keys.contains(&"cache_dir"));
        assert!(keys.contains(&"parallel"));
        assert!(keys.contains(&"strengthen"));
        assert!(keys.contains(&"cegar"));
        assert!(keys.contains(&"certify"));
        assert!(keys.contains(&"tv"));
        assert!(keys.contains(&"report_format"));
    }

    #[test]
    fn test_diff_configs_single_field() {
        let old = TrustConfig::default();
        let new = TrustConfig { timeout_ms: 10_000, ..Default::default() };
        let changes = diff_configs(&old, &new);
        assert_eq!(changes.len(), 1);
        assert_eq!(changes[0].key, "timeout_ms");
        assert_eq!(changes[0].old_value, "5000");
        assert_eq!(changes[0].new_value, "10000");
    }

    // -- validate_before_apply tests --

    #[test]
    fn test_validate_before_apply_valid() {
        let config = TrustConfig::default();
        assert!(validate_before_apply(&config).is_ok());
    }

    #[test]
    fn test_validate_before_apply_rejects_invalid_level() {
        let config = TrustConfig { level: "L99".to_string(), ..Default::default() };
        let err = validate_before_apply(&config).unwrap_err();
        assert!(matches!(err, HotReloadError::Validation(_)));
    }

    #[test]
    fn test_validate_before_apply_allows_warnings() {
        // Low timeout is a warning, not an error — should pass
        let config = TrustConfig { timeout_ms: 50, ..Default::default() };
        assert!(validate_before_apply(&config).is_ok());
    }

    // -- ConfigWatcher tests --

    #[test]
    fn test_watcher_loads_initial_config() {
        let dir = tempfile::tempdir().expect("should create tempdir");
        let path = dir.path().join("trust.toml");
        fs::write(&path, "timeout_ms = 7777\n").expect("should write file");

        let watcher = ConfigWatcher::watch(&path);
        assert_eq!(watcher.current().timeout_ms, 7777);
    }

    #[test]
    fn test_watcher_default_when_file_missing() {
        let watcher = ConfigWatcher::watch(Path::new("/nonexistent/trust.toml"));
        assert_eq!(watcher.current().timeout_ms, 5000);
    }

    #[test]
    fn test_watcher_poll_no_change() {
        let dir = tempfile::tempdir().expect("should create tempdir");
        let path = dir.path().join("trust.toml");
        fs::write(&path, "timeout_ms = 1000\n").expect("should write file");

        let mut watcher = ConfigWatcher::watch(&path);
        // No change since we just loaded
        assert!(watcher.poll_changes().is_none());
    }

    #[test]
    fn test_watcher_poll_detects_change() {
        let dir = tempfile::tempdir().expect("should create tempdir");
        let path = dir.path().join("trust.toml");
        fs::write(&path, "timeout_ms = 1000\n").expect("should write file");

        let mut watcher = ConfigWatcher::watch(&path);
        assert_eq!(watcher.current().timeout_ms, 1000);

        // Sleep to ensure mtime changes (filesystem granularity)
        thread::sleep(Duration::from_millis(50));
        fs::write(&path, "timeout_ms = 2000\n").expect("should write file");

        let new_config = watcher.poll_changes();
        assert!(new_config.is_some());
        assert_eq!(new_config.unwrap().timeout_ms, 2000);
        assert_eq!(watcher.current().timeout_ms, 2000);
    }

    #[test]
    fn test_watcher_poll_rejects_invalid_config() {
        let dir = tempfile::tempdir().expect("should create tempdir");
        let path = dir.path().join("trust.toml");
        fs::write(&path, "timeout_ms = 1000\n").expect("should write file");

        let mut watcher = ConfigWatcher::watch(&path);

        thread::sleep(Duration::from_millis(50));
        // Invalid level is an error-severity finding
        fs::write(&path, "level = \"L99\"\n").expect("should write file");

        // Should be rejected by validation
        assert!(watcher.poll_changes().is_none());
        // Current config unchanged
        assert_eq!(watcher.current().timeout_ms, 1000);
    }

    #[test]
    fn test_watcher_history_populated_on_change() {
        let dir = tempfile::tempdir().expect("should create tempdir");
        let path = dir.path().join("trust.toml");
        fs::write(&path, "timeout_ms = 1000\n").expect("should write file");

        let mut watcher = ConfigWatcher::watch(&path);
        assert!(watcher.history().is_empty());

        thread::sleep(Duration::from_millis(50));
        fs::write(&path, "timeout_ms = 2000\n").expect("should write file");
        watcher.poll_changes();

        assert_eq!(watcher.history().len(), 1);
        assert_eq!(watcher.history().get(0).unwrap().config.timeout_ms, 1000);
    }

    // -- Rollback tests --

    #[test]
    fn test_rollback_to_previous() {
        let dir = tempfile::tempdir().expect("should create tempdir");
        let path = dir.path().join("trust.toml");
        fs::write(&path, "timeout_ms = 1000\n").expect("should write file");

        let mut watcher = ConfigWatcher::watch(&path);

        // Simulate a change via atomic_update (avoids mtime timing issues)
        watcher
            .atomic_update(TrustConfig { timeout_ms: 2000, ..Default::default() })
            .expect("should update");
        assert_eq!(watcher.current().timeout_ms, 2000);

        // Rollback to previous
        let rolled_back = watcher.rollback(1).expect("should rollback");
        assert_eq!(rolled_back.timeout_ms, 1000);
        assert_eq!(watcher.current().timeout_ms, 1000);
    }

    #[test]
    fn test_rollback_out_of_range() {
        let watcher_path = Path::new("/nonexistent/trust.toml");
        let mut watcher = ConfigWatcher::watch(watcher_path);
        let err = watcher.rollback(1).unwrap_err();
        assert!(matches!(err, HotReloadError::RollbackOutOfRange(1, 0)));
    }

    #[test]
    fn test_rollback_zero_is_error() {
        let mut watcher = ConfigWatcher::watch(Path::new("/nonexistent/trust.toml"));
        let err = watcher.rollback(0).unwrap_err();
        assert!(matches!(err, HotReloadError::RollbackOutOfRange(0, _)));
    }

    // -- atomic_update tests --

    #[test]
    fn test_atomic_update_success() {
        let mut watcher = ConfigWatcher::watch(Path::new("/nonexistent/trust.toml"));
        let new = TrustConfig { timeout_ms: 9999, ..Default::default() };
        watcher.atomic_update(new).expect("should update");
        assert_eq!(watcher.current().timeout_ms, 9999);
    }

    #[test]
    fn test_atomic_update_rejects_invalid() {
        let mut watcher = ConfigWatcher::watch(Path::new("/nonexistent/trust.toml"));
        let bad = TrustConfig { level: "INVALID".to_string(), ..Default::default() };
        assert!(watcher.atomic_update(bad).is_err());
        // Original config preserved
        assert_eq!(watcher.current().level, "L0");
    }

    #[test]
    fn test_atomic_update_records_history() {
        let mut watcher = ConfigWatcher::watch(Path::new("/nonexistent/trust.toml"));
        assert!(watcher.history().is_empty());

        watcher
            .atomic_update(TrustConfig { timeout_ms: 1111, ..Default::default() })
            .expect("should update");

        assert_eq!(watcher.history().len(), 1);
        // History entry is the old (default) config
        assert_eq!(watcher.history().get(0).unwrap().config.timeout_ms, 5000);
    }

    // -- on_change callback tests --

    #[test]
    fn test_on_change_callback_fires() {
        let mut watcher = ConfigWatcher::watch(Path::new("/nonexistent/trust.toml"));
        let fired = Arc::new(Mutex::new(false));
        let fired_clone = Arc::clone(&fired);

        watcher.on_change(move |_cfg| {
            *fired_clone.lock().unwrap() = true;
        });

        watcher
            .atomic_update(TrustConfig { timeout_ms: 42, ..Default::default() })
            .expect("should update");

        assert!(*fired.lock().unwrap());
    }

    #[test]
    fn test_on_change_callback_receives_new_config() {
        let mut watcher = ConfigWatcher::watch(Path::new("/nonexistent/trust.toml"));
        let captured_timeout = Arc::new(Mutex::new(0u64));
        let captured = Arc::clone(&captured_timeout);

        watcher.on_change(move |cfg| {
            *captured.lock().unwrap() = cfg.timeout_ms;
        });

        watcher
            .atomic_update(TrustConfig { timeout_ms: 7777, ..Default::default() })
            .expect("should update");

        assert_eq!(*captured_timeout.lock().unwrap(), 7777);
    }

    #[test]
    fn test_callback_not_fired_on_rejected_update() {
        let mut watcher = ConfigWatcher::watch(Path::new("/nonexistent/trust.toml"));
        let fired = Arc::new(Mutex::new(false));
        let fired_clone = Arc::clone(&fired);

        watcher.on_change(move |_cfg| {
            *fired_clone.lock().unwrap() = true;
        });

        // Invalid config should be rejected
        let _ =
            watcher.atomic_update(TrustConfig { level: "BOGUS".to_string(), ..Default::default() });

        assert!(!*fired.lock().unwrap());
    }
}
