//! trust-config: Unified configuration loader with source tracking
//!
//! Provides a high-level API for loading configuration through the full
//! resolution stack (defaults -> profile -> file -> env), with provenance
//! tracking so callers know where each setting originated.
//!
//! Author: Andrew Yates <andrew@andrewdyates.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;
use std::path::{Path, PathBuf};

use crate::TrustConfig;
use crate::env_override::apply_env_overrides;
use crate::file_config::{find_config_file, load_config, merge_configs};
use crate::profile::{VerificationProfile, apply_profile};
use crate::validation::{ConfigWarning, Severity, validate_config};

/// tRust: Where a configuration value originated.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum ConfigSource {
    /// Came from `TrustConfig::default()`.
    Default,
    /// Came from a named verification profile.
    Profile(String),
    /// Came from a TOML config file at the given path.
    File(PathBuf),
    /// Came from a `TRUST_*` environment variable.
    Environment(String),
}

impl std::fmt::Display for ConfigSource {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Default => write!(f, "default"),
            Self::Profile(name) => write!(f, "profile:{name}"),
            Self::File(path) => write!(f, "file:{}", path.display()),
            Self::Environment(var) => write!(f, "env:{var}"),
        }
    }
}

/// tRust: A resolved configuration with provenance tracking.
///
/// Wraps a `TrustConfig` along with metadata about how it was resolved:
/// which sources contributed, which config file was found, and any
/// validation warnings.
#[derive(Debug, Clone)]
pub struct ResolvedConfig {
    /// The final merged configuration.
    pub config: TrustConfig,
    /// Which source each field's value came from.
    pub sources: FxHashMap<String, ConfigSource>,
    /// Path to the config file used, if any.
    pub config_file: Option<PathBuf>,
    /// Profile applied, if any.
    pub profile: Option<VerificationProfile>,
    /// Validation warnings (non-fatal). Empty if valid.
    pub warnings: Vec<ConfigWarning>,
}

impl ResolvedConfig {
    /// Whether the resolved config has any error-severity validation findings.
    #[must_use]
    pub fn has_errors(&self) -> bool {
        self.warnings.iter().any(|w| w.severity == Severity::Error)
    }

    /// Whether the resolved config has any warnings (including errors).
    #[must_use]
    pub fn has_warnings(&self) -> bool {
        !self.warnings.is_empty()
    }

    /// Get the source of a specific field by name.
    #[must_use]
    pub fn source_of(&self, field: &str) -> Option<&ConfigSource> {
        self.sources.get(field)
    }

    /// Human-readable summary of where this config came from.
    #[must_use]
    pub fn summary(&self) -> String {
        let mut parts = Vec::new();
        if let Some(ref path) = self.config_file {
            parts.push(format!("file: {}", path.display()));
        }
        if let Some(ref profile) = self.profile {
            parts.push(format!("profile: {}", profile.name()));
        }
        let env_count =
            self.sources.values().filter(|s| matches!(s, ConfigSource::Environment(_))).count();
        if env_count > 0 {
            parts.push(format!("{env_count} env override(s)"));
        }
        if parts.is_empty() { "defaults only".to_string() } else { parts.join(", ") }
    }
}

/// tRust: Load configuration through the full resolution stack with tracking.
///
/// Resolution order (each layer overrides the previous):
/// 1. `TrustConfig::default()`
/// 2. Profile (if specified)
/// 3. Config file (searched up from `start_dir`)
/// 4. Environment variables (`TRUST_*`)
///
/// Returns a `ResolvedConfig` with the final config, source provenance
/// per field, and any validation warnings.
#[must_use]
pub fn resolve_config(start_dir: &Path, profile: Option<VerificationProfile>) -> ResolvedConfig {
    let defaults = TrustConfig::default();
    let mut config = defaults.clone();
    let mut sources = initial_sources();

    // Step 2: Apply profile
    if let Some(p) = profile {
        let before = config.clone();
        apply_profile(&mut config, p);
        let profile_source = ConfigSource::Profile(p.name().to_string());
        track_changes(&before, &config, &profile_source, &mut sources);
    }

    // Step 3: Merge file config
    let config_file = find_config_file(start_dir);
    if let Some(ref path) = config_file
        && let Ok(file_config) = load_config(path)
    {
        let before = config.clone();
        config = merge_configs(config, file_config);
        let file_source = ConfigSource::File(path.clone());
        track_changes(&before, &config, &file_source, &mut sources);
    }

    // Step 4: Apply env overrides
    let before_env = config.clone();
    apply_env_overrides(&mut config);
    track_env_changes(&before_env, &config, &mut sources);

    // Validate
    let warnings = match validate_config(&config) {
        Ok(()) => Vec::new(),
        Err(w) => w,
    };

    ResolvedConfig { config, sources, config_file, profile, warnings }
}

/// tRust: Load configuration from an explicit file path (no directory search).
///
/// Useful when the caller already knows the config file location.
/// Still applies profile and env overrides on top.
pub fn resolve_config_from_file(
    config_path: &Path,
    profile: Option<VerificationProfile>,
) -> Result<ResolvedConfig, crate::ConfigError> {
    let mut config = TrustConfig::default();
    let mut sources = initial_sources();

    // Apply profile
    if let Some(p) = profile {
        let before = config.clone();
        apply_profile(&mut config, p);
        let profile_source = ConfigSource::Profile(p.name().to_string());
        track_changes(&before, &config, &profile_source, &mut sources);
    }

    // Load explicit file
    let file_config = load_config(config_path)?;
    let before = config.clone();
    config = merge_configs(config, file_config);
    let file_source = ConfigSource::File(config_path.to_path_buf());
    track_changes(&before, &config, &file_source, &mut sources);

    // Env overrides
    let before_env = config.clone();
    apply_env_overrides(&mut config);
    track_env_changes(&before_env, &config, &mut sources);

    let warnings = match validate_config(&config) {
        Ok(()) => Vec::new(),
        Err(w) => w,
    };

    Ok(ResolvedConfig {
        config,
        sources,
        config_file: Some(config_path.to_path_buf()),
        profile,
        warnings,
    })
}

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

/// All fields start as Default source.
fn initial_sources() -> FxHashMap<String, ConfigSource> {
    let mut m = FxHashMap::default();
    for field in ALL_FIELDS {
        m.insert((*field).to_string(), ConfigSource::Default);
    }
    m
}

/// Config field names we track provenance for.
const ALL_FIELDS: &[&str] = &[
    "enabled",
    "level",
    "timeout_ms",
    "skip_functions",
    "verify_functions",
    "solver",
    "proof_level",
    "cache_dir",
    "parallel",
    "strengthen",
    "cegar",
    "certify",
    "tv",
];

/// Compare two configs field-by-field and update sources for changed fields.
fn track_changes(
    before: &TrustConfig,
    after: &TrustConfig,
    source: &ConfigSource,
    sources: &mut FxHashMap<String, ConfigSource>,
) {
    if before.enabled != after.enabled {
        sources.insert("enabled".to_string(), source.clone());
    }
    if before.level != after.level {
        sources.insert("level".to_string(), source.clone());
    }
    if before.timeout_ms != after.timeout_ms {
        sources.insert("timeout_ms".to_string(), source.clone());
    }
    if before.skip_functions != after.skip_functions {
        sources.insert("skip_functions".to_string(), source.clone());
    }
    if before.verify_functions != after.verify_functions {
        sources.insert("verify_functions".to_string(), source.clone());
    }
    if before.solver != after.solver {
        sources.insert("solver".to_string(), source.clone());
    }
    if before.proof_level != after.proof_level {
        sources.insert("proof_level".to_string(), source.clone());
    }
    if before.cache_dir != after.cache_dir {
        sources.insert("cache_dir".to_string(), source.clone());
    }
    if before.parallel != after.parallel {
        sources.insert("parallel".to_string(), source.clone());
    }
    if before.strengthen != after.strengthen {
        sources.insert("strengthen".to_string(), source.clone());
    }
    if before.cegar != after.cegar {
        sources.insert("cegar".to_string(), source.clone());
    }
    if before.certify != after.certify {
        sources.insert("certify".to_string(), source.clone());
    }
    if before.tv != after.tv {
        sources.insert("tv".to_string(), source.clone());
    }
}

/// Track environment variable changes by mapping field names to env var names.
fn track_env_changes(
    before: &TrustConfig,
    after: &TrustConfig,
    sources: &mut FxHashMap<String, ConfigSource>,
) {
    if before.enabled != after.enabled {
        sources
            .insert("enabled".to_string(), ConfigSource::Environment("TRUST_ENABLED".to_string()));
    }
    if before.level != after.level {
        sources.insert(
            "level".to_string(),
            ConfigSource::Environment("TRUST_VERIFY_LEVEL".to_string()),
        );
    }
    if before.timeout_ms != after.timeout_ms {
        sources.insert(
            "timeout_ms".to_string(),
            ConfigSource::Environment("TRUST_TIMEOUT_MS".to_string()),
        );
    }
    if before.skip_functions != after.skip_functions {
        sources.insert(
            "skip_functions".to_string(),
            ConfigSource::Environment("TRUST_SKIP_FUNCTIONS".to_string()),
        );
    }
    if before.verify_functions != after.verify_functions {
        sources.insert(
            "verify_functions".to_string(),
            ConfigSource::Environment("TRUST_VERIFY_FUNCTIONS".to_string()),
        );
    }
    if before.solver != after.solver {
        sources.insert("solver".to_string(), ConfigSource::Environment("TRUST_SOLVER".to_string()));
    }
    if before.proof_level != after.proof_level {
        sources.insert(
            "proof_level".to_string(),
            ConfigSource::Environment("TRUST_PROOF_LEVEL".to_string()),
        );
    }
    if before.cache_dir != after.cache_dir {
        sources.insert(
            "cache_dir".to_string(),
            ConfigSource::Environment("TRUST_CACHE_DIR".to_string()),
        );
    }
    if before.parallel != after.parallel {
        sources.insert(
            "parallel".to_string(),
            ConfigSource::Environment("TRUST_PARALLEL".to_string()),
        );
    }
    if before.strengthen != after.strengthen {
        sources.insert(
            "strengthen".to_string(),
            ConfigSource::Environment("TRUST_DISABLE_STRENGTHEN".to_string()),
        );
    }
    if before.cegar != after.cegar {
        sources.insert(
            "cegar".to_string(),
            ConfigSource::Environment("TRUST_DISABLE_CEGAR".to_string()),
        );
    }
    if before.certify != after.certify {
        sources.insert(
            "certify".to_string(),
            ConfigSource::Environment("TRUST_DISABLE_CERTIFY".to_string()),
        );
    }
    if before.tv != after.tv {
        sources.insert("tv".to_string(), ConfigSource::Environment("TRUST_DISABLE_TV".to_string()));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::env;
    use std::fs;

    fn with_env_vars<F: FnOnce()>(vars: &[(&str, &str)], f: F) {
        let _guard = crate::TEST_ENV_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let trust_vars = [
            "TRUST_ENABLED",
            "TRUST_VERIFY_LEVEL",
            "TRUST_TIMEOUT_MS",
            "TRUST_SKIP_FUNCTIONS",
            "TRUST_VERIFY_FUNCTIONS",
            "TRUST_SOLVER",
            "TRUST_PROOF_LEVEL",
            "TRUST_CACHE_DIR",
            "TRUST_PARALLEL",
            "TRUST_DISABLE_STRENGTHEN",
            "TRUST_DISABLE_CEGAR",
            "TRUST_DISABLE_CERTIFY",
            "TRUST_DISABLE_TV",
        ];
        let saved: Vec<_> = trust_vars.iter().map(|k| (*k, std::env::var(k).ok())).collect();
        for k in &trust_vars {
            unsafe { env::remove_var(k) };
        }
        for (k, v) in vars {
            unsafe { env::set_var(k, v) };
        }
        f();
        for (k, _) in vars {
            unsafe { env::remove_var(k) };
        }
        for (k, v) in &saved {
            if let Some(val) = v {
                unsafe { env::set_var(k, val) };
            }
        }
    }

    /// Run a closure with all TRUST_* env vars temporarily cleared.
    fn with_clean_env<F: FnOnce()>(f: F) {
        let _guard = crate::TEST_ENV_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let trust_vars = [
            "TRUST_ENABLED",
            "TRUST_VERIFY_LEVEL",
            "TRUST_TIMEOUT_MS",
            "TRUST_SKIP_FUNCTIONS",
            "TRUST_VERIFY_FUNCTIONS",
            "TRUST_SOLVER",
            "TRUST_PROOF_LEVEL",
            "TRUST_CACHE_DIR",
            "TRUST_PARALLEL",
            "TRUST_DISABLE_STRENGTHEN",
            "TRUST_DISABLE_CEGAR",
            "TRUST_DISABLE_CERTIFY",
            "TRUST_DISABLE_TV",
        ];
        let saved: Vec<_> = trust_vars.iter().map(|k| (*k, std::env::var(k).ok())).collect();
        for k in &trust_vars {
            unsafe { env::remove_var(k) };
        }
        f();
        for (k, v) in &saved {
            if let Some(val) = v {
                unsafe { env::set_var(k, val) };
            }
        }
    }

    // -- ConfigSource Display --

    #[test]
    fn test_config_source_display() {
        assert_eq!(ConfigSource::Default.to_string(), "default");
        assert_eq!(ConfigSource::Profile("quick".to_string()).to_string(), "profile:quick");
        assert_eq!(
            ConfigSource::File(PathBuf::from("/etc/trust.toml")).to_string(),
            "file:/etc/trust.toml"
        );
        assert_eq!(
            ConfigSource::Environment("TRUST_LEVEL".to_string()).to_string(),
            "env:TRUST_LEVEL"
        );
    }

    // -- resolve_config: defaults only --

    #[test]
    fn test_resolve_config_defaults_only() {
        with_clean_env(|| {
            let dir = tempfile::tempdir().expect("should create tempdir");
            let resolved = resolve_config(dir.path(), None);

            assert!(resolved.config.enabled);
            assert_eq!(resolved.config.level, "L0");
            assert_eq!(resolved.config.timeout_ms, 5000);
            assert!(resolved.config_file.is_none());
            assert!(resolved.profile.is_none());
            assert!(!resolved.has_errors());

            // All sources should be Default
            for field in ALL_FIELDS {
                assert_eq!(
                    resolved.source_of(field),
                    Some(&ConfigSource::Default),
                    "field '{field}' should be Default"
                );
            }
        }); // with_clean_env
    }

    // -- resolve_config: with profile --

    #[test]
    fn test_resolve_config_with_profile() {
        with_clean_env(|| {
            let dir = tempfile::tempdir().expect("should create tempdir");
            let resolved = resolve_config(dir.path(), Some(VerificationProfile::Thorough));

            assert_eq!(resolved.config.level, "L1");
            assert_eq!(resolved.config.timeout_ms, 30_000);
            assert_eq!(resolved.profile, Some(VerificationProfile::Thorough));

            // Level and timeout came from profile
            assert_eq!(
                resolved.source_of("level"),
                Some(&ConfigSource::Profile("thorough".to_string()))
            );
            assert_eq!(
                resolved.source_of("timeout_ms"),
                Some(&ConfigSource::Profile("thorough".to_string()))
            );
        });
    }

    // -- resolve_config: with file --

    #[test]
    fn test_resolve_config_with_file() {
        with_clean_env(|| {
            let dir = tempfile::tempdir().expect("should create tempdir");
            let config_path = dir.path().join("trust.toml");
            fs::write(&config_path, "level = \"L2\"\ntimeout_ms = 9999\n")
                .expect("should write file");

            let resolved = resolve_config(dir.path(), None);

            assert_eq!(resolved.config.level, "L2");
            assert_eq!(resolved.config.timeout_ms, 9999);
            assert_eq!(resolved.config_file, Some(config_path.clone()));

            assert_eq!(resolved.source_of("level"), Some(&ConfigSource::File(config_path.clone())));
            assert_eq!(resolved.source_of("timeout_ms"), Some(&ConfigSource::File(config_path)));
            // enabled was not overridden
            assert_eq!(resolved.source_of("enabled"), Some(&ConfigSource::Default));
        });
    }

    // -- resolve_config: file overrides profile --

    #[test]
    fn test_resolve_config_file_overrides_profile() {
        with_clean_env(|| {
            let dir = tempfile::tempdir().expect("should create tempdir");
            let config_path = dir.path().join("trust.toml");
            fs::write(&config_path, "timeout_ms = 7777\n").expect("should write file");

            let resolved = resolve_config(dir.path(), Some(VerificationProfile::Thorough));

            // File override wins for timeout
            assert_eq!(resolved.config.timeout_ms, 7777);
            assert_eq!(resolved.source_of("timeout_ms"), Some(&ConfigSource::File(config_path)));
            // Profile wins for level (file did not set it)
            assert_eq!(resolved.config.level, "L1");
            assert_eq!(
                resolved.source_of("level"),
                Some(&ConfigSource::Profile("thorough".to_string()))
            );
        });
    }

    // -- resolve_config: env overrides everything --

    #[test]
    fn test_resolve_config_env_overrides_all() {
        let dir = tempfile::tempdir().expect("should create tempdir");
        let config_path = dir.path().join("trust.toml");
        fs::write(&config_path, "level = \"L2\"\ntimeout_ms = 9999\n").expect("should write file");

        with_env_vars(&[("TRUST_TIMEOUT_MS", "42")], || {
            let resolved = resolve_config(dir.path(), Some(VerificationProfile::Thorough));

            // Env override wins for timeout
            assert_eq!(resolved.config.timeout_ms, 42);
            assert_eq!(
                resolved.source_of("timeout_ms"),
                Some(&ConfigSource::Environment("TRUST_TIMEOUT_MS".to_string()))
            );
            // File wins for level (env did not set it, file overrode profile)
            assert_eq!(resolved.config.level, "L2");
        });
    }

    // -- resolve_config: validation warnings --

    #[test]
    fn test_resolve_config_validation_warnings() {
        with_clean_env(|| {
            let dir = tempfile::tempdir().expect("should create tempdir");
            let config_path = dir.path().join("trust.toml");
            fs::write(&config_path, "level = \"L99\"\n").expect("should write file");

            let resolved = resolve_config(dir.path(), None);
            assert!(resolved.has_errors());
            assert!(resolved.has_warnings());
            assert!(
                resolved
                    .warnings
                    .iter()
                    .any(|w| w.field == "level" && w.severity == Severity::Error)
            );
        });
    }

    // -- resolve_config_from_file --

    #[test]
    fn test_resolve_config_from_file_success() {
        with_clean_env(|| {
            let dir = tempfile::tempdir().expect("should create tempdir");
            let path = dir.path().join("trust.toml");
            fs::write(&path, "timeout_ms = 4444\nsolver = \"zani\"\n").expect("should write file");

            let resolved = resolve_config_from_file(&path, None).expect("should resolve");
            assert_eq!(resolved.config.timeout_ms, 4444);
            assert_eq!(resolved.config.solver.as_deref(), Some("zani"));
            assert_eq!(resolved.config_file, Some(path.clone()));
            assert_eq!(resolved.source_of("timeout_ms"), Some(&ConfigSource::File(path.clone())));
            assert_eq!(resolved.source_of("solver"), Some(&ConfigSource::File(path)));
        });
    }

    #[test]
    fn test_resolve_config_from_file_missing() {
        let result = resolve_config_from_file(Path::new("/nonexistent/trust.toml"), None);
        assert!(result.is_err());
    }

    #[test]
    fn test_resolve_config_from_file_with_profile() {
        with_clean_env(|| {
            let dir = tempfile::tempdir().expect("should create tempdir");
            let path = dir.path().join("trust.toml");
            fs::write(&path, "timeout_ms = 3333\n").expect("should write file");

            let resolved = resolve_config_from_file(&path, Some(VerificationProfile::Exhaustive))
                .expect("should resolve");

            // File overrides timeout
            assert_eq!(resolved.config.timeout_ms, 3333);
            // Profile sets level (file did not)
            assert_eq!(resolved.config.level, "L2");
            assert_eq!(resolved.profile, Some(VerificationProfile::Exhaustive));
        });
    }

    // -- ResolvedConfig methods --

    #[test]
    fn test_resolved_config_summary_defaults_only() {
        with_clean_env(|| {
            let dir = tempfile::tempdir().expect("should create tempdir");
            let resolved = resolve_config(dir.path(), None);
            assert_eq!(resolved.summary(), "defaults only");
        });
    }

    #[test]
    fn test_resolved_config_summary_with_file_and_profile() {
        with_clean_env(|| {
            let dir = tempfile::tempdir().expect("should create tempdir");
            let config_path = dir.path().join("trust.toml");
            fs::write(&config_path, "level = \"L1\"\n").expect("should write file");

            let resolved = resolve_config(dir.path(), Some(VerificationProfile::Quick));
            let summary = resolved.summary();
            assert!(summary.contains("file:"), "summary should mention file");
            assert!(summary.contains("profile: quick"), "summary should mention profile");
        });
    }

    #[test]
    fn test_resolved_config_summary_with_env() {
        let dir = tempfile::tempdir().expect("should create tempdir");
        with_env_vars(&[("TRUST_SOLVER", "zani")], || {
            let resolved = resolve_config(dir.path(), None);
            let summary = resolved.summary();
            assert!(summary.contains("env override"), "summary should mention env overrides");
        });
    }

    #[test]
    fn test_resolved_config_has_errors_false_for_valid() {
        with_clean_env(|| {
            let dir = tempfile::tempdir().expect("should create tempdir");
            let resolved = resolve_config(dir.path(), None);
            assert!(!resolved.has_errors());
            assert!(!resolved.has_warnings());
        });
    }

    // -- Full stack integration --

    #[test]
    fn test_full_stack_defaults_profile_file_env() {
        let dir = tempfile::tempdir().expect("should create tempdir");
        let config_path = dir.path().join("trust.toml");
        // File sets level and skip_functions
        fs::write(&config_path, "level = \"L2\"\nskip_functions = [\"test_\"]\n")
            .expect("should write file");

        with_env_vars(&[("TRUST_PARALLEL", "16")], || {
            let resolved = resolve_config(dir.path(), Some(VerificationProfile::Thorough));

            // Level: file overrode profile's "L1" with "L2"
            assert_eq!(resolved.config.level, "L2");
            // Timeout: profile set it (file did not override)
            assert_eq!(resolved.config.timeout_ms, 30_000);
            // skip_functions: from file
            assert_eq!(resolved.config.skip_functions, vec!["test_"]);
            // parallel: env override wins over profile
            assert_eq!(resolved.config.parallel, Some(16));

            // Provenance tracking
            assert_eq!(resolved.source_of("level"), Some(&ConfigSource::File(config_path.clone())));
            assert_eq!(
                resolved.source_of("timeout_ms"),
                Some(&ConfigSource::Profile("thorough".to_string()))
            );
            assert_eq!(
                resolved.source_of("skip_functions"),
                Some(&ConfigSource::File(config_path.clone()))
            );
            assert_eq!(
                resolved.source_of("parallel"),
                Some(&ConfigSource::Environment("TRUST_PARALLEL".to_string()))
            );
        });
    }

    #[test]
    fn test_resolve_config_disable_feature_env_tracks_source() {
        let dir = tempfile::tempdir().expect("should create tempdir");
        with_env_vars(&[("TRUST_DISABLE_STRENGTHEN", "1")], || {
            let resolved = resolve_config(dir.path(), None);
            assert!(!resolved.config.strengthen);
            assert_eq!(
                resolved.source_of("strengthen"),
                Some(&ConfigSource::Environment("TRUST_DISABLE_STRENGTHEN".to_string()))
            );
        });
    }

    #[test]
    fn test_source_of_unknown_field() {
        with_clean_env(|| {
            let dir = tempfile::tempdir().expect("should create tempdir");
            let resolved = resolve_config(dir.path(), None);
            assert!(resolved.source_of("nonexistent_field").is_none());
        });
    }

    #[test]
    fn test_config_source_equality() {
        assert_eq!(ConfigSource::Default, ConfigSource::Default);
        assert_ne!(ConfigSource::Default, ConfigSource::Profile("quick".to_string()));
        assert_eq!(
            ConfigSource::Environment("TRUST_LEVEL".to_string()),
            ConfigSource::Environment("TRUST_LEVEL".to_string())
        );
        assert_ne!(
            ConfigSource::Environment("TRUST_LEVEL".to_string()),
            ConfigSource::Environment("TRUST_TIMEOUT".to_string())
        );
    }
}
