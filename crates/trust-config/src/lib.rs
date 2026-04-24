// dead_code audit: crate-level suppression removed (#939)
//! trust-config: Configuration file parser for tRust verification
//!
//! Parses `trust.toml` files following Rust ecosystem conventions (like
//! `clippy.toml`, `rustfmt.toml`). Supports project-level opt-out,
//! verification level selection, timeout tuning, per-function skip/verify
//! patterns, environment variable overrides, validation, and profiles.
//!
//! # Config Resolution Order
//!
//! 1. **Defaults** — `TrustConfig::default()`
//! 2. **Profile** — `VerificationProfile` sets baseline for use case
//! 3. **File** — `trust.toml` found by walking up directory tree
//! 4. **Environment** — `TRUST_*` env vars override everything
//!
//! Author: Andrew Yates <andrew@andrewdyates.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::path::{Path, PathBuf};

use serde::Deserialize;
use thiserror::Error;

// ---------------------------------------------------------------------------
// Report format selection (#622)
// ---------------------------------------------------------------------------

/// tRust #622: Output format for verification reports.
///
/// Controls which report format(s) `cargo trust check` produces.
/// Multiple formats can be enabled simultaneously via `All`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
#[derive(Default)]
pub enum ReportFormat {
    /// Terminal text output (human-readable summary to stderr). Default.
    #[default]
    Text,
    /// JSON report written to `target/trust/report.json`.
    Json,
    /// Self-contained HTML report written to `target/trust/report.html`.
    /// Includes per-function badges, counterexamples, and solver stats.
    Html,
    /// Emit all formats: text + JSON + HTML.
    All,
}

impl ReportFormat {
    /// Parse a report format name from a string (case-insensitive).
    #[must_use]
    pub fn from_name(name: &str) -> Option<Self> {
        match name.to_lowercase().as_str() {
            "text" => Some(Self::Text),
            "json" => Some(Self::Json),
            "html" => Some(Self::Html),
            "all" => Some(Self::All),
            _ => None,
        }
    }

    /// Whether this format includes text output.
    #[must_use]
    pub fn includes_text(self) -> bool {
        matches!(self, Self::Text | Self::All)
    }

    /// Whether this format includes JSON output.
    #[must_use]
    pub fn includes_json(self) -> bool {
        matches!(self, Self::Json | Self::All)
    }

    /// Whether this format includes HTML output.
    #[must_use]
    pub fn includes_html(self) -> bool {
        matches!(self, Self::Html | Self::All)
    }
}

pub(crate) mod env_override;
pub(crate) mod file_config;
pub(crate) mod hot_reload;
pub(crate) mod loader;
pub(crate) mod presets;
pub(crate) mod profile;
pub(crate) mod scope;
pub(crate) mod validation;

// tRust: Re-export key types for convenient access
pub use env_override::apply_env_overrides;
pub use file_config::{default_config, find_config_file, load_config, merge_configs};
pub use hot_reload::{
    ConfigChange, ConfigHistory, ConfigWatcher, HotReloadError, diff_configs, validate_before_apply,
};
pub use loader::{ConfigSource, ResolvedConfig, resolve_config, resolve_config_from_file};
pub use presets::{apply_preset, describe_preset, merge_preset, suggest_preset};
pub use profile::{VerificationProfile, apply_profile};
pub use scope::{ScopeFilter, VerificationScope, filter_functions};
pub use validation::{ConfigWarning, Severity, validate_config};

/// tRust: Errors that can occur during configuration loading.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum ConfigError {
    /// Failed to read the config file from disk.
    #[error("failed to read config file '{}': {source}", path.display())]
    Io { path: PathBuf, source: std::io::Error },
    /// Config file contains invalid TOML or unknown fields.
    #[error("failed to parse config file '{}': {source}", path.display())]
    Parse { path: PathBuf, source: toml::de::Error },
}

/// tRust: Configuration loaded from `trust.toml`.
///
/// All fields have sensible defaults so an empty file yields a valid config
/// with verification enabled at L0 (safety checks).
#[derive(Debug, Clone, PartialEq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TrustConfig {
    /// Whether verification is enabled. Default: `true`.
    #[serde(default = "default_true")]
    pub enabled: bool,

    /// Verification level: "L0" (safety), "L1" (functional), "L2" (domain).
    /// Default: "L0".
    #[serde(default = "default_level")]
    pub level: String,

    /// Per-function timeout in milliseconds. Default: 5000.
    #[serde(default = "default_timeout")]
    pub timeout_ms: u64,

    /// Function path patterns to skip verification for.
    /// Uses substring matching against the fully-qualified function path.
    #[serde(default)]
    pub skip_functions: Vec<String>,

    /// If non-empty, ONLY verify functions matching these patterns.
    /// Takes precedence over `skip_functions`.
    #[serde(default)]
    pub verify_functions: Vec<String>,

    /// Solver backend to use (e.g., "z4", "zani", "sunder").
    /// Default: None (router selects automatically).
    #[serde(default)]
    pub solver: Option<String>,

    /// Proof level for verification obligations.
    /// Default: None (inherits from `level`).
    #[serde(default)]
    pub proof_level: Option<String>,

    /// Directory for verification result caching.
    /// Default: None (uses system temp directory).
    #[serde(default)]
    pub cache_dir: Option<PathBuf>,

    /// Number of parallel verification workers.
    /// Default: None (auto-detect from CPU count).
    #[serde(default)]
    pub parallel: Option<u32>,

    /// Whether spec strengthening (trust-strengthen) is enabled. Default: true.
    /// Disable with TRUST_DISABLE_STRENGTHEN=1.
    #[serde(default = "default_true")]
    pub strengthen: bool,

    /// Whether CEGAR refinement loop is enabled. Default: true.
    /// Disable with TRUST_DISABLE_CEGAR=1.
    #[serde(default = "default_true")]
    pub cegar: bool,

    /// Whether proof certificate generation is enabled. Default: true.
    /// Disable with TRUST_DISABLE_CERTIFY=1.
    #[serde(default = "default_true")]
    pub certify: bool,

    /// Whether translation validation is enabled. Default: true.
    /// Disable with TRUST_DISABLE_TV=1.
    #[serde(default = "default_true")]
    pub tv: bool,

    /// tRust #622: Report output format ("text", "json", "html", "all").
    /// Default: None (uses "text"). Override with `TRUST_REPORT_FORMAT`.
    #[serde(default)]
    pub report_format: Option<String>,

    /// tRust #882: Process memory limit (MB) for solver backends.
    /// When set, the router checks RSS before each solver dispatch and
    /// returns a MemoryGuard error if the limit is exceeded. 0 = unlimited.
    /// Default: None (uses MemoryGuard's default of 1024 MB).
    /// Override with `TRUST_SOLVER_MEMORY_LIMIT_MB`.
    #[serde(default)]
    pub solver_memory_limit_mb: Option<u64>,
}

fn default_true() -> bool {
    true
}

fn default_level() -> String {
    "L0".to_string()
}

fn default_timeout() -> u64 {
    5000
}

impl Default for TrustConfig {
    fn default() -> Self {
        TrustConfig {
            enabled: true,
            level: default_level(),
            timeout_ms: default_timeout(),
            skip_functions: vec![],
            verify_functions: vec![],
            solver: None,
            proof_level: None,
            cache_dir: None,
            parallel: None,
            strengthen: true,
            cegar: true,
            certify: true,
            tv: true,
            report_format: None,
            solver_memory_limit_mb: None,
        }
    }
}

impl TrustConfig {
    /// tRust #622: Resolve the report format from the config string.
    ///
    /// Falls back to `ReportFormat::Text` if unset or unrecognized.
    #[must_use]
    pub fn resolved_report_format(&self) -> ReportFormat {
        self.report_format.as_deref().and_then(ReportFormat::from_name).unwrap_or_default()
    }

    /// tRust: Load configuration from `trust.toml` in the given directory.
    ///
    /// Returns `Default` if the file does not exist. Prints a warning to
    /// stderr and returns `Default` if the file cannot be read or parsed.
    #[must_use]
    pub fn load(dir: &Path) -> Self {
        let path = dir.join("trust.toml");
        if path.exists() {
            match std::fs::read_to_string(&path) {
                Ok(content) => match toml::from_str(&content) {
                    Ok(config) => return config,
                    Err(e) => eprintln!("warning: failed to parse {}: {e}", path.display()),
                },
                Err(e) => eprintln!("warning: failed to read {}: {e}", path.display()),
            }
        }
        Self::default()
    }

    /// tRust: Parse a `TrustConfig` from a TOML string.
    ///
    /// Returns `Err` if the string contains unknown fields or invalid values.
    pub fn from_toml(content: &str) -> Result<Self, toml::de::Error> {
        toml::from_str(content)
    }

    /// tRust: Load configuration with the full resolution stack.
    ///
    /// Resolution order: defaults -> profile -> file -> env overrides.
    /// Searches up from `start_dir` for `trust.toml`.
    #[must_use]
    pub fn resolve(start_dir: &Path, profile: Option<VerificationProfile>) -> Self {
        let mut config = Self::default();

        // Apply profile if specified
        if let Some(p) = profile {
            apply_profile(&mut config, p);
        }

        // Merge with file config if found
        if let Some(config_path) = find_config_file(start_dir) {
            match load_config(&config_path) {
                Ok(file_config) => config = merge_configs(config, file_config),
                Err(e) => eprintln!("warning: {e}"),
            }
        }

        // Apply environment overrides (highest precedence)
        apply_env_overrides(&mut config);

        config
    }

    /// tRust: Determine whether a function should be verified.
    ///
    /// Logic:
    /// 1. If `enabled` is false, always returns false.
    /// 2. If `verify_functions` is non-empty, returns true only if
    ///    `func_path` matches any pattern (allowlist mode).
    /// 3. Otherwise, returns false if `func_path` matches any
    ///    `skip_functions` pattern (blocklist mode).
    /// 4. Default: returns true.
    #[must_use]
    pub fn should_verify(&self, func_path: &str) -> bool {
        if !self.enabled {
            return false;
        }
        // tRust: Allowlist takes precedence — if specified, only matching functions run.
        if !self.verify_functions.is_empty() {
            return self.verify_functions.iter().any(|p| func_path.contains(p));
        }
        // tRust: Blocklist — skip matching functions.
        if self.skip_functions.iter().any(|p| func_path.contains(p)) {
            return false;
        }
        true
    }
}

// Shared env-var lock for all test modules in this crate.
// Three test modules (lib, loader, env_override) mutate process env vars;
// they must share ONE mutex to avoid races.
#[cfg(test)]
pub(crate) static TEST_ENV_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

#[cfg(test)]
mod tests {
    use super::*;

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
            "TRUST_REPORT_FORMAT",
            "TRUST_SOLVER_MEMORY_LIMIT_MB",
        ];
        let saved: Vec<_> = trust_vars.iter().map(|k| (*k, std::env::var(k).ok())).collect();
        for k in &trust_vars {
            // SAFETY: test-only env var manipulation; tests are serialized via TEST_ENV_LOCK
            // so no concurrent access to the environment occurs. // tRust:
            unsafe { std::env::remove_var(k) };
        }
        f();
        for (k, v) in &saved {
            if let Some(val) = v {
                // SAFETY: test-only env var restoration; tests are serialized via TEST_ENV_LOCK // tRust:
                unsafe { std::env::set_var(k, val) };
            }
        }
    }

    #[test]
    fn test_config_default_values() {
        let config = TrustConfig::default();
        assert!(config.enabled);
        assert_eq!(config.level, "L0");
        assert_eq!(config.timeout_ms, 5000);
        assert!(config.skip_functions.is_empty());
        assert!(config.verify_functions.is_empty());
        assert!(config.solver.is_none());
        assert!(config.proof_level.is_none());
        assert!(config.cache_dir.is_none());
        assert!(config.parallel.is_none());
    }

    #[test]
    fn test_config_from_toml_empty_yields_defaults() {
        let config = TrustConfig::from_toml("").expect("empty TOML should parse to defaults");
        assert!(config.enabled);
        assert_eq!(config.level, "L0");
        assert_eq!(config.timeout_ms, 5000);
    }

    #[test]
    fn test_config_from_toml_partial_override() {
        let toml = r#"
enabled = false
level = "L1"
"#;
        let config = TrustConfig::from_toml(toml).expect("partial TOML should parse");
        assert!(!config.enabled);
        assert_eq!(config.level, "L1");
        assert_eq!(config.timeout_ms, 5000); // default preserved
    }

    #[test]
    fn test_config_from_toml_full() {
        let toml = r#"
enabled = true
level = "L2"
timeout_ms = 10000
skip_functions = ["test_helper", "bench_"]
verify_functions = ["critical::"]
solver = "z4"
proof_level = "L1"
cache_dir = "/tmp/trust"
parallel = 4
strengthen = false
cegar = true
certify = false
tv = true
"#;
        let config = TrustConfig::from_toml(toml).expect("full TOML should parse");
        assert!(config.enabled);
        assert_eq!(config.level, "L2");
        assert_eq!(config.timeout_ms, 10000);
        assert_eq!(config.skip_functions, vec!["test_helper", "bench_"]);
        assert_eq!(config.verify_functions, vec!["critical::"]);
        assert_eq!(config.solver.as_deref(), Some("z4"));
        assert_eq!(config.proof_level.as_deref(), Some("L1"));
        assert_eq!(config.cache_dir, Some(PathBuf::from("/tmp/trust")));
        assert_eq!(config.parallel, Some(4));
        assert!(!config.strengthen);
        assert!(config.cegar);
        assert!(!config.certify);
        assert!(config.tv);
    }

    #[test]
    fn test_config_default_feature_flags_enabled() {
        let config = TrustConfig::default();
        assert!(config.strengthen);
        assert!(config.cegar);
        assert!(config.certify);
        assert!(config.tv);
    }

    #[test]
    fn test_config_deny_unknown_fields() {
        let toml = r#"
enabled = true
bogus_field = "oops"
"#;
        let result = TrustConfig::from_toml(toml);
        assert!(result.is_err(), "unknown fields should be rejected");
    }

    #[test]
    fn test_should_verify_disabled() {
        let config = TrustConfig { enabled: false, ..Default::default() };
        assert!(!config.should_verify("any::function"));
    }

    #[test]
    fn test_should_verify_default_allows_all() {
        let config = TrustConfig::default();
        assert!(config.should_verify("my_crate::module::function"));
        assert!(config.should_verify("std::vec::Vec::push"));
    }

    #[test]
    fn test_should_verify_skip_functions_blocklist() {
        let config = TrustConfig {
            skip_functions: vec!["test_".to_string(), "bench_".to_string()],
            ..Default::default()
        };
        assert!(!config.should_verify("my_crate::test_helper"));
        assert!(!config.should_verify("my_crate::bench_sort"));
        assert!(config.should_verify("my_crate::production_fn"));
    }

    #[test]
    fn test_should_verify_verify_functions_allowlist() {
        let config = TrustConfig {
            verify_functions: vec!["critical::".to_string()],
            skip_functions: vec!["critical::debug".to_string()],
            ..Default::default()
        };
        // Allowlist takes precedence — skip_functions is ignored when verify_functions is set.
        assert!(config.should_verify("critical::process"));
        assert!(config.should_verify("critical::debug")); // skip_functions NOT consulted
        assert!(!config.should_verify("other::module"));
    }

    #[test]
    fn test_load_nonexistent_dir_returns_default() {
        let config = TrustConfig::load(Path::new("/nonexistent/path"));
        assert!(config.enabled);
        assert_eq!(config.level, "L0");
    }

    #[test]
    fn test_config_error_display() {
        let err = ConfigError::Io {
            path: PathBuf::from("/tmp/trust.toml"),
            source: std::io::Error::new(std::io::ErrorKind::NotFound, "file not found"),
        };
        let msg = format!("{err}");
        assert!(msg.contains("/tmp/trust.toml"));
        assert!(msg.contains("file not found"));
    }

    #[test]
    fn test_resolve_with_file() {
        with_clean_env(|| {
            let dir = tempfile::tempdir().expect("should create tempdir");
            std::fs::write(dir.path().join("trust.toml"), "level = \"L2\"\ntimeout_ms = 9999\n")
                .expect("should write file");

            let config = TrustConfig::resolve(dir.path(), None);
            assert_eq!(config.level, "L2");
            assert_eq!(config.timeout_ms, 9999);
        });
    }

    #[test]
    fn test_resolve_with_profile_and_file() {
        with_clean_env(|| {
            let dir = tempfile::tempdir().expect("should create tempdir");
            std::fs::write(dir.path().join("trust.toml"), "timeout_ms = 7777\n")
                .expect("should write file");

            let config = TrustConfig::resolve(dir.path(), Some(VerificationProfile::Thorough));
            // File override wins for timeout
            assert_eq!(config.timeout_ms, 7777);
            // Profile sets level (file didn't override it)
            assert_eq!(config.level, "L1");
        });
    }

    #[test]
    fn test_resolve_no_file_returns_defaults() {
        with_clean_env(|| {
            let dir = tempfile::tempdir().expect("should create tempdir");
            let config = TrustConfig::resolve(dir.path(), None);
            assert!(config.enabled);
            assert_eq!(config.level, "L0");
            assert_eq!(config.timeout_ms, 5000);
        });
    }

    // -------------------------------------------------------------------
    // #622: ReportFormat tests
    // -------------------------------------------------------------------

    #[test]
    fn test_report_format_from_name() {
        assert_eq!(ReportFormat::from_name("text"), Some(ReportFormat::Text));
        assert_eq!(ReportFormat::from_name("json"), Some(ReportFormat::Json));
        assert_eq!(ReportFormat::from_name("html"), Some(ReportFormat::Html));
        assert_eq!(ReportFormat::from_name("all"), Some(ReportFormat::All));
        assert_eq!(ReportFormat::from_name("HTML"), Some(ReportFormat::Html));
        assert_eq!(ReportFormat::from_name("TEXT"), Some(ReportFormat::Text));
        assert_eq!(ReportFormat::from_name("bogus"), None);
        assert_eq!(ReportFormat::from_name(""), None);
    }

    #[test]
    fn test_report_format_default_is_text() {
        assert_eq!(ReportFormat::default(), ReportFormat::Text);
    }

    #[test]
    fn test_report_format_includes_methods() {
        assert!(ReportFormat::Text.includes_text());
        assert!(!ReportFormat::Text.includes_json());
        assert!(!ReportFormat::Text.includes_html());

        assert!(!ReportFormat::Json.includes_text());
        assert!(ReportFormat::Json.includes_json());
        assert!(!ReportFormat::Json.includes_html());

        assert!(!ReportFormat::Html.includes_text());
        assert!(!ReportFormat::Html.includes_json());
        assert!(ReportFormat::Html.includes_html());

        assert!(ReportFormat::All.includes_text());
        assert!(ReportFormat::All.includes_json());
        assert!(ReportFormat::All.includes_html());
    }

    #[test]
    fn test_resolved_report_format_default() {
        let config = TrustConfig::default();
        assert_eq!(config.resolved_report_format(), ReportFormat::Text);
    }

    #[test]
    fn test_resolved_report_format_from_config() {
        let config = TrustConfig { report_format: Some("html".to_string()), ..Default::default() };
        assert_eq!(config.resolved_report_format(), ReportFormat::Html);
    }

    #[test]
    fn test_resolved_report_format_invalid_falls_back() {
        let config = TrustConfig { report_format: Some("xml".to_string()), ..Default::default() };
        assert_eq!(config.resolved_report_format(), ReportFormat::Text);
    }

    #[test]
    fn test_config_from_toml_with_report_format() {
        let toml = r#"report_format = "html""#;
        let config = TrustConfig::from_toml(toml).expect("should parse report_format");
        assert_eq!(config.report_format.as_deref(), Some("html"));
        assert_eq!(config.resolved_report_format(), ReportFormat::Html);
    }

    #[test]
    fn test_config_from_toml_with_report_format_all() {
        let toml = r#"report_format = "all""#;
        let config = TrustConfig::from_toml(toml).expect("should parse report_format");
        assert_eq!(config.resolved_report_format(), ReportFormat::All);
    }

    // -------------------------------------------------------------------
    // #882: solver_memory_limit_mb tests
    // -------------------------------------------------------------------

    #[test]
    fn test_config_default_solver_memory_limit_none() {
        let config = TrustConfig::default();
        assert!(config.solver_memory_limit_mb.is_none());
    }

    #[test]
    fn test_config_from_toml_solver_memory_limit() {
        let toml = r#"solver_memory_limit_mb = 2048"#;
        let config = TrustConfig::from_toml(toml).expect("should parse solver_memory_limit_mb");
        assert_eq!(config.solver_memory_limit_mb, Some(2048));
    }

    #[test]
    fn test_config_from_toml_solver_memory_limit_zero() {
        let toml = r#"solver_memory_limit_mb = 0"#;
        let config = TrustConfig::from_toml(toml).expect("should parse 0");
        assert_eq!(config.solver_memory_limit_mb, Some(0));
    }
}
