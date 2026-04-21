// trust-driver/config_bridge.rs: Bridge between trust-config (trust.toml) and LoopConfig
//
// Converts TrustConfig → LoopConfig, supports CLI overrides, and provides
// a convenience loader for trust.toml files.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::path::Path;
use std::time::Duration;

use trust_config::TrustConfig;

use crate::{DriverError, LoopConfig};

/// CLI overrides that take precedence over trust.toml values.
///
/// All fields are `Option` — `None` means "use the config file value."
#[derive(Debug, Clone, Default)]
pub struct CliOverrides {
    /// Override max loop iterations.
    pub max_iterations: Option<u32>,
    /// Override verification level ("L0", "L1", "L2").
    pub level: Option<String>,
    /// Override per-function timeout in milliseconds.
    pub timeout_ms: Option<u64>,
    /// Override whether source rewriting is allowed.
    pub allow_rewrite: Option<bool>,
}

/// tRust: Convert a `TrustConfig` into a `LoopConfig`.
///
/// Mapping:
/// - `max_iterations`: preserved from `LoopConfig::default()` (TrustConfig has no equivalent)
/// - `stable_round_limit`: preserved from default
/// - `allow_rewrite`: `true` (default) — TrustConfig doesn't control this
/// - `run_debug`: `true` if enabled
///
/// The `level` and `timeout_ms` fields from TrustConfig are informational
/// and returned alongside the LoopConfig via [`ConfigBridge`].
#[must_use]
pub fn loop_config_from_trust_config(config: &TrustConfig) -> LoopConfig {
    let defaults = LoopConfig::default();
    LoopConfig {
        max_iterations: defaults.max_iterations,
        stable_round_limit: defaults.stable_round_limit,
        allow_rewrite: defaults.allow_rewrite,
        // tRust: Disable debug phase when verification is disabled entirely
        run_debug: config.enabled && defaults.run_debug,
    }
}

/// Full configuration bridge result, carrying both the LoopConfig and
/// the additional TrustConfig fields that the loop phases need.
#[derive(Debug, Clone)]
pub struct ConfigBridge {
    /// Configuration for the prove-strengthen-backprop loop.
    pub loop_config: LoopConfig,
    /// Verification level from trust.toml (e.g., "L0", "L1", "L2").
    pub level: String,
    /// Per-function timeout.
    pub timeout: Duration,
    /// Whether verification is enabled at all.
    pub enabled: bool,
    /// Function skip patterns from trust.toml.
    pub skip_functions: Vec<String>,
    /// Function allow patterns from trust.toml.
    pub verify_functions: Vec<String>,
}

impl ConfigBridge {
    /// tRust: Build a full ConfigBridge from a TrustConfig.
    #[must_use]
    pub fn from_trust_config(config: &TrustConfig) -> Self {
        Self {
            loop_config: loop_config_from_trust_config(config),
            level: config.level.clone(),
            timeout: Duration::from_millis(config.timeout_ms),
            enabled: config.enabled,
            skip_functions: config.skip_functions.clone(),
            verify_functions: config.verify_functions.clone(),
        }
    }

    /// tRust: Load a ConfigBridge from a trust.toml file path.
    ///
    /// The path should point to the directory containing `trust.toml`.
    /// Returns defaults if the file does not exist.
    #[must_use]
    pub fn from_toml_dir(dir: &Path) -> Self {
        let config = TrustConfig::load(dir);
        Self::from_trust_config(&config)
    }

    /// tRust: Load a ConfigBridge from a direct path to a trust.toml file.
    ///
    /// Returns an error if the file exists but cannot be read or parsed.
    pub fn from_toml_path(path: &Path) -> Result<Self, DriverError> {
        if !path.exists() {
            return Ok(Self::from_trust_config(&TrustConfig::default()));
        }
        let content = std::fs::read_to_string(path)
            .map_err(|e| DriverError::ConfigRead { path: path.display().to_string(), source: e })?;
        let config = TrustConfig::from_toml(&content).map_err(|e| DriverError::ConfigParse {
            path: path.display().to_string(),
            message: e.to_string(),
        })?;
        Ok(Self::from_trust_config(&config))
    }

    /// tRust: Apply CLI overrides on top of the loaded configuration.
    ///
    /// CLI values take precedence — `None` fields are left unchanged.
    #[must_use]
    pub fn merge_with_cli(mut self, cli: &CliOverrides) -> Self {
        if let Some(max_iter) = cli.max_iterations {
            self.loop_config.max_iterations = max_iter;
        }
        if let Some(ref level) = cli.level {
            self.level = level.clone();
        }
        if let Some(timeout_ms) = cli.timeout_ms {
            self.timeout = Duration::from_millis(timeout_ms);
        }
        if let Some(allow_rewrite) = cli.allow_rewrite {
            self.loop_config.allow_rewrite = allow_rewrite;
        }
        self
    }
}

/// tRust: Convenience function to load LoopConfig from a trust.toml path.
///
/// Loads the file, converts to LoopConfig, and returns it. For the full
/// configuration (level, timeout, filters), use [`ConfigBridge::from_toml_path`].
pub fn from_toml_path(path: &Path) -> Result<LoopConfig, DriverError> {
    let bridge = ConfigBridge::from_toml_path(path)?;
    Ok(bridge.loop_config)
}

/// tRust: Apply CLI overrides to a LoopConfig.
///
/// This is the simple version that only touches LoopConfig fields.
/// For level/timeout overrides, use [`ConfigBridge::merge_with_cli`].
#[must_use]
pub fn merge_with_cli(config: LoopConfig, cli: &CliOverrides) -> LoopConfig {
    LoopConfig {
        max_iterations: cli.max_iterations.unwrap_or(config.max_iterations),
        stable_round_limit: config.stable_round_limit,
        allow_rewrite: cli.allow_rewrite.unwrap_or(config.allow_rewrite),
        run_debug: config.run_debug,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;
    use tempfile::TempDir;

    // -- TrustConfig -> LoopConfig conversion tests --

    #[test]
    fn test_default_trust_config_produces_default_loop_config() {
        let tc = TrustConfig::default();
        let lc = loop_config_from_trust_config(&tc);
        let defaults = LoopConfig::default();
        assert_eq!(lc.max_iterations, defaults.max_iterations);
        assert_eq!(lc.stable_round_limit, defaults.stable_round_limit);
        assert_eq!(lc.allow_rewrite, defaults.allow_rewrite);
        assert!(lc.run_debug);
    }

    #[test]
    fn test_disabled_config_disables_debug() {
        let tc = TrustConfig { enabled: false, ..Default::default() };
        let lc = loop_config_from_trust_config(&tc);
        assert!(!lc.run_debug, "debug should be disabled when verification is off");
    }

    // -- ConfigBridge tests --

    #[test]
    fn test_config_bridge_from_trust_config() {
        let tc = TrustConfig {
            enabled: true,
            level: "L2".to_string(),
            timeout_ms: 10000,
            skip_functions: vec!["test_".to_string()],
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
        };
        let bridge = ConfigBridge::from_trust_config(&tc);
        assert_eq!(bridge.level, "L2");
        assert_eq!(bridge.timeout, Duration::from_millis(10000));
        assert!(bridge.enabled);
        assert_eq!(bridge.skip_functions, vec!["test_"]);
        assert!(bridge.verify_functions.is_empty());
    }

    #[test]
    fn test_config_bridge_from_toml_dir_nonexistent() {
        let bridge = ConfigBridge::from_toml_dir(Path::new("/nonexistent/path"));
        assert!(bridge.enabled);
        assert_eq!(bridge.level, "L0");
        assert_eq!(bridge.timeout, Duration::from_millis(5000));
    }

    #[test]
    fn test_config_bridge_from_toml_path_nonexistent() {
        let result = ConfigBridge::from_toml_path(Path::new("/nonexistent/trust.toml"));
        let bridge = result.expect("nonexistent path should return defaults");
        assert!(bridge.enabled);
        assert_eq!(bridge.level, "L0");
    }

    #[test]
    fn test_config_bridge_from_toml_path_valid() {
        let dir = TempDir::new().expect("tempdir");
        let path = dir.path().join("trust.toml");
        let mut f = std::fs::File::create(&path).expect("create");
        writeln!(f, r#"level = "L1""#).expect("write");
        writeln!(f, "timeout_ms = 3000").expect("write");
        drop(f);

        let bridge = ConfigBridge::from_toml_path(&path).expect("should parse valid toml");
        assert_eq!(bridge.level, "L1");
        assert_eq!(bridge.timeout, Duration::from_millis(3000));
        assert!(bridge.enabled); // default
    }

    #[test]
    fn test_config_bridge_from_toml_path_invalid() {
        let dir = TempDir::new().expect("tempdir");
        let path = dir.path().join("trust.toml");
        std::fs::write(&path, "not_a_valid_field = 42").expect("write");

        let result = ConfigBridge::from_toml_path(&path);
        assert!(result.is_err(), "invalid toml should produce DriverError");
    }

    // -- CLI override tests --

    #[test]
    fn test_merge_with_cli_no_overrides() {
        let bridge = ConfigBridge::from_trust_config(&TrustConfig::default());
        let cli = CliOverrides::default();
        let merged = bridge.clone().merge_with_cli(&cli);
        assert_eq!(merged.loop_config.max_iterations, bridge.loop_config.max_iterations);
        assert_eq!(merged.level, bridge.level);
        assert_eq!(merged.timeout, bridge.timeout);
    }

    #[test]
    fn test_merge_with_cli_all_overrides() {
        let bridge = ConfigBridge::from_trust_config(&TrustConfig::default());
        let cli = CliOverrides {
            max_iterations: Some(20),
            level: Some("L2".to_string()),
            timeout_ms: Some(15000),
            allow_rewrite: Some(false),
        };
        let merged = bridge.merge_with_cli(&cli);
        assert_eq!(merged.loop_config.max_iterations, 20);
        assert_eq!(merged.level, "L2");
        assert_eq!(merged.timeout, Duration::from_millis(15000));
        assert!(!merged.loop_config.allow_rewrite);
    }

    #[test]
    fn test_merge_with_cli_partial_overrides() {
        let tc = TrustConfig { level: "L1".to_string(), timeout_ms: 8000, ..Default::default() };
        let bridge = ConfigBridge::from_trust_config(&tc);
        let cli = CliOverrides { max_iterations: Some(3), ..Default::default() };
        let merged = bridge.merge_with_cli(&cli);
        assert_eq!(merged.loop_config.max_iterations, 3);
        assert_eq!(merged.level, "L1"); // unchanged
        assert_eq!(merged.timeout, Duration::from_millis(8000)); // unchanged
    }

    // -- Convenience function tests --

    #[test]
    fn test_from_toml_path_convenience() {
        let dir = TempDir::new().expect("tempdir");
        let path = dir.path().join("trust.toml");
        std::fs::write(&path, "enabled = false").expect("write");

        let lc = from_toml_path(&path).expect("should parse");
        assert!(!lc.run_debug, "disabled config should disable debug");
    }

    #[test]
    fn test_merge_with_cli_convenience() {
        let lc = LoopConfig::default();
        let cli = CliOverrides {
            max_iterations: Some(42),
            allow_rewrite: Some(false),
            ..Default::default()
        };
        let merged = merge_with_cli(lc, &cli);
        assert_eq!(merged.max_iterations, 42);
        assert!(!merged.allow_rewrite);
        // Unchanged fields
        assert_eq!(merged.stable_round_limit, LoopConfig::default().stable_round_limit);
        assert_eq!(merged.run_debug, LoopConfig::default().run_debug);
    }

    // -- End-to-end test: load toml -> merge CLI -> get LoopConfig --

    #[test]
    fn test_end_to_end_toml_plus_cli() {
        let dir = TempDir::new().expect("tempdir");
        let path = dir.path().join("trust.toml");
        std::fs::write(
            &path,
            r#"
enabled = true
level = "L1"
timeout_ms = 7000
skip_functions = ["bench_"]
"#,
        )
        .expect("write");

        let bridge = ConfigBridge::from_toml_path(&path).expect("parse");
        assert_eq!(bridge.level, "L1");
        assert_eq!(bridge.timeout, Duration::from_millis(7000));
        assert_eq!(bridge.skip_functions, vec!["bench_"]);

        // CLI overrides level and max_iterations
        let cli = CliOverrides {
            level: Some("L2".to_string()),
            max_iterations: Some(5),
            ..Default::default()
        };
        let final_config = bridge.merge_with_cli(&cli);
        assert_eq!(final_config.level, "L2");
        assert_eq!(final_config.loop_config.max_iterations, 5);
        // timeout and skip_functions unchanged from toml
        assert_eq!(final_config.timeout, Duration::from_millis(7000));
        assert_eq!(final_config.skip_functions, vec!["bench_"]);
    }
}
