//! trust-config: TOML file loading and directory-tree search
//!
//! Loads `trust.toml` configuration files, searches up the directory tree
//! to find the nearest config file, and supports config merging (base + overlay).
//!
//! Author: Andrew Yates <andrew@andrewdyates.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::path::{Path, PathBuf};

use crate::{ConfigError, TrustConfig};

/// tRust: The config file name we search for.
const CONFIG_FILE_NAME: &str = "trust.toml";

/// tRust: Load a `TrustConfig` from a TOML file at the given path.
///
/// Returns a typed error if the file cannot be read or parsed.
pub fn load_config(path: &Path) -> Result<TrustConfig, ConfigError> {
    let content = std::fs::read_to_string(path)
        .map_err(|e| ConfigError::Io { path: path.to_path_buf(), source: e })?;
    let config: TrustConfig = toml::from_str(&content)
        .map_err(|e| ConfigError::Parse { path: path.to_path_buf(), source: e })?;
    Ok(config)
}

/// tRust: Search up the directory tree for a `trust.toml` file.
///
/// Starts at `start_dir` and walks parent directories until it finds
/// `trust.toml` or reaches the filesystem root. Returns `None` if no
/// config file is found.
#[must_use]
pub fn find_config_file(start_dir: &Path) -> Option<PathBuf> {
    let mut current = start_dir.to_path_buf();
    loop {
        let candidate = current.join(CONFIG_FILE_NAME);
        if candidate.is_file() {
            return Some(candidate);
        }
        if !current.pop() {
            return None;
        }
    }
}

/// tRust: Return a `TrustConfig` with sensible defaults.
///
/// Equivalent to `TrustConfig::default()` but named for clarity in the
/// config loading pipeline.
#[must_use]
pub fn default_config() -> TrustConfig {
    TrustConfig::default()
}

/// tRust: Merge two configs, with `overlay` values taking precedence.
///
/// For scalar fields, overlay's value wins if it differs from the default.
/// For vector fields, overlay's value replaces base's if non-empty.
/// For `Option` fields, overlay's value wins if `Some`.
#[must_use]
pub fn merge_configs(base: TrustConfig, overlay: TrustConfig) -> TrustConfig {
    let defaults = TrustConfig::default();

    TrustConfig {
        // Bool: overlay wins if it differs from default
        enabled: if overlay.enabled != defaults.enabled { overlay.enabled } else { base.enabled },
        // String: overlay wins if it differs from default
        level: if overlay.level != defaults.level { overlay.level } else { base.level },
        // u64: overlay wins if it differs from default
        timeout_ms: if overlay.timeout_ms != defaults.timeout_ms {
            overlay.timeout_ms
        } else {
            base.timeout_ms
        },
        // Vec: overlay wins if non-empty
        skip_functions: if !overlay.skip_functions.is_empty() {
            overlay.skip_functions
        } else {
            base.skip_functions
        },
        verify_functions: if !overlay.verify_functions.is_empty() {
            overlay.verify_functions
        } else {
            base.verify_functions
        },
        // Option: overlay wins if Some
        solver: overlay.solver.or(base.solver),
        proof_level: overlay.proof_level.or(base.proof_level),
        cache_dir: overlay.cache_dir.or(base.cache_dir),
        parallel: overlay.parallel.or(base.parallel),
        strengthen: if overlay.strengthen != defaults.strengthen {
            overlay.strengthen
        } else {
            base.strengthen
        },
        cegar: if overlay.cegar != defaults.cegar { overlay.cegar } else { base.cegar },
        certify: if overlay.certify != defaults.certify { overlay.certify } else { base.certify },
        tv: if overlay.tv != defaults.tv { overlay.tv } else { base.tv },
        report_format: overlay.report_format.or(base.report_format),
        solver_memory_limit_mb: overlay.solver_memory_limit_mb.or(base.solver_memory_limit_mb),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    #[test]
    fn test_load_config_valid_toml() {
        let dir = tempfile::tempdir().expect("should create tempdir");
        let path = dir.path().join("trust.toml");
        fs::write(
            &path,
            r#"
enabled = true
level = "L1"
timeout_ms = 10000
"#,
        )
        .expect("should write file");

        let config = load_config(&path).expect("should parse valid TOML");
        assert_eq!(config.level, "L1");
        assert_eq!(config.timeout_ms, 10_000);
    }

    #[test]
    fn test_load_config_missing_file() {
        let result = load_config(Path::new("/nonexistent/trust.toml"));
        assert!(matches!(result, Err(ConfigError::Io { .. })));
    }

    #[test]
    fn test_load_config_invalid_toml() {
        let dir = tempfile::tempdir().expect("should create tempdir");
        let path = dir.path().join("trust.toml");
        fs::write(&path, "not valid toml [[[").expect("should write file");

        let result = load_config(&path);
        assert!(matches!(result, Err(ConfigError::Parse { .. })));
    }

    #[test]
    fn test_find_config_file_in_current_dir() {
        let dir = tempfile::tempdir().expect("should create tempdir");
        let config_path = dir.path().join("trust.toml");
        fs::write(&config_path, "enabled = true").expect("should write file");

        let found = find_config_file(dir.path());
        assert_eq!(found, Some(config_path));
    }

    #[test]
    fn test_find_config_file_in_parent_dir() {
        let parent = tempfile::tempdir().expect("should create tempdir");
        let child = parent.path().join("src");
        fs::create_dir(&child).expect("should create child dir");
        let config_path = parent.path().join("trust.toml");
        fs::write(&config_path, "enabled = true").expect("should write file");

        let found = find_config_file(&child);
        assert_eq!(found, Some(config_path));
    }

    #[test]
    fn test_find_config_file_not_found() {
        let dir = tempfile::tempdir().expect("should create tempdir");
        assert_eq!(find_config_file(dir.path()), None);
    }

    #[test]
    fn test_default_config_matches_struct_default() {
        let dc = default_config();
        let sd = TrustConfig::default();
        assert_eq!(dc.enabled, sd.enabled);
        assert_eq!(dc.level, sd.level);
        assert_eq!(dc.timeout_ms, sd.timeout_ms);
    }

    #[test]
    fn test_merge_configs_overlay_wins_for_non_default() {
        let base =
            TrustConfig { timeout_ms: 8000, solver: Some("z4".to_string()), ..Default::default() };
        let overlay = TrustConfig {
            level: "L2".to_string(),
            solver: Some("zani".to_string()),
            ..Default::default()
        };
        let merged = merge_configs(base, overlay);
        assert_eq!(merged.timeout_ms, 8000); // base preserved (overlay was default)
        assert_eq!(merged.level, "L2"); // overlay wins
        assert_eq!(merged.solver.as_deref(), Some("zani")); // overlay wins (both Some)
    }

    #[test]
    fn test_merge_configs_base_preserved_when_overlay_default() {
        let base = TrustConfig {
            enabled: false,
            timeout_ms: 999,
            skip_functions: vec!["test_".to_string()],
            proof_level: Some("L1".to_string()),
            ..Default::default()
        };
        let overlay = TrustConfig::default();
        let merged = merge_configs(base, overlay);
        // Base values preserved since overlay is all defaults
        assert!(!merged.enabled);
        assert_eq!(merged.timeout_ms, 999);
        assert_eq!(merged.skip_functions, vec!["test_"]);
        assert_eq!(merged.proof_level.as_deref(), Some("L1"));
    }

    #[test]
    fn test_merge_configs_vecs_overlay_replaces_when_nonempty() {
        let base = TrustConfig { skip_functions: vec!["old_".to_string()], ..Default::default() };
        let overlay =
            TrustConfig { skip_functions: vec!["new_".to_string()], ..Default::default() };
        let merged = merge_configs(base, overlay);
        assert_eq!(merged.skip_functions, vec!["new_"]);
    }

    #[test]
    fn test_merge_configs_feature_flags_follow_default_on_semantics() {
        let base = TrustConfig { strengthen: false, cegar: false, ..Default::default() };
        let overlay = TrustConfig { certify: false, tv: false, ..Default::default() };
        let merged = merge_configs(base, overlay);
        assert!(!merged.strengthen);
        assert!(!merged.cegar);
        assert!(!merged.certify);
        assert!(!merged.tv);
    }
}
