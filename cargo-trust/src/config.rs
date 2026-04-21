// cargo-trust configuration: TrustConfig loaded from trust.toml
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::path::Path;

use serde::Deserialize;

/// Configuration loaded from `trust.toml`.
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
#[allow(dead_code)] // Fields used by deserialization and config logic
pub(crate) struct TrustConfig {
    #[serde(default = "default_true")]
    pub(crate) enabled: bool,
    #[serde(default = "default_level")]
    pub(crate) level: String,
    #[serde(default = "default_timeout")]
    pub(crate) timeout_ms: u64,
    #[serde(default)]
    pub(crate) skip_functions: Vec<String>,
    #[serde(default)]
    pub(crate) verify_functions: Vec<String>,
}

fn default_true() -> bool {
    true
}
pub(crate) fn default_level() -> String {
    "L0".to_string()
}
pub(crate) fn default_timeout() -> u64 {
    5000
}

impl Default for TrustConfig {
    fn default() -> Self {
        Self {
            enabled: true,
            level: default_level(),
            timeout_ms: default_timeout(),
            skip_functions: vec![],
            verify_functions: vec![],
        }
    }
}

impl TrustConfig {
    /// Load configuration from `trust.toml` in the given directory.
    /// Returns `Default` if the file does not exist or cannot be parsed.
    pub(crate) fn load(dir: &Path) -> Self {
        let path = dir.join("trust.toml");
        if path.exists() {
            match std::fs::read_to_string(&path) {
                Ok(content) => match toml::from_str(&content) {
                    Ok(config) => {
                        eprintln!(
                            "cargo-trust: loaded config from {}",
                            path.display()
                        );
                        return config;
                    }
                    Err(e) => {
                        eprintln!(
                            "cargo-trust: warning: failed to parse {}: {e}",
                            path.display()
                        );
                    }
                },
                Err(e) => {
                    eprintln!(
                        "cargo-trust: warning: failed to read {}: {e}",
                        path.display()
                    );
                }
            }
        }
        Self::default()
    }
}
