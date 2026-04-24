// cargo-trust configuration: TrustConfig loaded from trust.toml
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::path::Path;

use serde::{Deserialize, Deserializer, de};

pub(crate) const DEFAULT_CODEGEN_BACKEND: &str = "llvm";

pub(crate) fn normalize_verification_level(name: &str) -> Option<&'static str> {
    match name.trim().to_ascii_uppercase().as_str() {
        "L0" => Some("L0"),
        "L1" => Some("L1"),
        "L2" => Some("L2"),
        _ => None,
    }
}

pub(crate) fn known_verification_levels() -> &'static [&'static str] {
    &["L0", "L1", "L2"]
}

pub(crate) fn normalize_codegen_backend(name: &str) -> Option<&'static str> {
    match name.trim().to_ascii_lowercase().as_str() {
        "llvm" => Some("llvm"),
        "llvm2" => Some("llvm2"),
        _ => None,
    }
}

pub(crate) fn known_codegen_backend_names() -> &'static [&'static str] {
    &["llvm", "llvm2"]
}

/// Configuration loaded from `trust.toml`.
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
#[allow(dead_code)] // Fields used by deserialization and config logic
pub(crate) struct TrustConfig {
    #[serde(default = "default_true")]
    pub(crate) enabled: bool,
    #[serde(default = "default_level", deserialize_with = "deserialize_level")]
    pub(crate) level: String,
    #[serde(default = "default_timeout")]
    pub(crate) timeout_ms: u64,
    #[serde(default)]
    pub(crate) skip_functions: Vec<String>,
    #[serde(default)]
    pub(crate) verify_functions: Vec<String>,
    #[serde(default)]
    pub(crate) codegen_backend: Option<String>,
}

fn default_true() -> bool {
    true
}
pub(crate) fn default_level() -> String {
    "L1".to_string()
}
pub(crate) fn default_timeout() -> u64 {
    5000
}

fn deserialize_level<'de, D>(deserializer: D) -> Result<String, D::Error>
where
    D: Deserializer<'de>,
{
    let raw = String::deserialize(deserializer)?;
    normalize_verification_level(&raw)
        .map(str::to_string)
        .ok_or_else(|| {
            let known = known_verification_levels().join(", ");
            de::Error::custom(format!(
                "invalid verification level `{raw}` (expected one of: {known})"
            ))
        })
}

impl Default for TrustConfig {
    fn default() -> Self {
        Self {
            enabled: true,
            level: default_level(),
            timeout_ms: default_timeout(),
            skip_functions: vec![],
            verify_functions: vec![],
            codegen_backend: None,
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
                Ok(content) => match toml::from_str::<TrustConfig>(&content) {
                    Ok(mut config) => {
                        if let Some(raw_backend) = config.codegen_backend.take() {
                            if let Some(normalized) = normalize_codegen_backend(&raw_backend) {
                                config.codegen_backend = Some(normalized.to_string());
                            } else {
                                let known = known_codegen_backend_names().join(", ");
                                eprintln!(
                                    "cargo-trust: warning: ignoring unknown codegen backend `{raw_backend}` in {} (known backends: {known})",
                                    path.display()
                                );
                            }
                        }
                        eprintln!("cargo-trust: loaded config from {}", path.display());
                        return config;
                    }
                    Err(e) => {
                        eprintln!("cargo-trust: warning: failed to parse {}: {e}", path.display());
                    }
                },
                Err(e) => {
                    eprintln!("cargo-trust: warning: failed to read {}: {e}", path.display());
                }
            }
        }
        Self::default()
    }
}
