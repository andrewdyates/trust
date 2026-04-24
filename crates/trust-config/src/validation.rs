//! trust-config: Configuration validation
//!
//! Validates a `TrustConfig` for semantic correctness: valid level strings,
//! reasonable timeout ranges, recognized solver names, etc.
//!
//! Author: Andrew Yates <andrew@andrewdyates.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::TrustConfig;

/// tRust: Severity level for configuration warnings.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum Severity {
    /// May cause unexpected behavior but config is usable.
    Warning,
    /// Config is invalid and will likely cause failures.
    Error,
}

/// tRust: A single configuration validation finding.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConfigWarning {
    /// Which config field triggered this warning.
    pub field: String,
    /// Human-readable description of the problem.
    pub message: String,
    /// How severe this finding is.
    pub severity: Severity,
}

impl ConfigWarning {
    #[must_use]
    fn warning(field: impl Into<String>, message: impl Into<String>) -> Self {
        Self { field: field.into(), message: message.into(), severity: Severity::Warning }
    }

    #[must_use]
    fn error(field: impl Into<String>, message: impl Into<String>) -> Self {
        Self { field: field.into(), message: message.into(), severity: Severity::Error }
    }
}

/// tRust: Known valid verification levels.
const VALID_LEVELS: &[&str] = &["L0", "L1", "L2"];

/// tRust: Known valid solver names.
const VALID_SOLVERS: &[&str] = &["z4", "zani", "sunder", "certus", "tla2", "lean5", "mock"];

/// tRust: Minimum reasonable timeout in milliseconds.
const MIN_TIMEOUT_MS: u64 = 100;

/// tRust: Maximum reasonable timeout in milliseconds (10 minutes).
const MAX_TIMEOUT_MS: u64 = 600_000;

/// tRust: Minimum reasonable parallel worker count.
const MIN_PARALLEL: u32 = 1;

/// tRust: Maximum reasonable parallel worker count.
const MAX_PARALLEL: u32 = 256;

/// tRust: Validate a configuration for semantic correctness.
///
/// Returns `Ok(())` if the config is valid, or `Err(warnings)` with a list
/// of findings if any problems are detected. Errors are fatal; warnings
/// indicate suboptimal but usable configuration.
pub fn validate_config(config: &TrustConfig) -> Result<(), Vec<ConfigWarning>> {
    let mut warnings = Vec::new();

    // Validate level
    if !VALID_LEVELS.contains(&config.level.as_str()) {
        warnings.push(ConfigWarning::error(
            "level",
            format!(
                "unknown verification level '{}'; valid levels: {}",
                config.level,
                VALID_LEVELS.join(", ")
            ),
        ));
    }

    // Validate timeout range
    if config.timeout_ms < MIN_TIMEOUT_MS {
        warnings.push(ConfigWarning::warning(
            "timeout_ms",
            format!(
                "timeout {}ms is very low (minimum recommended: {}ms)",
                config.timeout_ms, MIN_TIMEOUT_MS
            ),
        ));
    }
    if config.timeout_ms > MAX_TIMEOUT_MS {
        warnings.push(ConfigWarning::warning(
            "timeout_ms",
            format!(
                "timeout {}ms exceeds maximum recommended ({}ms / 10min)",
                config.timeout_ms, MAX_TIMEOUT_MS
            ),
        ));
    }

    // Validate solver if specified
    if let Some(ref solver) = config.solver
        && !VALID_SOLVERS.contains(&solver.as_str())
    {
        warnings.push(ConfigWarning::error(
            "solver",
            format!("unknown solver '{}'; valid solvers: {}", solver, VALID_SOLVERS.join(", ")),
        ));
    }

    // Validate proof_level if specified
    if let Some(ref proof_level) = config.proof_level
        && !VALID_LEVELS.contains(&proof_level.as_str())
    {
        warnings.push(ConfigWarning::error(
            "proof_level",
            format!(
                "unknown proof level '{}'; valid levels: {}",
                proof_level,
                VALID_LEVELS.join(", ")
            ),
        ));
    }

    // Validate parallel count
    if let Some(parallel) = config.parallel {
        if parallel < MIN_PARALLEL {
            warnings.push(ConfigWarning::error(
                "parallel",
                format!("parallel count must be at least {MIN_PARALLEL}"),
            ));
        }
        if parallel > MAX_PARALLEL {
            warnings.push(ConfigWarning::warning(
                "parallel",
                format!("parallel count {} exceeds maximum recommended ({MAX_PARALLEL})", parallel),
            ));
        }
    }

    // Warn on conflicting skip/verify lists
    if !config.skip_functions.is_empty() && !config.verify_functions.is_empty() {
        warnings.push(ConfigWarning::warning(
            "skip_functions",
            "both skip_functions and verify_functions are set; \
             verify_functions takes precedence and skip_functions will be ignored"
                .to_string(),
        ));
    }

    // Warn if verification disabled but other settings configured
    if !config.enabled
        && (config.level != "L0"
            || !config.skip_functions.is_empty()
            || !config.verify_functions.is_empty())
    {
        warnings.push(ConfigWarning::warning(
            "enabled",
            "verification is disabled but other verification settings are configured; \
             they will have no effect"
                .to_string(),
        ));
    }

    if warnings.is_empty() { Ok(()) } else { Err(warnings) }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_validate_config_default_passes() {
        let config = TrustConfig::default();
        assert!(validate_config(&config).is_ok());
    }

    #[test]
    fn test_validate_config_invalid_level() {
        let config = TrustConfig { level: "L9".to_string(), ..Default::default() };
        let warnings = validate_config(&config).unwrap_err();
        assert_eq!(warnings.len(), 1);
        assert_eq!(warnings[0].field, "level");
        assert_eq!(warnings[0].severity, Severity::Error);
    }

    #[test]
    fn test_validate_config_timeout_too_low() {
        let config = TrustConfig { timeout_ms: 10, ..Default::default() };
        let warnings = validate_config(&config).unwrap_err();
        assert!(warnings.iter().any(|w| w.field == "timeout_ms"));
    }

    #[test]
    fn test_validate_config_timeout_too_high() {
        let config = TrustConfig { timeout_ms: 1_000_000, ..Default::default() };
        let warnings = validate_config(&config).unwrap_err();
        assert!(warnings.iter().any(|w| w.field == "timeout_ms"));
    }

    #[test]
    fn test_validate_config_invalid_solver() {
        let config = TrustConfig { solver: Some("nonexistent".to_string()), ..Default::default() };
        let warnings = validate_config(&config).unwrap_err();
        assert!(warnings.iter().any(|w| w.field == "solver"));
        assert_eq!(warnings[0].severity, Severity::Error);
    }

    #[test]
    fn test_validate_config_valid_solver() {
        let config = TrustConfig { solver: Some("z4".to_string()), ..Default::default() };
        assert!(validate_config(&config).is_ok());
    }

    #[test]
    fn test_validate_config_conflicting_lists_warning() {
        let config = TrustConfig {
            skip_functions: vec!["foo".to_string()],
            verify_functions: vec!["bar".to_string()],
            ..Default::default()
        };
        let warnings = validate_config(&config).unwrap_err();
        assert!(
            warnings.iter().any(|w| w.field == "skip_functions" && w.severity == Severity::Warning)
        );
    }

    #[test]
    fn test_validate_config_disabled_with_settings_warning() {
        let config = TrustConfig { enabled: false, level: "L2".to_string(), ..Default::default() };
        let warnings = validate_config(&config).unwrap_err();
        assert!(warnings.iter().any(|w| w.field == "enabled"));
    }

    #[test]
    fn test_validate_config_invalid_parallel() {
        let config = TrustConfig { parallel: Some(0), ..Default::default() };
        let warnings = validate_config(&config).unwrap_err();
        assert!(warnings.iter().any(|w| w.field == "parallel" && w.severity == Severity::Error));
    }
}
