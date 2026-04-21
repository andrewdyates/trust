//! trust-config: Environment variable overrides
//!
//! Applies `TRUST_*` environment variables on top of file-based configuration.
//! Environment overrides take highest precedence in the config stack:
//! defaults < profile < file < environment.
//!
//! Author: Andrew Yates <andrew@andrewdyates.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::env;
use std::path::PathBuf;

use crate::TrustConfig;

/// tRust: Apply TRUST_* environment variable overrides to a config.
///
/// Supported variables:
/// - `TRUST_VERIFY_LEVEL` — verification level (L0, L1, L2)
/// - `TRUST_TIMEOUT_MS` — per-function timeout in milliseconds
/// - `TRUST_SOLVER` — solver backend name
/// - `TRUST_SKIP_FUNCTIONS` — comma-separated function patterns to skip
/// - `TRUST_PROOF_LEVEL` — proof level (L0, L1, L2)
/// - `TRUST_CACHE_DIR` — directory for verification cache
/// - `TRUST_PARALLEL` — number of parallel verification workers
/// - `TRUST_ENABLED` — enable/disable verification (true/false, 1/0)
/// - `TRUST_DISABLE_STRENGTHEN` — disable spec strengthening (true/false, 1/0)
/// - `TRUST_DISABLE_CEGAR` — disable CEGAR refinement loop (true/false, 1/0)
/// - `TRUST_DISABLE_CERTIFY` — disable proof certificate generation (true/false, 1/0)
/// - `TRUST_DISABLE_TV` — disable translation validation (true/false, 1/0)
///
/// Invalid values are silently ignored (logged to stderr).
pub fn apply_env_overrides(config: &mut TrustConfig) {
    if let Some(val) = env_var("TRUST_ENABLED") {
        if let Some(b) = parse_bool(&val) {
            config.enabled = b;
        } else {
            eprintln!("warning: ignoring TRUST_ENABLED='{}'; expected true/false or 1/0", val);
        }
    }

    if let Some(val) = env_var("TRUST_VERIFY_LEVEL") {
        config.level = val;
    }

    if let Some(val) = env_var("TRUST_TIMEOUT_MS") {
        match val.parse::<u64>() {
            Ok(ms) => config.timeout_ms = ms,
            Err(_) => eprintln!("warning: ignoring TRUST_TIMEOUT_MS='{}'; expected integer", val),
        }
    }

    if let Some(val) = env_var("TRUST_SOLVER") {
        config.solver = Some(val);
    }

    if let Some(val) = env_var("TRUST_SKIP_FUNCTIONS") {
        config.skip_functions = val.split(',').map(|s| s.trim().to_string()).collect();
    }

    if let Some(val) = env_var("TRUST_PROOF_LEVEL") {
        config.proof_level = Some(val);
    }

    if let Some(val) = env_var("TRUST_CACHE_DIR") {
        config.cache_dir = Some(PathBuf::from(val));
    }

    if let Some(val) = env_var("TRUST_PARALLEL") {
        match val.parse::<u32>() {
            Ok(n) => config.parallel = Some(n),
            Err(_) => eprintln!("warning: ignoring TRUST_PARALLEL='{}'; expected integer", val),
        }
    }

    if let Some(val) = env_var("TRUST_DISABLE_STRENGTHEN") {
        if let Some(b) = parse_bool(&val) {
            config.strengthen = !b;
        } else {
            eprintln!(
                "warning: ignoring TRUST_DISABLE_STRENGTHEN='{}'; expected true/false or 1/0",
                val
            );
        }
    }

    if let Some(val) = env_var("TRUST_DISABLE_CEGAR") {
        if let Some(b) = parse_bool(&val) {
            config.cegar = !b;
        } else {
            eprintln!(
                "warning: ignoring TRUST_DISABLE_CEGAR='{}'; expected true/false or 1/0",
                val
            );
        }
    }

    if let Some(val) = env_var("TRUST_DISABLE_CERTIFY") {
        if let Some(b) = parse_bool(&val) {
            config.certify = !b;
        } else {
            eprintln!(
                "warning: ignoring TRUST_DISABLE_CERTIFY='{}'; expected true/false or 1/0",
                val
            );
        }
    }

    if let Some(val) = env_var("TRUST_DISABLE_TV") {
        if let Some(b) = parse_bool(&val) {
            config.tv = !b;
        } else {
            eprintln!("warning: ignoring TRUST_DISABLE_TV='{}'; expected true/false or 1/0", val);
        }
    }

    // tRust #622: Report format override.
    if let Some(val) = env_var("TRUST_REPORT_FORMAT") {
        if crate::ReportFormat::from_name(&val).is_some() {
            config.report_format = Some(val.to_lowercase());
        } else {
            eprintln!(
                "warning: ignoring TRUST_REPORT_FORMAT='{}'; expected text/json/html/all",
                val
            );
        }
    }
}

/// tRust: Read an environment variable, returning None for absent or empty.
fn env_var(key: &str) -> Option<String> {
    match env::var(key) {
        Ok(val) if !val.is_empty() => Some(val),
        _ => None,
    }
}

/// tRust: Parse a boolean from common string representations.
fn parse_bool(s: &str) -> Option<bool> {
    match s.to_lowercase().as_str() {
        "true" | "1" | "yes" | "on" => Some(true),
        "false" | "0" | "no" | "off" => Some(false),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
        let saved: Vec<_> = trust_vars.iter().map(|k| (*k, env::var(k).ok())).collect();
        for k in &trust_vars {
            // SAFETY: Serialized by ENV_LOCK; clearing env for test isolation.
            unsafe { env::remove_var(k) };
        }
        for (k, v) in vars {
            // SAFETY: Serialized by ENV_LOCK; no other threads reading env concurrently.
            unsafe { env::set_var(k, v) };
        }
        f();
        for k in &trust_vars {
            // SAFETY: Serialized by ENV_LOCK; cleaning up after test.
            unsafe { env::remove_var(k) };
        }
        for (k, v) in &saved {
            if let Some(val) = v {
                // SAFETY: Serialized by ENV_LOCK; restoring pre-test env state.
                unsafe { env::set_var(k, val) };
            }
        }
    }

    #[test]
    fn test_apply_env_verify_level() {
        with_env_vars(&[("TRUST_VERIFY_LEVEL", "L2")], || {
            let mut config = TrustConfig::default();
            apply_env_overrides(&mut config);
            assert_eq!(config.level, "L2");
        });
    }

    #[test]
    fn test_apply_env_timeout() {
        with_env_vars(&[("TRUST_TIMEOUT_MS", "15000")], || {
            let mut config = TrustConfig::default();
            apply_env_overrides(&mut config);
            assert_eq!(config.timeout_ms, 15_000);
        });
    }

    #[test]
    fn test_apply_env_invalid_timeout_ignored() {
        with_env_vars(&[("TRUST_TIMEOUT_MS", "not_a_number")], || {
            let mut config = TrustConfig::default();
            apply_env_overrides(&mut config);
            assert_eq!(config.timeout_ms, 5_000); // default preserved
        });
    }

    #[test]
    fn test_apply_env_solver() {
        with_env_vars(&[("TRUST_SOLVER", "zani")], || {
            let mut config = TrustConfig::default();
            apply_env_overrides(&mut config);
            assert_eq!(config.solver.as_deref(), Some("zani"));
        });
    }

    #[test]
    fn test_apply_env_skip_functions_comma_separated() {
        with_env_vars(&[("TRUST_SKIP_FUNCTIONS", "test_, bench_, debug_")], || {
            let mut config = TrustConfig::default();
            apply_env_overrides(&mut config);
            assert_eq!(config.skip_functions, vec!["test_", "bench_", "debug_"]);
        });
    }

    #[test]
    fn test_apply_env_proof_level() {
        with_env_vars(&[("TRUST_PROOF_LEVEL", "L1")], || {
            let mut config = TrustConfig::default();
            apply_env_overrides(&mut config);
            assert_eq!(config.proof_level.as_deref(), Some("L1"));
        });
    }

    #[test]
    fn test_apply_env_cache_dir() {
        with_env_vars(&[("TRUST_CACHE_DIR", "/tmp/trust-cache")], || {
            let mut config = TrustConfig::default();
            apply_env_overrides(&mut config);
            assert_eq!(config.cache_dir, Some(PathBuf::from("/tmp/trust-cache")));
        });
    }

    #[test]
    fn test_apply_env_parallel() {
        with_env_vars(&[("TRUST_PARALLEL", "8")], || {
            let mut config = TrustConfig::default();
            apply_env_overrides(&mut config);
            assert_eq!(config.parallel, Some(8));
        });
    }

    #[test]
    fn test_apply_env_enabled_bool_variants() {
        for (val, expected) in [("true", true), ("false", false), ("1", true), ("0", false)] {
            with_env_vars(&[("TRUST_ENABLED", val)], || {
                let mut config = TrustConfig::default();
                apply_env_overrides(&mut config);
                assert_eq!(config.enabled, expected, "TRUST_ENABLED={val}");
            });
        }
    }

    #[test]
    fn test_parse_bool_variants() {
        assert_eq!(parse_bool("true"), Some(true));
        assert_eq!(parse_bool("TRUE"), Some(true));
        assert_eq!(parse_bool("1"), Some(true));
        assert_eq!(parse_bool("yes"), Some(true));
        assert_eq!(parse_bool("on"), Some(true));
        assert_eq!(parse_bool("false"), Some(false));
        assert_eq!(parse_bool("0"), Some(false));
        assert_eq!(parse_bool("no"), Some(false));
        assert_eq!(parse_bool("off"), Some(false));
        assert_eq!(parse_bool("maybe"), None);
    }

    #[test]
    fn test_empty_env_var_ignored() {
        with_env_vars(&[("TRUST_SOLVER", "")], || {
            let mut config = TrustConfig::default();
            apply_env_overrides(&mut config);
            assert!(config.solver.is_none());
        });
    }

    #[test]
    fn test_apply_env_disable_strengthen() {
        with_env_vars(&[("TRUST_DISABLE_STRENGTHEN", "1")], || {
            let mut config = TrustConfig::default();
            apply_env_overrides(&mut config);
            assert!(!config.strengthen, "TRUST_DISABLE_STRENGTHEN=1 should disable strengthen");
        });
    }

    #[test]
    fn test_apply_env_disable_cegar() {
        with_env_vars(&[("TRUST_DISABLE_CEGAR", "true")], || {
            let mut config = TrustConfig::default();
            apply_env_overrides(&mut config);
            assert!(!config.cegar, "TRUST_DISABLE_CEGAR=true should disable cegar");
        });
    }

    #[test]
    fn test_apply_env_disable_certify() {
        with_env_vars(&[("TRUST_DISABLE_CERTIFY", "yes")], || {
            let mut config = TrustConfig::default();
            apply_env_overrides(&mut config);
            assert!(!config.certify, "TRUST_DISABLE_CERTIFY=yes should disable certify");
        });
    }

    #[test]
    fn test_apply_env_disable_tv() {
        with_env_vars(&[("TRUST_DISABLE_TV", "on")], || {
            let mut config = TrustConfig::default();
            apply_env_overrides(&mut config);
            assert!(!config.tv, "TRUST_DISABLE_TV=on should disable tv");
        });
    }

    #[test]
    fn test_apply_env_disable_zero_means_keep_enabled() {
        with_env_vars(&[("TRUST_DISABLE_STRENGTHEN", "0")], || {
            let mut config = TrustConfig::default();
            apply_env_overrides(&mut config);
            assert!(config.strengthen, "TRUST_DISABLE_STRENGTHEN=0 should keep strengthen enabled");
        });
    }
}
