//! trust-config: Built-in configuration presets
//!
//! Provides named presets (Quick, Standard, Thorough, Paranoid, CiPipeline,
//! Development) that configure verification settings for common scenarios.
//! Presets can be applied to replace a config or merged to keep user overrides.
//!
//! Author: Andrew Yates <andrew@andrewdyates.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::TrustConfig;

/// tRust: Built-in verification presets for common scenarios.
///
/// Each preset configures timeout, level, solver, parallelism, and other
/// settings for a specific use case. Use [`apply_preset`] to replace config
/// fields or [`merge_preset`] to overlay preset values while keeping user
/// overrides.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum Preset {
    /// Minimal checks, fast feedback loop.
    /// Timeout: 5s, no liveness, skip complex properties.
    Quick,
    /// Balanced verification for everyday development.
    /// Timeout: 30s, basic liveness, all safety properties.
    Standard,
    /// Comprehensive verification for thorough analysis.
    /// Timeout: 120s, full liveness, temporal, loop invariants.
    Thorough,
    /// Maximum verification rigor.
    /// Timeout: 600s, all properties, multiple solvers.
    Paranoid,
    /// Optimized for CI/CD pipelines.
    /// Timeout: 60s, parallel, fail-fast.
    CiPipeline,
    /// Development-focused: incremental, changed functions only.
    /// Timeout: 10s, fast iteration.
    Development,
}

impl Preset {
    /// Parse a preset name from a string (case-insensitive).
    #[must_use]
    pub fn from_name(name: &str) -> Option<Self> {
        match name.to_lowercase().as_str() {
            "quick" => Some(Self::Quick),
            "standard" => Some(Self::Standard),
            "thorough" => Some(Self::Thorough),
            "paranoid" => Some(Self::Paranoid),
            "ci" | "ci_pipeline" | "ci-pipeline" | "cipipeline" => Some(Self::CiPipeline),
            "dev" | "development" => Some(Self::Development),
            _ => None,
        }
    }

    /// Get the canonical name of this preset.
    #[must_use]
    pub fn name(self) -> &'static str {
        match self {
            Self::Quick => "quick",
            Self::Standard => "standard",
            Self::Thorough => "thorough",
            Self::Paranoid => "paranoid",
            Self::CiPipeline => "ci-pipeline",
            Self::Development => "development",
        }
    }

    /// Return all available presets.
    #[must_use]
    pub fn all() -> &'static [Self] {
        &[
            Self::Quick,
            Self::Standard,
            Self::Thorough,
            Self::Paranoid,
            Self::CiPipeline,
            Self::Development,
        ]
    }

    /// Timeout in milliseconds for this preset.
    #[must_use]
    pub fn timeout_ms(self) -> u64 {
        match self {
            Self::Quick => 5_000,
            Self::Standard => 30_000,
            Self::Thorough => 120_000,
            Self::Paranoid => 600_000,
            Self::CiPipeline => 60_000,
            Self::Development => 10_000,
        }
    }

    /// Verification level for this preset.
    #[must_use]
    pub fn level(self) -> &'static str {
        match self {
            Self::Quick => "L0",
            Self::Standard => "L0",
            Self::Thorough => "L1",
            Self::Paranoid => "L2",
            Self::CiPipeline => "L1",
            Self::Development => "L0",
        }
    }

    /// Solver selection for this preset.
    #[must_use]
    pub fn solver(self) -> Option<&'static str> {
        match self {
            Self::Quick => Some("z4"),
            Self::Standard => Some("z4"),
            Self::Thorough => Some("z4"),
            Self::Paranoid => None, // router selects — tries multiple
            Self::CiPipeline => Some("z4"),
            Self::Development => Some("z4"),
        }
    }

    /// Proof level for this preset.
    #[must_use]
    pub fn proof_level(self) -> &'static str {
        match self {
            Self::Quick => "L0",
            Self::Standard => "L0",
            Self::Thorough => "L1",
            Self::Paranoid => "L2",
            Self::CiPipeline => "L1",
            Self::Development => "L0",
        }
    }

    /// Parallel worker count for this preset.
    #[must_use]
    pub fn parallel(self) -> u32 {
        match self {
            Self::Quick => 1,
            Self::Standard => 2,
            Self::Thorough => 4,
            Self::Paranoid => 8,
            Self::CiPipeline => 4,
            Self::Development => 1,
        }
    }
}

/// tRust: Apply a preset to a config, replacing all preset-managed fields.
///
/// This overwrites timeout, level, solver, proof_level, and parallel
/// unconditionally. Use [`merge_preset`] to keep user overrides.
#[must_use]
pub fn apply_preset(config: &TrustConfig, preset: Preset) -> TrustConfig {
    TrustConfig {
        enabled: config.enabled,
        level: preset.level().to_string(),
        timeout_ms: preset.timeout_ms(),
        skip_functions: config.skip_functions.clone(),
        verify_functions: config.verify_functions.clone(),
        solver: preset.solver().map(String::from),
        proof_level: Some(preset.proof_level().to_string()),
        cache_dir: config.cache_dir.clone(),
        parallel: Some(preset.parallel()),
        strengthen: config.strengthen,
        cegar: config.cegar,
        certify: config.certify,
        tv: config.tv,
        report_format: config.report_format.clone(),
        solver_memory_limit_mb: config.solver_memory_limit_mb,
    }
}

/// tRust: Merge a preset into a config, preserving user overrides.
///
/// Only sets fields that are still at their default values. If the user
/// has explicitly configured a field, the preset does not overwrite it.
#[must_use]
pub fn merge_preset(config: &TrustConfig, preset: Preset) -> TrustConfig {
    let defaults = TrustConfig::default();
    TrustConfig {
        enabled: config.enabled,
        level: if config.level == defaults.level {
            preset.level().to_string()
        } else {
            config.level.clone()
        },
        timeout_ms: if config.timeout_ms == defaults.timeout_ms {
            preset.timeout_ms()
        } else {
            config.timeout_ms
        },
        skip_functions: config.skip_functions.clone(),
        verify_functions: config.verify_functions.clone(),
        solver: if config.solver.is_none() {
            preset.solver().map(String::from)
        } else {
            config.solver.clone()
        },
        proof_level: if config.proof_level.is_none() {
            Some(preset.proof_level().to_string())
        } else {
            config.proof_level.clone()
        },
        cache_dir: config.cache_dir.clone(),
        parallel: if config.parallel.is_none() { Some(preset.parallel()) } else { config.parallel },
        strengthen: config.strengthen,
        cegar: config.cegar,
        certify: config.certify,
        tv: config.tv,
        report_format: config.report_format.clone(),
        solver_memory_limit_mb: config.solver_memory_limit_mb,
    }
}

/// tRust: Get a human-readable description of a preset.
#[must_use]
pub fn describe_preset(preset: Preset) -> String {
    match preset {
        Preset::Quick => format!(
            "Quick: Minimal checks for fast feedback. \
             Timeout {}s, level {}, {} worker. \
             Skips complex properties like liveness and temporal logic.",
            preset.timeout_ms() / 1000,
            preset.level(),
            preset.parallel(),
        ),
        Preset::Standard => format!(
            "Standard: Balanced verification for daily development. \
             Timeout {}s, level {}, {} workers. \
             Checks all safety properties with basic liveness.",
            preset.timeout_ms() / 1000,
            preset.level(),
            preset.parallel(),
        ),
        Preset::Thorough => format!(
            "Thorough: Comprehensive analysis for pre-merge checks. \
             Timeout {}s, level {}, {} workers. \
             Full liveness, temporal properties, and loop invariants.",
            preset.timeout_ms() / 1000,
            preset.level(),
            preset.parallel(),
        ),
        Preset::Paranoid => format!(
            "Paranoid: Maximum verification rigor for releases. \
             Timeout {}s, level {}, {} workers. \
             All property classes, multiple solver backends, full proof depth.",
            preset.timeout_ms() / 1000,
            preset.level(),
            preset.parallel(),
        ),
        Preset::CiPipeline => format!(
            "CI Pipeline: Optimized for continuous integration. \
             Timeout {}s, level {}, {} workers. \
             Parallel execution with fail-fast on first error.",
            preset.timeout_ms() / 1000,
            preset.level(),
            preset.parallel(),
        ),
        Preset::Development => format!(
            "Development: Focused on changed functions only. \
             Timeout {}s, level {}, {} worker. \
             Incremental verification for fast iteration.",
            preset.timeout_ms() / 1000,
            preset.level(),
            preset.parallel(),
        ),
    }
}

/// tRust: Suggest a preset based on project characteristics.
///
/// `project_size` is an estimate of the number of functions to verify.
/// `ci_mode` indicates whether we're running in a CI environment.
#[must_use]
pub fn suggest_preset(project_size: usize, ci_mode: bool) -> Preset {
    if ci_mode {
        return Preset::CiPipeline;
    }
    match project_size {
        0..=10 => Preset::Thorough,
        11..=100 => Preset::Standard,
        101..=500 => Preset::Quick,
        _ => Preset::Quick,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // -- Preset name parsing --

    #[test]
    fn test_preset_from_name_all_variants() {
        assert_eq!(Preset::from_name("quick"), Some(Preset::Quick));
        assert_eq!(Preset::from_name("standard"), Some(Preset::Standard));
        assert_eq!(Preset::from_name("thorough"), Some(Preset::Thorough));
        assert_eq!(Preset::from_name("paranoid"), Some(Preset::Paranoid));
        assert_eq!(Preset::from_name("ci"), Some(Preset::CiPipeline));
        assert_eq!(Preset::from_name("ci_pipeline"), Some(Preset::CiPipeline));
        assert_eq!(Preset::from_name("ci-pipeline"), Some(Preset::CiPipeline));
        assert_eq!(Preset::from_name("cipipeline"), Some(Preset::CiPipeline));
        assert_eq!(Preset::from_name("dev"), Some(Preset::Development));
        assert_eq!(Preset::from_name("development"), Some(Preset::Development));
    }

    #[test]
    fn test_preset_from_name_case_insensitive() {
        assert_eq!(Preset::from_name("QUICK"), Some(Preset::Quick));
        assert_eq!(Preset::from_name("Paranoid"), Some(Preset::Paranoid));
        assert_eq!(Preset::from_name("CI_PIPELINE"), Some(Preset::CiPipeline));
    }

    #[test]
    fn test_preset_from_name_unknown() {
        assert_eq!(Preset::from_name("bogus"), None);
        assert_eq!(Preset::from_name(""), None);
    }

    #[test]
    fn test_preset_name_roundtrip() {
        for preset in Preset::all() {
            assert_eq!(
                Preset::from_name(preset.name()),
                Some(*preset),
                "roundtrip failed for {:?}",
                preset,
            );
        }
    }

    // -- Preset properties --

    #[test]
    fn test_preset_timeout_ordering() {
        assert!(Preset::Quick.timeout_ms() < Preset::Standard.timeout_ms());
        assert!(Preset::Standard.timeout_ms() < Preset::Thorough.timeout_ms());
        assert!(Preset::Thorough.timeout_ms() < Preset::Paranoid.timeout_ms());
    }

    #[test]
    fn test_preset_all_returns_six() {
        assert_eq!(Preset::all().len(), 6);
    }

    #[test]
    fn test_paranoid_has_no_solver_for_multi_solver() {
        assert!(Preset::Paranoid.solver().is_none());
    }

    #[test]
    fn test_non_paranoid_presets_have_z4() {
        for preset in [
            Preset::Quick,
            Preset::Standard,
            Preset::Thorough,
            Preset::CiPipeline,
            Preset::Development,
        ] {
            assert_eq!(preset.solver(), Some("z4"), "{:?} should use z4", preset);
        }
    }

    // -- apply_preset tests --

    #[test]
    fn test_apply_preset_quick() {
        let config = TrustConfig::default();
        let result = apply_preset(&config, Preset::Quick);
        assert_eq!(result.timeout_ms, 5_000);
        assert_eq!(result.level, "L0");
        assert_eq!(result.solver.as_deref(), Some("z4"));
        assert_eq!(result.parallel, Some(1));
    }

    #[test]
    fn test_apply_preset_paranoid() {
        let config = TrustConfig::default();
        let result = apply_preset(&config, Preset::Paranoid);
        assert_eq!(result.timeout_ms, 600_000);
        assert_eq!(result.level, "L2");
        assert!(result.solver.is_none()); // multi-solver
        assert_eq!(result.proof_level.as_deref(), Some("L2"));
        assert_eq!(result.parallel, Some(8));
    }

    #[test]
    fn test_apply_preset_ci_pipeline() {
        let config = TrustConfig::default();
        let result = apply_preset(&config, Preset::CiPipeline);
        assert_eq!(result.timeout_ms, 60_000);
        assert_eq!(result.level, "L1");
        assert_eq!(result.parallel, Some(4));
    }

    #[test]
    fn test_apply_preset_preserves_non_preset_fields() {
        let config = TrustConfig {
            enabled: false,
            skip_functions: vec!["test_".to_string()],
            cache_dir: Some(std::path::PathBuf::from("/my/cache")),
            ..Default::default()
        };
        let result = apply_preset(&config, Preset::Thorough);
        // Non-preset fields preserved
        assert!(!result.enabled);
        assert_eq!(result.skip_functions, vec!["test_"]);
        assert_eq!(result.cache_dir, Some(std::path::PathBuf::from("/my/cache")));
        // Preset fields applied
        assert_eq!(result.timeout_ms, 120_000);
        assert_eq!(result.level, "L1");
    }

    #[test]
    fn test_apply_preset_preserves_feature_flags() {
        let config = TrustConfig {
            strengthen: false,
            cegar: false,
            certify: false,
            tv: false,
            ..Default::default()
        };
        let result = apply_preset(&config, Preset::Thorough);
        assert!(!result.strengthen);
        assert!(!result.cegar);
        assert!(!result.certify);
        assert!(!result.tv);
    }

    #[test]
    fn test_apply_preset_overwrites_user_settings() {
        let config =
            TrustConfig { timeout_ms: 999, solver: Some("zani".to_string()), ..Default::default() };
        let result = apply_preset(&config, Preset::Quick);
        // apply_preset always overwrites
        assert_eq!(result.timeout_ms, 5_000);
        assert_eq!(result.solver.as_deref(), Some("z4"));
    }

    // -- merge_preset tests --

    #[test]
    fn test_merge_preset_applies_to_defaults() {
        let config = TrustConfig::default();
        let result = merge_preset(&config, Preset::Thorough);
        assert_eq!(result.timeout_ms, 120_000);
        assert_eq!(result.level, "L1");
        assert_eq!(result.parallel, Some(4));
    }

    #[test]
    fn test_merge_preset_preserves_user_overrides() {
        let config =
            TrustConfig { timeout_ms: 999, solver: Some("zani".to_string()), ..Default::default() };
        let result = merge_preset(&config, Preset::Paranoid);
        // User values preserved
        assert_eq!(result.timeout_ms, 999);
        assert_eq!(result.solver.as_deref(), Some("zani"));
        // Default fields get preset values
        assert_eq!(result.level, "L2");
        assert_eq!(result.parallel, Some(8));
    }

    #[test]
    fn test_merge_preset_preserves_feature_flags() {
        let config = TrustConfig {
            strengthen: false,
            cegar: false,
            certify: false,
            tv: false,
            ..Default::default()
        };
        let result = merge_preset(&config, Preset::Quick);
        assert!(!result.strengthen);
        assert!(!result.cegar);
        assert!(!result.certify);
        assert!(!result.tv);
    }

    #[test]
    fn test_merge_vs_apply_priority() {
        let config = TrustConfig { timeout_ms: 42, ..Default::default() };

        let applied = apply_preset(&config, Preset::Standard);
        let merged = merge_preset(&config, Preset::Standard);

        // apply overwrites; merge preserves
        assert_eq!(applied.timeout_ms, 30_000);
        assert_eq!(merged.timeout_ms, 42);

        // Both set default fields the same way
        assert_eq!(applied.level, merged.level);
    }

    // -- describe_preset tests --

    #[test]
    fn test_describe_preset_non_empty() {
        for preset in Preset::all() {
            let desc = describe_preset(*preset);
            assert!(!desc.is_empty(), "description for {:?} should not be empty", preset);
        }
    }

    #[test]
    fn test_describe_preset_contains_timeout() {
        let desc = describe_preset(Preset::Quick);
        assert!(desc.contains("5s"), "Quick description should mention 5s timeout");
    }

    #[test]
    fn test_describe_preset_contains_name() {
        let desc = describe_preset(Preset::Paranoid);
        assert!(desc.contains("Paranoid"), "description should contain preset name");
    }

    // -- suggest_preset tests --

    #[test]
    fn test_suggest_preset_ci_mode() {
        assert_eq!(suggest_preset(5, true), Preset::CiPipeline);
        assert_eq!(suggest_preset(1000, true), Preset::CiPipeline);
    }

    #[test]
    fn test_suggest_preset_small_project() {
        assert_eq!(suggest_preset(5, false), Preset::Thorough);
    }

    #[test]
    fn test_suggest_preset_medium_project() {
        assert_eq!(suggest_preset(50, false), Preset::Standard);
    }

    #[test]
    fn test_suggest_preset_large_project() {
        assert_eq!(suggest_preset(200, false), Preset::Quick);
        assert_eq!(suggest_preset(1000, false), Preset::Quick);
    }

    // -- Development preset --

    #[test]
    fn test_development_preset_values() {
        let config = TrustConfig::default();
        let result = apply_preset(&config, Preset::Development);
        assert_eq!(result.timeout_ms, 10_000);
        assert_eq!(result.level, "L0");
        assert_eq!(result.parallel, Some(1));
        assert_eq!(result.solver.as_deref(), Some("z4"));
    }
}
