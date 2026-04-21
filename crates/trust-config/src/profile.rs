//! trust-config: Verification profiles
//!
//! Pre-defined profiles that configure timeout, solver, and proof level
//! for common use cases. Profiles provide sensible defaults that can be
//! further customized via config file or environment overrides.
//!
//! Author: Andrew Yates <andrew@andrewdyates.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::TrustConfig;

/// tRust: Pre-defined verification intensity profiles.
///
/// Each profile sets defaults for timeout, solver, and proof level.
/// Applied before file/env overrides, so users can still customize.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum VerificationProfile {
    /// Fast feedback: short timeout, basic safety checks only.
    /// Good for IDE integration and rapid development.
    Quick,
    /// Balanced: moderate timeout, standard safety + functional checks.
    /// Default for `cargo trust check`.
    Standard,
    /// Deep analysis: longer timeout, all proof levels.
    /// Good for CI pipelines and pre-merge checks.
    Thorough,
    /// Maximum rigor: longest timeout, all solvers, all levels.
    /// Good for release verification and formal audits.
    Exhaustive,
}

impl VerificationProfile {
    /// tRust: Parse a profile name from a string (case-insensitive).
    #[must_use]
    pub fn from_name(name: &str) -> Option<Self> {
        match name.to_lowercase().as_str() {
            "quick" => Some(Self::Quick),
            "standard" => Some(Self::Standard),
            "thorough" => Some(Self::Thorough),
            "exhaustive" => Some(Self::Exhaustive),
            _ => None,
        }
    }

    /// tRust: Get the human-readable name of this profile.
    #[must_use]
    pub fn name(self) -> &'static str {
        match self {
            Self::Quick => "quick",
            Self::Standard => "standard",
            Self::Thorough => "thorough",
            Self::Exhaustive => "exhaustive",
        }
    }

    /// tRust: Get the timeout in milliseconds for this profile.
    #[must_use]
    pub fn timeout_ms(self) -> u64 {
        match self {
            Self::Quick => 1_000,
            Self::Standard => 5_000,
            Self::Thorough => 30_000,
            Self::Exhaustive => 120_000,
        }
    }

    /// tRust: Get the default solver for this profile.
    #[must_use]
    pub fn solver(self) -> &'static str {
        match self {
            Self::Quick => "z4",
            Self::Standard => "z4",
            Self::Thorough => "z4",
            Self::Exhaustive => "z4",
        }
    }

    /// tRust: Get the default verification level for this profile.
    #[must_use]
    pub fn level(self) -> &'static str {
        match self {
            Self::Quick => "L0",
            Self::Standard => "L0",
            Self::Thorough => "L1",
            Self::Exhaustive => "L2",
        }
    }

    /// tRust: Get the default proof level for this profile.
    #[must_use]
    pub fn proof_level(self) -> &'static str {
        match self {
            Self::Quick => "L0",
            Self::Standard => "L0",
            Self::Thorough => "L1",
            Self::Exhaustive => "L2",
        }
    }

    /// tRust: Get the default parallel worker count for this profile.
    #[must_use]
    pub fn parallel(self) -> u32 {
        match self {
            Self::Quick => 1,
            Self::Standard => 2,
            Self::Thorough => 4,
            Self::Exhaustive => 8,
        }
    }
}

/// tRust: Apply a verification profile to a config.
///
/// Sets timeout, solver, level, proof_level, and parallel from the profile
/// defaults. Only overwrites fields that are at their default values, so
/// explicit user settings in the config file are preserved.
pub fn apply_profile(config: &mut TrustConfig, profile: VerificationProfile) {
    let defaults = TrustConfig::default();

    // Only override fields still at default values
    if config.timeout_ms == defaults.timeout_ms {
        config.timeout_ms = profile.timeout_ms();
    }
    if config.level == defaults.level {
        config.level = profile.level().to_string();
    }
    if config.solver.is_none() {
        config.solver = Some(profile.solver().to_string());
    }
    if config.proof_level.is_none() {
        config.proof_level = Some(profile.proof_level().to_string());
    }
    if config.parallel.is_none() {
        config.parallel = Some(profile.parallel());
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_profile_from_name_case_insensitive() {
        assert_eq!(
            VerificationProfile::from_name("Quick"),
            Some(VerificationProfile::Quick)
        );
        assert_eq!(
            VerificationProfile::from_name("THOROUGH"),
            Some(VerificationProfile::Thorough)
        );
        assert_eq!(
            VerificationProfile::from_name("exhaustive"),
            Some(VerificationProfile::Exhaustive)
        );
        assert_eq!(VerificationProfile::from_name("bogus"), None);
    }

    #[test]
    fn test_profile_name_roundtrip() {
        for profile in [
            VerificationProfile::Quick,
            VerificationProfile::Standard,
            VerificationProfile::Thorough,
            VerificationProfile::Exhaustive,
        ] {
            assert_eq!(
                VerificationProfile::from_name(profile.name()),
                Some(profile)
            );
        }
    }

    #[test]
    fn test_apply_profile_quick_sets_short_timeout() {
        let mut config = TrustConfig::default();
        apply_profile(&mut config, VerificationProfile::Quick);
        assert_eq!(config.timeout_ms, 1_000);
        assert_eq!(config.level, "L0");
        assert_eq!(config.solver.as_deref(), Some("z4"));
        assert_eq!(config.parallel, Some(1));
    }

    #[test]
    fn test_apply_profile_exhaustive_sets_max_rigor() {
        let mut config = TrustConfig::default();
        apply_profile(&mut config, VerificationProfile::Exhaustive);
        assert_eq!(config.timeout_ms, 120_000);
        assert_eq!(config.level, "L2");
        assert_eq!(config.proof_level.as_deref(), Some("L2"));
        assert_eq!(config.parallel, Some(8));
    }

    #[test]
    fn test_apply_profile_preserves_explicit_settings() {
        let mut config = TrustConfig {
            timeout_ms: 999,
            solver: Some("zani".to_string()),
            ..Default::default()
        };
        apply_profile(&mut config, VerificationProfile::Exhaustive);
        // Explicit settings preserved
        assert_eq!(config.timeout_ms, 999);
        assert_eq!(config.solver.as_deref(), Some("zani"));
        // Defaults overridden by profile
        assert_eq!(config.level, "L2");
        assert_eq!(config.parallel, Some(8));
    }

    #[test]
    fn test_profile_timeout_ordering() {
        assert!(VerificationProfile::Quick.timeout_ms() < VerificationProfile::Standard.timeout_ms());
        assert!(
            VerificationProfile::Standard.timeout_ms() < VerificationProfile::Thorough.timeout_ms()
        );
        assert!(
            VerificationProfile::Thorough.timeout_ms()
                < VerificationProfile::Exhaustive.timeout_ms()
        );
    }
}
