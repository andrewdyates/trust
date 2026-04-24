// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0
// Part of #895 (Phase 3: Build daemon). Milestone 1: priority ordering.
//
// The daemon ultimately runs a priority queue where lower numeric values are
// processed first. This milestone only defines the enum and a coarse
// classifier; a later milestone will add the per-argv classifier (fast
// `cargo check -p <crate>` vs. workspace check, per-crate test vs. full
// crate, etc.) and priority-aging/fairness mechanisms described in
// designs/2026-04-17-multi-agent-build-coordination.md §Component 5.

use crate::protocol::Request;

/// Priority of a request in the daemon's work queue. Lower values run first.
///
/// Values match the priority table in
/// `designs/2026-04-17-multi-agent-build-coordination.md` §Component 5 so
/// the enum ordering corresponds directly to scheduling precedence:
/// `Check < Test < Build < Clippy < Kani`.
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Priority {
    Check = 1,
    Test = 5,
    Build = 10,
    Clippy = 15,
    Kani = 20,
}

/// Classify a protocol [`Request`] into a [`Priority`].
///
/// The full classifier that distinguishes `cargo check -p <crate>` from
/// `cargo test -p <crate>` from `cargo kani` will operate on the raw argv
/// and be added in a later milestone. For now, any [`Request::Build`] maps
/// to [`Priority::Build`] and control-plane messages
/// ([`Request::HealthCheck`], [`Request::Shutdown`]) map to
/// [`Priority::Check`] so they never starve behind a long build.
#[must_use]
pub fn priority_for_request(req: &Request) -> Priority {
    match req {
        Request::Build { .. } => Priority::Build,
        Request::HealthCheck | Request::Shutdown => Priority::Check,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::protocol::Profile;

    #[test]
    fn test_priority_ordering_matches_design_table() {
        assert!(Priority::Check < Priority::Test);
        assert!(Priority::Test < Priority::Build);
        assert!(Priority::Build < Priority::Clippy);
        assert!(Priority::Clippy < Priority::Kani);
    }

    #[test]
    fn test_priority_numeric_values() {
        assert_eq!(Priority::Check as u8, 1);
        assert_eq!(Priority::Test as u8, 5);
        assert_eq!(Priority::Build as u8, 10);
        assert_eq!(Priority::Clippy as u8, 15);
        assert_eq!(Priority::Kani as u8, 20);
    }

    #[test]
    fn test_priority_for_build_request() {
        let req = Request::Build {
            crate_name: "trust-types".to_string(),
            profile: Profile::Dev,
            features: vec![],
        };
        assert_eq!(priority_for_request(&req), Priority::Build);
    }

    #[test]
    fn test_priority_for_health_check() {
        assert_eq!(priority_for_request(&Request::HealthCheck), Priority::Check);
    }

    #[test]
    fn test_priority_for_shutdown() {
        assert_eq!(priority_for_request(&Request::Shutdown), Priority::Check);
    }
}
