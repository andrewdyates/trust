//! Compute per-build `--jobs` caps.
//!
//! The scheduler gives each concurrent build `floor(total_cpus / active)` jobs
//! as a baseline, then clamps that based on memory pressure. The logic is
//! intentionally pure: it takes only the number of CPUs, the active-build
//! count, and a [`MemoryPressure`], and returns a `u32`. The socket server
//! milestone will call this from the dispatch path.
//!
//! Part of #895, epic #894.

use super::memory_pressure::MemoryPressure;

/// Compute the per-build `--jobs` cap.
///
/// # Semantics
/// - `active_builds == 0` is treated as 1 (a single build about to start).
/// - Baseline cap = `max(1, total_cpus / active_builds)` (integer floor).
/// - `MemoryPressure::Normal`: baseline.
/// - `MemoryPressure::Warn`: `max(1, baseline / 2)`.
/// - `MemoryPressure::Critical`: always `1`.
/// - If `total_cpus == 0` we return `1` to avoid handing out a zero cap (no
///   caller wants `cargo --jobs 0`).
#[must_use]
pub fn compute_job_cap(total_cpus: u32, active_builds: u32, pressure: MemoryPressure) -> u32 {
    if total_cpus == 0 {
        return 1;
    }
    if matches!(pressure, MemoryPressure::Critical) {
        return 1;
    }
    let effective_active = active_builds.max(1);
    let baseline = (total_cpus / effective_active).max(1);
    match pressure {
        MemoryPressure::Normal => baseline,
        MemoryPressure::Warn => (baseline / 2).max(1),
        // Critical handled above.
        MemoryPressure::Critical => 1,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Acceptance criteria from the dispatch: 1 build -> 16, 4 -> 4, 16 -> 1.

    #[test]
    fn test_compute_job_cap_single_build_gets_all_cpus() {
        assert_eq!(compute_job_cap(16, 1, MemoryPressure::Normal), 16);
    }

    #[test]
    fn test_compute_job_cap_four_builds_split_evenly() {
        assert_eq!(compute_job_cap(16, 4, MemoryPressure::Normal), 4);
    }

    #[test]
    fn test_compute_job_cap_saturated_yields_one_job_each() {
        assert_eq!(compute_job_cap(16, 16, MemoryPressure::Normal), 1);
    }

    #[test]
    fn test_compute_job_cap_over_saturated_clamps_to_one() {
        assert_eq!(compute_job_cap(16, 32, MemoryPressure::Normal), 1);
    }

    #[test]
    fn test_compute_job_cap_zero_active_treated_as_one() {
        assert_eq!(compute_job_cap(16, 0, MemoryPressure::Normal), 16);
    }

    #[test]
    fn test_compute_job_cap_warn_halves_baseline() {
        assert_eq!(compute_job_cap(16, 4, MemoryPressure::Warn), 2);
    }

    #[test]
    fn test_compute_job_cap_warn_floor_is_one() {
        // baseline 1 halved would be 0; clamp to 1.
        assert_eq!(compute_job_cap(16, 16, MemoryPressure::Warn), 1);
    }

    #[test]
    fn test_compute_job_cap_critical_forces_one() {
        assert_eq!(compute_job_cap(16, 4, MemoryPressure::Critical), 1);
        assert_eq!(compute_job_cap(16, 1, MemoryPressure::Critical), 1);
    }

    #[test]
    fn test_compute_job_cap_zero_cpus_returns_one() {
        // Pathological input; never return 0 jobs.
        assert_eq!(compute_job_cap(0, 4, MemoryPressure::Normal), 1);
    }

    #[test]
    fn test_compute_job_cap_non_divisible_uses_floor() {
        // 10 cpus / 3 active = 3 (floor), not 4.
        assert_eq!(compute_job_cap(10, 3, MemoryPressure::Normal), 3);
    }
}
