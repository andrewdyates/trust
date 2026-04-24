//! Memory-aware scheduler for concurrent cargo builds.
//!
//! Combines three concerns (one submodule each):
//! - [`memory_pressure`]: read macOS memory pressure state via the
//!   `memory_pressure -Q` tool, or fall back to parsing `vm_stat`.
//! - [`job_caps`]: compute per-build `--jobs` caps given the number of active
//!   builds and the current memory pressure.
//! - [`backpressure`]: pause/resume running builds via `SIGSTOP` / `SIGCONT`.
//!
//! Part of #895 (build daemon), epic #894.

pub mod backpressure;
pub mod job_caps;
pub mod memory_pressure;

pub use backpressure::{BackpressureError, resume_build, stop_build};
pub use job_caps::compute_job_cap;
pub use memory_pressure::{MemoryPressure, MemoryPressureError, read_memory_pressure};

/// High-level memory-aware scheduler.
///
/// Holds the last-observed memory pressure and the host's total logical CPU
/// count, and computes per-build job caps for incoming build requests via
/// [`compute_job_cap`]. The socket server milestone will wrap this in a
/// `Mutex` and refresh `last_pressure` periodically.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct MemoryAwareScheduler {
    /// Total logical CPUs on the host. Upper bound for job caps.
    pub total_cpus: u32,
    /// Most recently observed memory pressure.
    pub last_pressure: MemoryPressure,
}

impl MemoryAwareScheduler {
    /// Construct a scheduler for a host with `total_cpus` logical CPUs. The
    /// initial pressure state is [`MemoryPressure::Normal`].
    #[must_use]
    pub fn new(total_cpus: u32) -> Self {
        Self { total_cpus, last_pressure: MemoryPressure::Normal }
    }

    /// Update [`Self::last_pressure`] to `pressure`.
    pub fn set_pressure(&mut self, pressure: MemoryPressure) {
        self.last_pressure = pressure;
    }

    /// Compute the per-build `jobs` cap given `active_builds`. Caps scale down
    /// under [`MemoryPressure::Warn`] and collapse to 1 under
    /// [`MemoryPressure::Critical`]. See [`compute_job_cap`] for the exact
    /// formula.
    #[must_use]
    pub fn job_cap(&self, active_builds: u32) -> u32 {
        compute_job_cap(self.total_cpus, active_builds, self.last_pressure)
    }
}
