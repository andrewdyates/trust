//! Pause and resume running builds via POSIX signals.
//!
//! The scheduler uses these to apply emergency backpressure when memory
//! pressure reaches [`super::MemoryPressure::Critical`]: rather than killing
//! running builds (which wastes the work already done) we `SIGSTOP` them and
//! `SIGCONT` them once pressure drops.
//!
//! The implementation shells out to `/bin/kill` instead of pulling in a `libc`
//! dependency — these calls are infrequent (a few per backpressure event) and
//! keeping the dep surface small matters for a build-system daemon that will
//! be part of every compile. The socket server milestone can revisit this if
//! signal delivery latency becomes a concern.
//!
//! Part of #895, epic #894.

use std::io;
use std::process::Command;

use thiserror::Error;

/// Errors produced by [`stop_build`] / [`resume_build`].
#[derive(Debug, Error)]
pub enum BackpressureError {
    /// Spawning `/bin/kill` failed, or reading its exit status did.
    #[error("signal delivery failed: {0}")]
    SignalFailed(#[from] io::Error),
}

/// Send `SIGSTOP` to the given PID, pausing the process.
///
/// Idempotent: already-stopped processes simply remain stopped.
pub fn stop_build(pid: u32) -> Result<(), BackpressureError> {
    send_signal(pid, "-STOP")
}

/// Send `SIGCONT` to the given PID, resuming a previously-stopped process.
///
/// Safe to call on running processes — `SIGCONT` is a no-op for them.
pub fn resume_build(pid: u32) -> Result<(), BackpressureError> {
    send_signal(pid, "-CONT")
}

fn send_signal(pid: u32, signal_arg: &str) -> Result<(), BackpressureError> {
    let status = Command::new("/bin/kill").args([signal_arg, &pid.to_string()]).status()?;
    if !status.success() {
        return Err(BackpressureError::SignalFailed(io::Error::other(format!(
            "/bin/kill {signal_arg} {pid} exited {status}"
        ))));
    }
    Ok(())
}

#[cfg(all(test, target_os = "macos"))]
mod tests {
    use super::*;
    use std::process::{Command, Stdio};
    use std::thread::sleep;
    use std::time::{Duration, Instant};

    /// Read `ps -o state= -p <pid>` and return its first non-empty line.
    fn process_state(pid: u32) -> Option<String> {
        let out =
            Command::new("ps").args(["-o", "state=", "-p", &pid.to_string()]).output().ok()?;
        if !out.status.success() {
            return None;
        }
        let stdout = String::from_utf8_lossy(&out.stdout);
        stdout.lines().map(str::trim).find(|line| !line.is_empty()).map(ToString::to_string)
    }

    /// Poll `process_state` until `predicate` returns true or `timeout` elapses.
    /// Returns the last observed state (or `None` if the process vanished).
    fn wait_for_state<F: Fn(&str) -> bool>(
        pid: u32,
        predicate: F,
        timeout: Duration,
    ) -> Option<String> {
        let deadline = Instant::now() + timeout;
        let mut last = process_state(pid);
        while Instant::now() < deadline {
            if let Some(ref s) = last {
                if predicate(s) {
                    return Some(s.clone());
                }
            }
            sleep(Duration::from_millis(20));
            last = process_state(pid);
        }
        last
    }

    #[test]
    fn test_stop_and_resume_build_round_trip() {
        // Spawn a long-lived, harmless child we can signal.
        let mut child = Command::new("sleep")
            .arg("30")
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .spawn()
            .expect("spawn sleep child");
        let pid = child.id();

        // Stop it.
        stop_build(pid).expect("stop_build succeeds");
        let stopped = wait_for_state(pid, |s| s.contains('T'), Duration::from_millis(500));
        assert!(
            stopped.as_deref().is_some_and(|s| s.contains('T')),
            "process should report stopped state 'T'; got {stopped:?}"
        );

        // Resume it.
        resume_build(pid).expect("resume_build succeeds");
        let running = wait_for_state(pid, |s| !s.contains('T'), Duration::from_millis(500));
        assert!(
            running.as_deref().is_some_and(|s| !s.contains('T')),
            "process should no longer report stopped state 'T'; got {running:?}"
        );

        // Clean up.
        child.kill().expect("kill sleep child");
        let _ = child.wait();
    }
}
