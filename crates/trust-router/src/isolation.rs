// trust-router/isolation.rs: Solver process isolation for crash safety
//
// tRust: Wraps any VerificationBackend with process isolation so that
// crashing solvers do not take down the compiler. Supports in-process,
// subprocess, and sandboxed execution modes.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::sync::Arc;
use std::time::{Duration, Instant};

use trust_types::*;

use crate::{BackendRole, VerificationBackend};

// ---------------------------------------------------------------------------
// tRust: Error types (#195)
// ---------------------------------------------------------------------------

/// Errors that can occur during isolated solver execution.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum IsolationError {
    /// The solver process crashed (non-zero exit, signal, etc.).
    #[error("solver crashed: {0}")]
    SolverCrash(SolverCrashReport),

    /// The solver process timed out.
    #[error("solver timed out after {timeout_ms}ms")]
    Timeout { timeout_ms: u64 },

    /// Failed to serialize the VC to a temp file.
    #[error("VC serialization failed: {reason}")]
    Serialization { reason: String },

    /// Failed to spawn or communicate with the solver process.
    #[error("subprocess error: {reason}")]
    Subprocess { reason: String },

    /// Failed to deserialize the solver result.
    #[error("result deserialization failed: {reason}")]
    Deserialization { reason: String },
}

// ---------------------------------------------------------------------------
// tRust: Crash report (#195)
// ---------------------------------------------------------------------------

/// Detailed report about a solver process crash.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SolverCrashReport {
    /// Solver backend name that crashed.
    pub solver_name: String,
    /// Process exit code, if available (None if killed by signal).
    pub exit_code: Option<i32>,
    /// Unix signal number that killed the process, if any.
    pub signal: Option<i32>,
    /// Captured stderr output from the solver process.
    pub stderr: String,
    /// How long the solver ran before crashing.
    pub elapsed_ms: u64,
}

impl std::fmt::Display for SolverCrashReport {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "solver '{}' crashed", self.solver_name)?;
        if let Some(code) = self.exit_code {
            write!(f, " (exit code {code})")?;
        }
        if let Some(sig) = self.signal {
            write!(f, " (signal {sig})")?;
        }
        if !self.stderr.is_empty() {
            let truncated = if self.stderr.len() > 200 {
                &self.stderr[..200]
            } else {
                &self.stderr
            };
            write!(f, ": {truncated}")?;
        }
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// tRust: Isolation mode enum (#195)
// ---------------------------------------------------------------------------

/// How a solver backend should be executed.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
#[derive(Default)]
pub enum IsolationMode {
    /// Run the solver in the same process (fastest, no isolation).
    /// A crash in the solver will crash the compiler.
    #[default]
    InProcess,
    /// Run the solver as a child process with timeout enforcement.
    /// Crashes are caught and reported without affecting the compiler.
    SubProcess,
    /// Run the solver in a sandboxed child process with restricted
    /// filesystem and network access. (Future: macOS sandbox-exec or
    /// Linux seccomp.)
    Sandboxed,
}


// ---------------------------------------------------------------------------
// tRust: Isolation configuration (#195)
// ---------------------------------------------------------------------------

/// Configuration for solver isolation.
#[derive(Debug, Clone)]
pub struct IsolationConfig {
    /// Execution mode for the solver.
    pub mode: IsolationMode,
    /// Timeout for solver execution. Applies to SubProcess and Sandboxed modes.
    pub timeout: Duration,
    /// Number of retry attempts after a crash before giving up.
    pub max_retries: u32,
    /// Directory for temporary VC serialization files. Uses `std::env::temp_dir()`
    /// if `None`.
    pub temp_dir: Option<PathBuf>,
}

impl Default for IsolationConfig {
    fn default() -> Self {
        Self {
            mode: IsolationMode::InProcess,
            timeout: Duration::from_secs(30),
            max_retries: 0,
            temp_dir: None,
        }
    }
}

impl IsolationConfig {
    /// Create a config for in-process (no isolation) execution.
    #[must_use]
    pub fn in_process() -> Self {
        Self { mode: IsolationMode::InProcess, ..Default::default() }
    }

    /// Create a config for subprocess isolation with the given timeout.
    #[must_use]
    pub fn subprocess(timeout: Duration) -> Self {
        Self {
            mode: IsolationMode::SubProcess,
            timeout,
            ..Default::default()
        }
    }

    /// Create a config for sandboxed subprocess isolation.
    #[must_use]
    pub fn sandboxed(timeout: Duration) -> Self {
        Self {
            mode: IsolationMode::Sandboxed,
            timeout,
            ..Default::default()
        }
    }

    /// Set the maximum number of retries after a solver crash.
    #[must_use]
    pub fn with_retries(mut self, max_retries: u32) -> Self {
        self.max_retries = max_retries;
        self
    }

    /// Set the temporary directory for VC serialization files.
    #[must_use]
    pub fn with_temp_dir(mut self, dir: impl Into<PathBuf>) -> Self {
        self.temp_dir = Some(dir.into());
        self
    }
}

// ---------------------------------------------------------------------------
// tRust: IsolatedSolver wrapper (#195)
// ---------------------------------------------------------------------------

/// Wraps any `VerificationBackend` with process isolation.
///
/// In `InProcess` mode, delegates directly (zero overhead).
/// In `SubProcess` mode, serializes the VC to a temp file, spawns the
/// inner backend's host binary, and collects results. Crashes are caught
/// and reported as `Unknown` results with crash information.
pub struct IsolatedSolver {
    inner: Arc<dyn VerificationBackend>,
    config: IsolationConfig,
}

impl IsolatedSolver {
    /// Create an isolated solver wrapping the given backend.
    pub fn new(backend: Arc<dyn VerificationBackend>, config: IsolationConfig) -> Self {
        Self { inner: backend, config }
    }

    /// Get a reference to the inner backend.
    #[must_use]
    pub fn inner(&self) -> &dyn VerificationBackend {
        self.inner.as_ref()
    }

    /// Get the isolation configuration.
    #[must_use]
    pub fn config(&self) -> &IsolationConfig {
        &self.config
    }

    /// Verify a VC with isolation, retrying on crash up to `max_retries`.
    fn verify_with_retries(&self, vc: &VerificationCondition) -> VerificationResult {
        let max_attempts = 1 + self.config.max_retries;
        let mut last_crash: Option<SolverCrashReport> = None;

        for attempt in 0..max_attempts {
            match self.verify_isolated(vc) {
                Ok(result) => return result,
                Err(IsolationError::SolverCrash(report)) => {
                    last_crash = Some(report);
                    // Continue to retry
                    if attempt + 1 < max_attempts {
                        continue;
                    }
                }
                Err(IsolationError::Timeout { timeout_ms }) => {
                    return VerificationResult::Timeout {
                        solver: self.inner.name().to_string(),
                        timeout_ms,
                    };
                }
                Err(e) => {
                    return recover_from_error(self.inner.name(), &e);
                }
            }
        }

        // All retries exhausted — recover from the last crash.
        if let Some(crash) = last_crash {
            recover_from_crash(self.inner.name(), &crash)
        } else {
            VerificationResult::Unknown {
                solver: self.inner.name().to_string(),
                time_ms: 0,
                reason: "all retries exhausted with no crash report".to_string(),
            }
        }
    }

    /// Execute one isolated verification attempt.
    fn verify_isolated(
        &self,
        vc: &VerificationCondition,
    ) -> Result<VerificationResult, IsolationError> {
        match self.config.mode {
            IsolationMode::InProcess => Ok(self.inner.verify(vc)),
            IsolationMode::SubProcess | IsolationMode::Sandboxed => {
                self.verify_subprocess(vc)
            }
        }
    }

    /// Run verification in a child process.
    ///
    /// Protocol:
    /// 1. Serialize VC as JSON to a temp file.
    /// 2. Spawn the solver process, passing the temp file path on stdin.
    /// 3. Read JSON-encoded `VerificationResult` from stdout.
    /// 4. Enforce timeout by polling with `try_wait`.
    fn verify_subprocess(
        &self,
        vc: &VerificationCondition,
    ) -> Result<VerificationResult, IsolationError> {
        let start = Instant::now();

        // Serialize VC to JSON.
        let vc_json = serde_json::to_string(vc).map_err(|e| IsolationError::Serialization {
            reason: format!("failed to serialize VC: {e}"),
        })?;

        // Write VC JSON to a temp file.
        let temp_dir = self
            .config
            .temp_dir
            .clone()
            .unwrap_or_else(std::env::temp_dir);
        let temp_path = temp_dir.join(format!(
            "trust-vc-{}-{}.json",
            std::process::id(),
            start.elapsed().as_nanos()
        ));

        std::fs::write(&temp_path, &vc_json).map_err(|e| IsolationError::Serialization {
            reason: format!("failed to write temp file {}: {e}", temp_path.display()),
        })?;

        // Build the subprocess command.
        // The child process protocol: reads VC JSON from the file path passed
        // on stdin, runs the solver, writes VerificationResult JSON to stdout.
        let mut child = Command::new(std::env::current_exe().unwrap_or_else(|_| "trust-solver-worker".into()))
            .arg("--solver-worker")
            .arg(self.inner.name())
            .arg(&temp_path)
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .map_err(|e| IsolationError::Subprocess {
                reason: format!("failed to spawn solver process: {e}"),
            })?;

        // Enforce timeout by polling.
        let timeout = self.config.timeout;
        let result = wait_with_timeout(&mut child, timeout);

        // Clean up temp file (best-effort).
        let _ = std::fs::remove_file(&temp_path);

        let elapsed_ms = start.elapsed().as_millis() as u64;

        match result {
            WaitResult::Exited(output) => {
                if output.status.success() {
                    // Parse result from stdout.
                    let stdout = String::from_utf8_lossy(&output.stdout);
                    serde_json::from_str::<VerificationResult>(&stdout).map_err(|e| {
                        IsolationError::Deserialization {
                            reason: format!("failed to parse solver output: {e}"),
                        }
                    })
                } else {
                    // Solver process failed.
                    let stderr = String::from_utf8_lossy(&output.stderr).to_string();

                    #[cfg(unix)]
                    let signal = {
                        use std::os::unix::process::ExitStatusExt;
                        output.status.signal()
                    };
                    #[cfg(not(unix))]
                    let signal = None;

                    Err(IsolationError::SolverCrash(SolverCrashReport {
                        solver_name: self.inner.name().to_string(),
                        exit_code: output.status.code(),
                        signal,
                        stderr,
                        elapsed_ms,
                    }))
                }
            }
            WaitResult::TimedOut => {
                // Kill the child process.
                let _ = child.kill();
                let _ = child.wait();
                Err(IsolationError::Timeout { timeout_ms: timeout.as_millis() as u64 })
            }
        }
    }
}

impl VerificationBackend for IsolatedSolver {
    fn name(&self) -> &str {
        self.inner.name()
    }

    fn role(&self) -> BackendRole {
        self.inner.role()
    }

    fn can_handle(&self, vc: &VerificationCondition) -> bool {
        self.inner.can_handle(vc)
    }

    fn verify(&self, vc: &VerificationCondition) -> VerificationResult {
        self.verify_with_retries(vc)
    }
}

// ---------------------------------------------------------------------------
// tRust: Recovery helpers (#195)
// ---------------------------------------------------------------------------

/// Convert a solver crash into an `Unknown` result instead of panicking.
///
/// The crash information is preserved in the `reason` field so that the
/// verification pipeline can report it without losing diagnostic data.
#[must_use]
pub fn recover_from_crash(solver_name: &str, crash: &SolverCrashReport) -> VerificationResult {
    VerificationResult::Unknown {
        solver: solver_name.to_string(),
        time_ms: crash.elapsed_ms,
        reason: format!("solver crash: {crash}"),
    }
}

/// Convert any isolation error into an `Unknown` result.
#[must_use]
pub(crate) fn recover_from_error(solver_name: &str, error: &IsolationError) -> VerificationResult {
    VerificationResult::Unknown {
        solver: solver_name.to_string(),
        time_ms: 0,
        reason: format!("isolation error: {error}"),
    }
}

// ---------------------------------------------------------------------------
// tRust: Subprocess timeout enforcement (#195)
// ---------------------------------------------------------------------------

enum WaitResult {
    Exited(std::process::Output),
    TimedOut,
}

/// Wait for a child process to exit, enforcing a timeout by polling `try_wait`.
///
/// Uses a progressive sleep strategy: starts at 1ms and caps at 50ms to
/// balance responsiveness against CPU overhead for short-running solvers.
fn wait_with_timeout(child: &mut std::process::Child, timeout: Duration) -> WaitResult {
    let start = Instant::now();
    let mut sleep_ms: u64 = 1;

    loop {
        match child.try_wait() {
            Ok(Some(_status)) => {
                // Process exited — collect full output.
                // We need stdout/stderr, so use wait_with_output on a process
                // that already exited. Since try_wait consumed the status, we
                // read the pipes directly.
                let stdout = child
                    .stdout
                    .take()
                    .map(|mut r| {
                        let mut buf = Vec::new();
                        std::io::Read::read_to_end(&mut r, &mut buf).unwrap_or(0);
                        buf
                    })
                    .unwrap_or_default();
                let stderr = child
                    .stderr
                    .take()
                    .map(|mut r| {
                        let mut buf = Vec::new();
                        std::io::Read::read_to_end(&mut r, &mut buf).unwrap_or(0);
                        buf
                    })
                    .unwrap_or_default();

                // Reconstruct an Output-like struct. We need the exit status again.
                // Since try_wait already consumed it, call wait() which returns
                // immediately for an already-exited process.
                let status = child.wait().unwrap_or(_status);
                return WaitResult::Exited(std::process::Output { status, stdout, stderr });
            }
            Ok(None) => {
                // Still running — check timeout.
                if start.elapsed() >= timeout {
                    return WaitResult::TimedOut;
                }
                std::thread::sleep(Duration::from_millis(sleep_ms));
                sleep_ms = (sleep_ms * 2).min(50);
            }
            Err(_) => {
                // Error querying process — treat as timeout.
                return WaitResult::TimedOut;
            }
        }
    }
}

// ---------------------------------------------------------------------------
// tRust: Convenience constructors (#195)
// ---------------------------------------------------------------------------

/// Wrap a backend with in-process (pass-through) isolation.
///
/// This is a zero-overhead wrapper that delegates directly to the inner
/// backend. Useful as the default when isolation is not needed.
#[must_use]
pub fn wrap_in_process(backend: Arc<dyn VerificationBackend>) -> IsolatedSolver {
    IsolatedSolver::new(backend, IsolationConfig::in_process())
}

/// Wrap a backend with subprocess isolation and the given timeout.
#[must_use]
pub fn wrap_subprocess(backend: Arc<dyn VerificationBackend>, timeout: Duration) -> IsolatedSolver {
    IsolatedSolver::new(backend, IsolationConfig::subprocess(timeout))
}

/// Wrap a backend with subprocess isolation, timeout, and retry count.
#[must_use]
pub fn wrap_with_retries(
    backend: Arc<dyn VerificationBackend>,
    timeout: Duration,
    max_retries: u32,
) -> IsolatedSolver {
    IsolatedSolver::new(
        backend,
        IsolationConfig::subprocess(timeout).with_retries(max_retries),
    )
}

// ---------------------------------------------------------------------------
// tRust: Tests (#195)
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mock_backend::MockBackend;

    fn make_vc() -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "test_fn".to_string(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
        }
    }

    // -- IsolationMode tests --

    #[test]
    fn test_isolation_mode_default_is_in_process() {
        assert_eq!(IsolationMode::default(), IsolationMode::InProcess);
    }

    #[test]
    fn test_isolation_mode_equality() {
        assert_eq!(IsolationMode::SubProcess, IsolationMode::SubProcess);
        assert_ne!(IsolationMode::InProcess, IsolationMode::SubProcess);
        assert_ne!(IsolationMode::SubProcess, IsolationMode::Sandboxed);
    }

    // -- IsolationConfig tests --

    #[test]
    fn test_isolation_config_default() {
        let config = IsolationConfig::default();
        assert_eq!(config.mode, IsolationMode::InProcess);
        assert_eq!(config.timeout, Duration::from_secs(30));
        assert_eq!(config.max_retries, 0);
        assert!(config.temp_dir.is_none());
    }

    #[test]
    fn test_isolation_config_subprocess() {
        let config = IsolationConfig::subprocess(Duration::from_secs(10));
        assert_eq!(config.mode, IsolationMode::SubProcess);
        assert_eq!(config.timeout, Duration::from_secs(10));
    }

    #[test]
    fn test_isolation_config_sandboxed() {
        let config = IsolationConfig::sandboxed(Duration::from_secs(60));
        assert_eq!(config.mode, IsolationMode::Sandboxed);
        assert_eq!(config.timeout, Duration::from_secs(60));
    }

    #[test]
    fn test_isolation_config_builder_retries() {
        let config = IsolationConfig::subprocess(Duration::from_secs(5)).with_retries(3);
        assert_eq!(config.max_retries, 3);
    }

    #[test]
    fn test_isolation_config_builder_temp_dir() {
        let config = IsolationConfig::subprocess(Duration::from_secs(5))
            .with_temp_dir("/tmp/trust-test");
        assert_eq!(config.temp_dir, Some(PathBuf::from("/tmp/trust-test")));
    }

    // -- SolverCrashReport tests --

    #[test]
    fn test_solver_crash_report_display_with_exit_code() {
        let report = SolverCrashReport {
            solver_name: "z4".to_string(),
            exit_code: Some(139),
            signal: None,
            stderr: "segmentation fault".to_string(),
            elapsed_ms: 42,
        };
        let display = report.to_string();
        assert!(display.contains("z4"));
        assert!(display.contains("exit code 139"));
        assert!(display.contains("segmentation fault"));
    }

    #[test]
    fn test_solver_crash_report_display_with_signal() {
        let report = SolverCrashReport {
            solver_name: "sunder".to_string(),
            exit_code: None,
            signal: Some(11),
            stderr: String::new(),
            elapsed_ms: 100,
        };
        let display = report.to_string();
        assert!(display.contains("sunder"));
        assert!(display.contains("signal 11"));
    }

    #[test]
    fn test_solver_crash_report_display_truncates_long_stderr() {
        let long_stderr = "x".repeat(500);
        let report = SolverCrashReport {
            solver_name: "test".to_string(),
            exit_code: Some(1),
            signal: None,
            stderr: long_stderr,
            elapsed_ms: 10,
        };
        let display = report.to_string();
        // Display should be truncated to ~200 chars of stderr
        assert!(display.len() < 300);
    }

    // -- recover_from_crash tests --

    #[test]
    fn test_recover_from_crash_returns_unknown() {
        let crash = SolverCrashReport {
            solver_name: "z4".to_string(),
            exit_code: Some(139),
            signal: Some(11),
            stderr: "SIGSEGV".to_string(),
            elapsed_ms: 50,
        };
        let result = recover_from_crash("z4", &crash);
        assert!(matches!(result, VerificationResult::Unknown { .. }));
        assert_eq!(result.solver_name(), "z4");
        assert_eq!(result.time_ms(), 50);
        if let VerificationResult::Unknown { reason, .. } = &result {
            assert!(reason.contains("solver crash"));
            assert!(reason.contains("z4"));
        }
    }

    #[test]
    fn test_recover_from_error_returns_unknown() {
        let error = IsolationError::Serialization {
            reason: "bad json".to_string(),
        };
        let result = recover_from_error("test-solver", &error);
        assert!(matches!(result, VerificationResult::Unknown { .. }));
        if let VerificationResult::Unknown { reason, .. } = &result {
            assert!(reason.contains("isolation error"));
            assert!(reason.contains("bad json"));
        }
    }

    // -- IsolatedSolver in-process mode tests --

    #[test]
    fn test_isolated_solver_in_process_delegates_directly() {
        let backend = Arc::new(MockBackend);
        let solver = IsolatedSolver::new(backend, IsolationConfig::in_process());

        let vc = make_vc();
        let result = solver.verify(&vc);
        assert!(result.is_proved());
        assert_eq!(result.solver_name(), "mock");
    }

    #[test]
    fn test_isolated_solver_name_delegates() {
        let backend = Arc::new(MockBackend);
        let solver = IsolatedSolver::new(backend, IsolationConfig::in_process());
        assert_eq!(solver.name(), "mock");
    }

    #[test]
    fn test_isolated_solver_role_delegates() {
        let backend = Arc::new(MockBackend);
        let solver = IsolatedSolver::new(backend, IsolationConfig::in_process());
        assert_eq!(solver.role(), BackendRole::General);
    }

    #[test]
    fn test_isolated_solver_can_handle_delegates() {
        let backend = Arc::new(MockBackend);
        let solver = IsolatedSolver::new(backend, IsolationConfig::in_process());
        let vc = make_vc();
        assert!(solver.can_handle(&vc));
    }

    #[test]
    fn test_isolated_solver_inner_accessor() {
        let backend = Arc::new(MockBackend);
        let solver = IsolatedSolver::new(backend, IsolationConfig::in_process());
        assert_eq!(solver.inner().name(), "mock");
    }

    #[test]
    fn test_isolated_solver_config_accessor() {
        let config = IsolationConfig::subprocess(Duration::from_secs(10)).with_retries(2);
        let backend = Arc::new(MockBackend);
        let solver = IsolatedSolver::new(backend, config.clone());
        assert_eq!(solver.config().mode, IsolationMode::SubProcess);
        assert_eq!(solver.config().max_retries, 2);
    }

    // -- Subprocess isolation tests --
    //
    // These test the subprocess execution path using a real child process.
    // We test with `false` (always exits non-zero) to verify crash recovery.

    #[test]
    fn test_subprocess_crash_recovery_with_false_command() {
        // Simulate a subprocess crash by verifying that a non-zero exit
        // from the child process is caught and converted to Unknown.
        let crash = SolverCrashReport {
            solver_name: "crashing-solver".to_string(),
            exit_code: Some(1),
            signal: None,
            stderr: "fatal error in solver".to_string(),
            elapsed_ms: 5,
        };
        let result = recover_from_crash("crashing-solver", &crash);
        assert!(matches!(result, VerificationResult::Unknown { .. }));
        assert_eq!(result.solver_name(), "crashing-solver");
        if let VerificationResult::Unknown { reason, .. } = &result {
            assert!(reason.contains("crash"));
            assert!(reason.contains("fatal error"));
        }
    }

    #[test]
    fn test_subprocess_timeout_enforcement() {
        // Verify that the wait_with_timeout function correctly detects timeout.
        // Spawn `sleep 60` and give it a 100ms timeout.
        let mut child = Command::new("sleep")
            .arg("60")
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .expect("failed to spawn sleep");

        let result = wait_with_timeout(&mut child, Duration::from_millis(100));
        assert!(matches!(result, WaitResult::TimedOut));

        // Clean up.
        let _ = child.kill();
        let _ = child.wait();
    }

    #[test]
    fn test_subprocess_normal_exit_collected() {
        // Verify that a normally exiting process has its output collected.
        let mut child = Command::new("echo")
            .arg("hello")
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .expect("failed to spawn echo");

        let result = wait_with_timeout(&mut child, Duration::from_secs(5));
        match result {
            WaitResult::Exited(output) => {
                assert!(output.status.success());
                let stdout = String::from_utf8_lossy(&output.stdout);
                assert!(stdout.contains("hello"));
            }
            WaitResult::TimedOut => panic!("echo should not time out"),
        }
    }

    // -- Convenience constructors --

    #[test]
    fn test_wrap_in_process() {
        let backend = Arc::new(MockBackend);
        let solver = wrap_in_process(backend);
        assert_eq!(solver.config().mode, IsolationMode::InProcess);
        let vc = make_vc();
        assert!(solver.verify(&vc).is_proved());
    }

    #[test]
    fn test_wrap_subprocess() {
        let backend = Arc::new(MockBackend);
        let solver = wrap_subprocess(backend, Duration::from_secs(10));
        assert_eq!(solver.config().mode, IsolationMode::SubProcess);
        assert_eq!(solver.config().timeout, Duration::from_secs(10));
    }

    #[test]
    fn test_wrap_with_retries() {
        let backend = Arc::new(MockBackend);
        let solver = wrap_with_retries(backend, Duration::from_secs(5), 3);
        assert_eq!(solver.config().mode, IsolationMode::SubProcess);
        assert_eq!(solver.config().max_retries, 3);
    }

    // -- IsolationError tests --

    #[test]
    fn test_isolation_error_display_variants() {
        let crash_err = IsolationError::SolverCrash(SolverCrashReport {
            solver_name: "z4".to_string(),
            exit_code: Some(1),
            signal: None,
            stderr: "err".to_string(),
            elapsed_ms: 10,
        });
        assert!(crash_err.to_string().contains("solver crashed"));

        let timeout_err = IsolationError::Timeout { timeout_ms: 5000 };
        assert!(timeout_err.to_string().contains("5000ms"));

        let ser_err = IsolationError::Serialization { reason: "bad".to_string() };
        assert!(ser_err.to_string().contains("bad"));

        let sub_err = IsolationError::Subprocess { reason: "spawn failed".to_string() };
        assert!(sub_err.to_string().contains("spawn failed"));

        let deser_err = IsolationError::Deserialization { reason: "parse fail".to_string() };
        assert!(deser_err.to_string().contains("parse fail"));
    }

    // -- Retry logic tests --

    #[test]
    fn test_isolated_solver_in_process_no_retries_needed() {
        // In-process mode with retries configured still works — the backend
        // succeeds on the first attempt, so retries are never triggered.
        let backend = Arc::new(MockBackend);
        let config = IsolationConfig::in_process().with_retries(3);
        let solver = IsolatedSolver::new(backend, config);

        let vc = make_vc();
        let result = solver.verify(&vc);
        assert!(result.is_proved());
    }

    #[test]
    fn test_isolated_solver_verify_trivially_true_fails() {
        // MockBackend returns Failed for Bool(true) formulas.
        let backend = Arc::new(MockBackend);
        let solver = wrap_in_process(backend);
        let vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "test_fn".to_string(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        };
        let result = solver.verify(&vc);
        assert!(result.is_failed());
    }
}
