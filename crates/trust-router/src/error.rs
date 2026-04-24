// trust-router/error.rs: Unified error types for the trust-router crate
//
// tRust #461: Replace string-typed errors with proper thiserror-derived enums.
// tRust #703: Unify per-module error types into a single RouterError enum.
//
// Module-local error types (ReplayError, etc.) remain in their respective
// modules for internal use. RouterError provides #[from] conversions so
// callers can use a single Result<T, RouterError> at the crate boundary.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use thiserror::Error;

use crate::fallback::FallbackError;
use crate::memory_guard::MemoryGuardError;
use crate::replay::ReplayError;

// ---------------------------------------------------------------------------
// tRust #970: ExecutionError moved here from solver_execution.rs (deleted)
// ---------------------------------------------------------------------------

/// Errors from solver execution operations.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum ExecutionError {
    /// The worker pool has been shut down.
    #[error("worker pool is shut down")]
    PoolShutdown,

    /// No workers available within the timeout.
    #[error("no worker available within {timeout_ms}ms")]
    WorkerUnavailable { timeout_ms: u64 },

    /// The solver execution timed out.
    #[error("solver execution timed out after {timeout_ms}ms")]
    Timeout { timeout_ms: u64 },

    /// The solver crashed during execution.
    #[error("solver crashed: {reason}")]
    SolverCrash { reason: String },

    /// Resource limit exceeded (memory, CPU).
    #[error("resource limit exceeded: {detail}")]
    ResourceLimitExceeded { detail: String },

    /// Internal error in the execution infrastructure.
    #[error("internal execution error: {reason}")]
    Internal { reason: String },
}

// ---------------------------------------------------------------------------
// tRust #970: IsolationError moved here from isolation.rs (deleted)
// ---------------------------------------------------------------------------

/// Errors that can occur during isolated solver execution.
#[derive(Debug, Error)]
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
            let truncated =
                if self.stderr.len() > 200 { &self.stderr[..200] } else { &self.stderr };
            write!(f, ": {truncated}")?;
        }
        Ok(())
    }
}

/// tRust #703: Unified error type for the trust-router crate.
///
/// Wraps all module-local error types via `#[from]` so that public API
/// functions can return `Result<T, RouterError>` instead of requiring callers
/// to know which module's error type a given function uses.
///
/// Module-local types remain available for callers who need fine-grained
/// matching (e.g., `ExecutionError::PoolShutdown`).
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum RouterError {
    /// Counterexample replay error (symex failure, block out of range).
    #[error("replay: {0}")]
    Replay(#[from] ReplayError),

    /// Solver execution error (pool shutdown, worker unavailable, crash).
    #[error("execution: {0}")]
    Execution(#[from] ExecutionError),

    /// Process isolation error (subprocess crash, timeout, serialization).
    #[error("isolation: {0}")]
    Isolation(#[from] IsolationError),

    /// Fallback chain error (all solvers failed, empty chain).
    #[error("fallback: {0}")]
    Fallback(#[from] FallbackError),

    /// Solver subprocess invocation error (binary not found, spawn failure).
    #[error("solver process: {0}")]
    SolverProcess(#[from] SolverProcessError),

    /// z4 encoding error (API failure, unsupported formula).
    #[error("z4 encode: {0}")]
    Z4Encode(#[from] Z4EncodeError),

    /// tRust #882: Memory guard error (limit exceeded, query failed).
    #[error("memory guard: {0}")]
    MemoryGuard(#[from] MemoryGuardError),
}

/// tRust: Error type for solver subprocess invocation (smtlib, zani, certus,
/// sunder, lean5 backends).
///
/// Each variant captures the structured cause rather than a format!() string.
/// The solver name is included in every variant so callers can attribute errors
/// without carrying additional context.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum SolverProcessError {
    /// The solver binary was not found on disk or PATH.
    #[error("{solver} binary not found: {hint}")]
    BinaryNotFound { solver: &'static str, hint: String },

    /// Failed to spawn the solver subprocess.
    #[error("failed to spawn {solver} at {path}: {source}")]
    SpawnFailed { solver: &'static str, path: String, source: std::io::Error },

    /// Failed to write to the solver's stdin.
    #[error("failed to write to {solver} stdin: {source}")]
    StdinWriteFailed { solver: &'static str, source: std::io::Error },

    /// Failed to read the solver's output (stdout/stderr).
    #[error("failed to read {solver} output: {source}")]
    OutputReadFailed { solver: &'static str, source: std::io::Error },

    /// The solver wrote diagnostic output to stderr, indicating an error.
    #[error("{solver} stderr: {stderr}")]
    SolverStderr { solver: &'static str, stderr: String },

    /// The solver process crashed (closed stdout unexpectedly).
    #[error("{solver} process crashed: {detail}")]
    ProcessCrashed { solver: &'static str, detail: String },

    /// The solver timed out waiting for a response.
    #[error("{solver} timeout: {detail}")]
    Timeout { solver: &'static str, detail: String },

    /// The solver reader thread disconnected (thread panicked or was killed).
    #[error("{solver} disconnected: {detail}")]
    Disconnected { solver: &'static str, detail: String },

    /// The solver's model output exceeded the size limit.
    #[error("{solver} model output too large: {bytes} bytes exceeds {limit} byte limit")]
    ModelOutputTooLarge { solver: &'static str, bytes: usize, limit: usize },
}

/// tRust: Error type for encoding `Formula` into z4 native terms.
///
/// Separates z4 API failures (which carry the z4 error) from unsupported
/// formula variants (which carry the debug representation).
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum Z4EncodeError {
    /// A z4 API call failed during term construction.
    #[error("{operation}: {message}")]
    Z4Api { operation: &'static str, message: String },

    /// The formula variant is not yet supported by the z4 backend encoder.
    #[error("unsupported formula variant: {description}")]
    UnsupportedFormula { description: String },
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_router_error_from_execution() {
        let exec_err = ExecutionError::PoolShutdown;
        let router_err: RouterError = exec_err.into();
        assert!(matches!(router_err, RouterError::Execution(ExecutionError::PoolShutdown)));
        let msg = router_err.to_string();
        assert!(msg.contains("execution"), "error message should contain 'execution': {msg}");
    }

    #[test]
    fn test_router_error_from_fallback() {
        let fb_err = FallbackError::EmptyChain;
        let router_err: RouterError = fb_err.into();
        assert!(matches!(router_err, RouterError::Fallback(FallbackError::EmptyChain)));
        let msg = router_err.to_string();
        assert!(msg.contains("fallback"), "error message should contain 'fallback': {msg}");
    }

    #[test]
    fn test_router_error_from_isolation() {
        let iso_err = IsolationError::Timeout { timeout_ms: 5000 };
        let router_err: RouterError = iso_err.into();
        assert!(matches!(
            router_err,
            RouterError::Isolation(IsolationError::Timeout { timeout_ms: 5000 })
        ));
    }

    #[test]
    fn test_router_error_from_replay() {
        let replay_err = ReplayError::NoBlocks;
        let router_err: RouterError = replay_err.into();
        assert!(matches!(router_err, RouterError::Replay(ReplayError::NoBlocks)));
    }

    #[test]
    fn test_router_error_from_solver_process() {
        let sp_err =
            SolverProcessError::BinaryNotFound { solver: "z3", hint: "not in PATH".to_string() };
        let router_err: RouterError = sp_err.into();
        assert!(matches!(
            router_err,
            RouterError::SolverProcess(SolverProcessError::BinaryNotFound { .. })
        ));
    }

    #[test]
    fn test_router_error_from_z4_encode() {
        let z4_err = Z4EncodeError::UnsupportedFormula { description: "BitVec".to_string() };
        let router_err: RouterError = z4_err.into();
        assert!(matches!(
            router_err,
            RouterError::Z4Encode(Z4EncodeError::UnsupportedFormula { .. })
        ));
    }

    #[test]
    fn test_router_error_is_non_exhaustive() {
        // Verify RouterError can be matched with a wildcard (non_exhaustive).
        let err: RouterError = ExecutionError::PoolShutdown.into();
        match err {
            RouterError::Execution(_) => {}
            _ => panic!("expected Execution variant"),
        }
    }
}
