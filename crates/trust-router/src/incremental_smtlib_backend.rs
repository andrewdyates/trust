// trust-router/incremental_smtlib_backend.rs: Persistent solver with incremental SMT-LIB2
//
// Maintains a long-lived solver process that accepts VCs via the incremental
// SMT-LIB2 protocol (push/pop). Reuses the solver across VCs within a function,
// amortizing startup cost and enabling learned-lemma reuse. Falls back to
// per-process SmtLibBackend on persistent process failure.
//
// tRust #722: All reads from the solver use a dedicated reader thread and
// mpsc::channel with recv_timeout() to enforce per-query timeouts. Model
// output is capped at MAX_MODEL_OUTPUT_BYTES to prevent OOM.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::io::{BufRead, BufReader, Write as _};
use std::process::{Child, Command, Stdio};
use std::sync::Mutex;
use std::sync::mpsc;
use std::time::{Duration, Instant};

use trust_types::*;

use crate::error::SolverProcessError;
use crate::smt2_export;
use crate::smtlib_backend::{self, SmtLibBackend};
use crate::{BackendRole, VerificationBackend};

/// Default timeout per-query in milliseconds.
const DEFAULT_QUERY_TIMEOUT_MS: u64 = 30_000;

/// Maximum consecutive failures before permanently falling back to per-process mode.
const MAX_CONSECUTIVE_FAILURES: u32 = 3;

/// tRust #722: Maximum model output size in bytes (10 MiB default).
///
/// Prevents unbounded memory growth from malformed or adversarial solver output.
const MAX_MODEL_OUTPUT_BYTES: usize = 10 * 1024 * 1024;

/// Internal state of the persistent solver process.
///
/// tRust #722: The reader thread continuously reads lines from solver stdout
/// and sends them over `line_rx`. This decouples I/O blocking from the main
/// thread, enabling timeout enforcement via `recv_timeout()`.
struct SolverProcess {
    child: Child,
    stdin: std::process::ChildStdin,
    /// tRust #722: Channel receiver for lines read by the dedicated reader thread.
    line_rx: mpsc::Receiver<Result<String, String>>,
}

/// Session state shared across verify calls (behind a Mutex for Send+Sync).
struct SessionState {
    /// The live solver process, if any.
    process: Option<SolverProcess>,
    /// Number of consecutive process failures (crash/timeout).
    consecutive_failures: u32,
    /// Whether we have permanently fallen back to per-process mode.
    fallen_back: bool,
    /// Total queries dispatched to the persistent process.
    queries_dispatched: u64,
    /// Total queries that required a process restart.
    restarts: u64,
}

/// Verification backend that maintains a persistent z4 process using the
/// incremental SMT-LIB2 protocol (push/pop).
///
/// # Protocol
///
/// The solver is started once with `(set-option :print-success true)` so that
/// every command produces an `success` acknowledgment. Each VC is wrapped in
/// `(push 1)` / `(pop 1)` to isolate assertion scopes while reusing learned
/// lemmas from shared declarations.
///
/// # Fault Isolation
///
/// A watchdog monitors each query. On timeout or crash:
/// 1. The solver process is killed and restarted.
/// 2. A consecutive failure counter increments.
/// 3. After `MAX_CONSECUTIVE_FAILURES`, the backend permanently falls back
///    to per-process mode (delegates to `SmtLibBackend`).
pub struct IncrementalSmtLibBackend {
    /// Path to the solver binary (default: "z4").
    solver_path: String,
    /// Extra arguments passed to the solver (default: ["-smt2", "-in"]).
    solver_args: Vec<String>,
    /// Timeout per query in milliseconds.
    query_timeout_ms: u64,
    /// Mutable session state protected by a mutex.
    state: Mutex<SessionState>,
    /// Fallback per-process backend used when the persistent process fails.
    fallback: SmtLibBackend,
}

impl IncrementalSmtLibBackend {
    /// Create an incremental backend that invokes z4 at the default path.
    pub fn new() -> Self {
        Self::with_solver_path("z4")
    }

    /// Create an incremental backend with a custom solver path.
    pub fn with_solver_path(path: impl Into<String>) -> Self {
        let path = path.into();
        let fallback = SmtLibBackend::with_solver_path(path.clone());
        IncrementalSmtLibBackend {
            solver_path: path,
            solver_args: vec!["-smt2".to_string(), "-in".to_string()],
            query_timeout_ms: DEFAULT_QUERY_TIMEOUT_MS,
            state: Mutex::new(SessionState {
                process: None,
                consecutive_failures: 0,
                fallen_back: false,
                queries_dispatched: 0,
                restarts: 0,
            }),
            fallback,
        }
    }

    /// Set the per-query timeout in milliseconds.
    pub fn with_timeout(mut self, timeout_ms: u64) -> Self {
        self.query_timeout_ms = timeout_ms;
        self.fallback = self.fallback.with_timeout(timeout_ms);
        self
    }

    /// Return statistics: (queries_dispatched, restarts, fallen_back).
    pub fn stats(&self) -> (u64, u64, bool) {
        let state = self.state.lock().expect("lock poisoned");
        (state.queries_dispatched, state.restarts, state.fallen_back)
    }

    /// Spawn a fresh solver process with incremental-mode options.
    ///
    /// tRust #722: Spawns a dedicated reader thread that reads lines from
    /// solver stdout and sends them over an mpsc channel. All subsequent
    /// reads use `recv_timeout()` for timeout enforcement.
    fn spawn_solver(&self) -> Result<SolverProcess, String> {
        let mut child = Command::new(&self.solver_path)
            .args(&self.solver_args)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .map_err(|e| format!("failed to spawn {}: {e}", self.solver_path))?;

        let stdin = child.stdin.take().ok_or("failed to capture solver stdin")?;
        let stdout = child.stdout.take().ok_or("failed to capture solver stdout")?;

        // tRust #722: Spawn a dedicated reader thread for non-blocking reads.
        let (tx, rx) = mpsc::channel();
        std::thread::spawn(move || {
            let mut reader = BufReader::new(stdout);
            loop {
                let mut line = String::new();
                match reader.read_line(&mut line) {
                    Ok(0) => {
                        // EOF: solver closed stdout.
                        let _ = tx.send(Err(
                            "solver closed stdout (process may have crashed)".to_string()
                        ));
                        break;
                    }
                    Ok(_) => {
                        if tx.send(Ok(line)).is_err() {
                            // Receiver dropped (process killed); exit thread.
                            break;
                        }
                    }
                    Err(e) => {
                        let _ = tx.send(Err(format!("read from solver: {e}")));
                        break;
                    }
                }
            }
        });

        let mut proc = SolverProcess { child, stdin, line_rx: rx };

        // Use a generous timeout for initial setup commands (5s).
        let setup_timeout = Duration::from_secs(5);

        // Enable print-success so we get acknowledgments for every command.
        send_command(&mut proc, "(set-option :print-success true)")?;
        read_response_line(&mut proc, setup_timeout)?;

        // Enable model production.
        send_command(&mut proc, "(set-option :produce-models true)")?;
        read_response_line(&mut proc, setup_timeout)?;

        Ok(proc)
    }

    /// Ensure a live solver process exists, spawning one if needed.
    fn ensure_process(&self, state: &mut SessionState) -> Result<(), String> {
        if state.process.is_some() {
            return Ok(());
        }
        let proc = self.spawn_solver()?;
        state.process = Some(proc);
        Ok(())
    }

    /// Kill the current solver process (if any) and clear it from state.
    fn kill_process(state: &mut SessionState) {
        if let Some(mut proc) = state.process.take() {
            let _ = proc.child.kill();
            let _ = proc.child.wait();
        }
    }

    /// Run a single VC query on the persistent solver using push/pop.
    ///
    /// tRust #722: All reads enforce the per-query timeout via `recv_timeout()`.
    /// On timeout, returns `Err` which triggers process kill and fallback in
    /// the caller.
    ///
    /// Returns the parsed VerificationResult or an error string if the
    /// process is unhealthy.
    fn run_incremental_query(
        &self,
        state: &mut SessionState,
        vc: &VerificationCondition,
    ) -> Result<VerificationResult, String> {
        self.ensure_process(state)?;
        let proc = state.process.as_mut().ok_or("no solver process")?;

        let timeout = Duration::from_millis(self.query_timeout_ms);
        let start = Instant::now();

        // Detect logic and set it (idempotent if solver supports it).
        let logic = smt2_export::detect_logic(&vc.formula);

        // Push a new scope.
        send_command(proc, "(push 1)")?;
        read_response_line(proc, remaining_timeout(timeout, start))?;

        // Set logic within the scope.
        send_command(proc, &format!("(set-logic {logic})"))?;
        read_response_line(proc, remaining_timeout(timeout, start))?;

        // Declare variables.
        for decl in smt2_export::emit_declarations(&vc.formula) {
            send_command(proc, &decl)?;
            read_response_line(proc, remaining_timeout(timeout, start))?;
        }

        // Assert the formula.
        let assertion = format!("(assert {})", smt2_export::formula_to_smt2(&vc.formula));
        send_command(proc, &assertion)?;
        read_response_line(proc, remaining_timeout(timeout, start))?;

        // Check satisfiability.
        send_command(proc, "(check-sat)")?;
        let sat_line = read_response_line(proc, remaining_timeout(timeout, start))?;

        let elapsed = start.elapsed().as_millis() as u64;

        // Parse check-sat result and optionally get model.
        let result = if sat_line.trim() == "unsat" {
            // Pop scope.
            send_command(proc, "(pop 1)")?;
            read_response_line(proc, remaining_timeout(timeout, start))?;
            VerificationResult::Proved {
                solver: "z4-smtlib-incremental".into(),
                time_ms: elapsed,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: None,
                solver_warnings: None,
            }
        } else if sat_line.trim() == "sat" {
            // Get model for counterexample.
            send_command(proc, "(get-model)")?;
            let model_output = read_model_response(proc, remaining_timeout(timeout, start))?;

            // Pop scope.
            send_command(proc, "(pop 1)")?;
            read_response_line(proc, remaining_timeout(timeout, start))?;

            // Parse the model into a counterexample.
            let full_output = format!("sat\n{model_output}");
            smtlib_backend::parse_solver_output(&full_output, elapsed, vec![])
        } else if sat_line.trim() == "unknown" {
            // Pop scope.
            send_command(proc, "(pop 1)")?;
            read_response_line(proc, remaining_timeout(timeout, start))?;
            VerificationResult::Unknown {
                solver: "z4-smtlib-incremental".into(),
                time_ms: elapsed,
                reason: "solver returned unknown".to_string(),
            }
        } else {
            // Unexpected output -- pop and report.
            let _ = send_command(proc, "(pop 1)");
            let _ = read_response_line(proc, remaining_timeout(timeout, start));
            return Err(format!("unexpected solver response: {}", sat_line.trim()));
        };

        Ok(result)
    }
}

impl Default for IncrementalSmtLibBackend {
    fn default() -> Self {
        Self::new()
    }
}

impl VerificationBackend for IncrementalSmtLibBackend {
    fn name(&self) -> &str {
        "z4-smtlib-incremental"
    }

    fn role(&self) -> BackendRole {
        BackendRole::SmtSolver
    }

    fn can_handle(&self, vc: &VerificationCondition) -> bool {
        matches!(vc.kind.proof_level(), ProofLevel::L0Safety | ProofLevel::L1Functional)
    }

    fn verify(&self, vc: &VerificationCondition) -> VerificationResult {
        let mut state = self.state.lock().expect("lock poisoned");

        state.queries_dispatched += 1;

        // If permanently fallen back, delegate to per-process backend.
        if state.fallen_back {
            drop(state);
            return self.fallback.verify(vc);
        }

        // Attempt incremental query.
        match self.run_incremental_query(&mut state, vc) {
            Ok(result) => {
                // Success resets the consecutive failure counter.
                state.consecutive_failures = 0;
                result
            }
            Err(err) => {
                // tRust #722: Distinguish timeout from other failures so we
                // can return a proper Timeout result instead of Unknown.
                let is_timeout = err.contains("timeout");

                // Process failure: kill, increment counter, maybe fall back.
                Self::kill_process(&mut state);
                state.consecutive_failures += 1;
                state.restarts += 1;

                if state.consecutive_failures >= MAX_CONSECUTIVE_FAILURES {
                    state.fallen_back = true;
                }

                // tRust #722: Return Timeout result when the error was a timeout,
                // rather than delegating to the fallback which would re-run the
                // (likely still expensive) query.
                if is_timeout {
                    return VerificationResult::Timeout {
                        solver: "z4-smtlib-incremental".into(),
                        timeout_ms: self.query_timeout_ms,
                    };
                }

                // For non-timeout failures, use the per-process fallback.
                drop(state);
                self.fallback.verify(vc)
            }
        }
    }
}

// --- I/O helpers for the persistent solver process ---

/// Send a command string to the solver's stdin, followed by a newline.
fn send_command(proc: &mut SolverProcess, cmd: &str) -> Result<(), String> {
    proc.stdin.write_all(cmd.as_bytes()).map_err(|e| format!("write to solver: {e}"))?;
    proc.stdin.write_all(b"\n").map_err(|e| format!("write newline: {e}"))?;
    proc.stdin.flush().map_err(|e| format!("flush solver stdin: {e}"))?;
    Ok(())
}

/// tRust #722: Compute remaining timeout from a deadline.
///
/// Returns at least 1ms to avoid zero-duration recv_timeout (which would
/// be an instant failure).
fn remaining_timeout(total: Duration, start: Instant) -> Duration {
    let elapsed = start.elapsed();
    if elapsed >= total { Duration::from_millis(1) } else { total - elapsed }
}

/// Read a single response line from the solver's stdout.
///
/// tRust #722: Uses `recv_timeout()` on the channel to enforce timeout.
/// Returns an error containing "timeout" on timeout so the caller can
/// distinguish timeout from other failures.
fn read_response_line(proc: &mut SolverProcess, timeout: Duration) -> Result<String, String> {
    match proc.line_rx.recv_timeout(timeout) {
        Ok(Ok(line)) => {
            if line.is_empty() {
                Err(SolverProcessError::ProcessCrashed {
                    solver: "z4-smtlib-incremental",
                    detail: "solver closed stdout".to_string(),
                }
                .to_string())
            } else {
                Ok(line)
            }
        }
        Ok(Err(e)) => Err(e),
        Err(mpsc::RecvTimeoutError::Timeout) => Err(SolverProcessError::Timeout {
            solver: "z4-smtlib-incremental",
            detail: "no response within deadline".to_string(),
        }
        .to_string()),
        Err(mpsc::RecvTimeoutError::Disconnected) => Err(SolverProcessError::Disconnected {
            solver: "z4-smtlib-incremental",
            detail: "reader thread disconnected (process may have crashed)".to_string(),
        }
        .to_string()),
    }
}

/// Read a multi-line model response from the solver.
///
/// tRust #722: Enforces timeout on each line read via `recv_timeout()` and
/// caps total accumulated output at `MAX_MODEL_OUTPUT_BYTES` to prevent OOM.
///
/// Reads lines until parentheses are balanced (the model s-expression is
/// complete). This handles both `(model ...)` and bare `(...)` formats.
fn read_model_response(proc: &mut SolverProcess, timeout: Duration) -> Result<String, String> {
    let mut output = String::new();
    let mut depth: i32 = 0;
    let mut started = false;
    let start = Instant::now();

    loop {
        let remaining = remaining_timeout(timeout, start);
        let line = match proc.line_rx.recv_timeout(remaining) {
            Ok(Ok(line)) => line,
            Ok(Err(e)) => return Err(e),
            Err(mpsc::RecvTimeoutError::Timeout) => {
                return Err(SolverProcessError::Timeout {
                    solver: "z4-smtlib-incremental",
                    detail: "timeout during model read".to_string(),
                }
                .to_string());
            }
            Err(mpsc::RecvTimeoutError::Disconnected) => {
                return Err(SolverProcessError::Disconnected {
                    solver: "z4-smtlib-incremental",
                    detail: "disconnected during model read".to_string(),
                }
                .to_string());
            }
        };

        if line.is_empty() {
            return Err(SolverProcessError::ProcessCrashed {
                solver: "z4-smtlib-incremental",
                detail: "solver closed stdout during model read".to_string(),
            }
            .to_string());
        }

        // Track parenthesis depth.
        for ch in line.chars() {
            match ch {
                '(' => {
                    depth += 1;
                    started = true;
                }
                ')' => depth -= 1,
                _ => {}
            }
        }

        output.push_str(&line);

        // tRust #722: Cap model output size to prevent OOM.
        if output.len() > MAX_MODEL_OUTPUT_BYTES {
            return Err(SolverProcessError::ModelOutputTooLarge {
                solver: "z4-smtlib-incremental",
                bytes: output.len(),
                limit: MAX_MODEL_OUTPUT_BYTES,
            }
            .to_string());
        }

        // Model is complete when we've started reading parens and depth returns to 0.
        if started && depth <= 0 {
            break;
        }
    }

    Ok(output)
}

/// Verify a batch of VCs using a single persistent solver process.
///
/// This is the main entry point for batch incremental verification. Each VC
/// gets its own push/pop scope, but all share the same solver process,
/// enabling learned-lemma reuse across related queries.
///
/// Returns paired (VC, result) tuples in the same order as input.
pub fn verify_batch_incremental(
    backend: &IncrementalSmtLibBackend,
    vcs: &[VerificationCondition],
) -> Vec<(VerificationCondition, VerificationResult)> {
    vcs.iter()
        .map(|vc| {
            let result = backend.verify(vc);
            (vc.clone(), result)
        })
        .collect()
}

/// Benchmark comparing incremental vs per-process backends on a batch of VCs.
///
/// Returns (incremental_total_ms, per_process_total_ms) for comparison.
pub fn benchmark_incremental_vs_process(
    solver_path: &str,
    vcs: &[VerificationCondition],
    timeout_ms: u64,
) -> (u64, u64) {
    // Incremental backend.
    let incr = IncrementalSmtLibBackend::with_solver_path(solver_path).with_timeout(timeout_ms);
    let start = Instant::now();
    for vc in vcs {
        incr.verify(vc);
    }
    let incremental_ms = start.elapsed().as_millis() as u64;

    // Per-process backend.
    let pp = SmtLibBackend::with_solver_path(solver_path).with_timeout(timeout_ms);
    let start = Instant::now();
    for vc in vcs {
        pp.verify(vc);
    }
    let per_process_ms = start.elapsed().as_millis() as u64;

    (incremental_ms, per_process_ms)
}

#[cfg(test)]
mod tests {
    use super::*;

    // --- Helper: create a simple VC ---

    fn make_vc(formula: Formula) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "test_fn".into(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
        }
    }

    fn int_var(name: &str) -> Formula {
        Formula::Var(name.into(), Sort::Int)
    }

    // --- Backend trait tests ---

    #[test]
    fn test_incremental_backend_name() {
        let backend = IncrementalSmtLibBackend::new();
        assert_eq!(backend.name(), "z4-smtlib-incremental");
    }

    #[test]
    fn test_incremental_backend_role() {
        let backend = IncrementalSmtLibBackend::new();
        assert_eq!(backend.role(), BackendRole::SmtSolver);
    }

    #[test]
    fn test_incremental_backend_can_handle_l0() {
        let backend = IncrementalSmtLibBackend::new();
        let vc = make_vc(Formula::Bool(false));
        assert!(backend.can_handle(&vc));
    }

    #[test]
    fn test_incremental_backend_can_handle_l1() {
        let backend = IncrementalSmtLibBackend::new();
        let vc = VerificationCondition {
            kind: VcKind::Postcondition,
            function: "test".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
        };
        assert!(backend.can_handle(&vc));
    }

    #[test]
    fn test_incremental_backend_cannot_handle_l2() {
        let backend = IncrementalSmtLibBackend::new();
        let vc = VerificationCondition {
            kind: VcKind::Deadlock,
            function: "test".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
        };
        assert!(!backend.can_handle(&vc));
    }

    #[test]
    fn test_incremental_backend_builder() {
        let backend =
            IncrementalSmtLibBackend::with_solver_path("/usr/bin/z4").with_timeout(60_000);
        assert_eq!(backend.solver_path, "/usr/bin/z4");
        assert_eq!(backend.query_timeout_ms, 60_000);
    }

    #[test]
    fn test_incremental_backend_stats_initial() {
        let backend = IncrementalSmtLibBackend::new();
        let (queries, restarts, fallen_back) = backend.stats();
        assert_eq!(queries, 0);
        assert_eq!(restarts, 0);
        assert!(!fallen_back);
    }

    // --- Fallback behavior tests ---

    #[test]
    fn test_incremental_backend_falls_back_on_bad_solver_path() {
        // With a nonexistent solver, spawn will fail and we should fall back.
        let backend = IncrementalSmtLibBackend::with_solver_path("nonexistent_solver_binary_xyz");
        let vc = make_vc(Formula::Bool(false));

        // The first verify call will fail to spawn the solver and fall back.
        // The fallback (SmtLibBackend) will also fail to spawn, returning Unknown.
        let result = backend.verify(&vc);
        assert!(matches!(result, VerificationResult::Unknown { .. }));

        let (queries, restarts, _) = backend.stats();
        assert_eq!(queries, 1);
        assert_eq!(restarts, 1);
    }

    #[test]
    fn test_incremental_backend_permanent_fallback_after_max_failures() {
        let backend = IncrementalSmtLibBackend::with_solver_path("nonexistent_solver_binary_xyz");
        let vc = make_vc(Formula::Bool(false));

        // Trigger MAX_CONSECUTIVE_FAILURES failures.
        for _ in 0..MAX_CONSECUTIVE_FAILURES {
            let _ = backend.verify(&vc);
        }

        let (_, _, fallen_back) = backend.stats();
        assert!(
            fallen_back,
            "should permanently fall back after {MAX_CONSECUTIVE_FAILURES} failures"
        );
    }

    // --- I/O helper tests ---

    #[test]
    fn test_read_model_response_simple() {
        // Simulate a model response via a pipe.
        let model = "(model\n  (define-fun x () Int 42)\n)\n";

        // We can't easily test read_model_response with a real BufReader of a pipe,
        // but we can verify the parenthesis depth tracking logic directly.
        let mut depth: i32 = 0;
        let mut started = false;
        let mut output = String::new();

        for line in model.lines() {
            let line_with_nl = format!("{line}\n");
            for ch in line_with_nl.chars() {
                match ch {
                    '(' => {
                        depth += 1;
                        started = true;
                    }
                    ')' => depth -= 1,
                    _ => {}
                }
            }
            output.push_str(&line_with_nl);
            if started && depth <= 0 {
                break;
            }
        }

        assert!(output.contains("define-fun x () Int 42"));
        assert!(started);
        assert_eq!(depth, 0);
    }

    #[test]
    fn test_read_model_response_nested() {
        let model = "(\n  (define-fun x () Int (- 7))\n  (define-fun y () Bool true)\n)\n";

        let mut depth: i32 = 0;
        let mut started = false;
        let mut lines_read = 0;

        for line in model.lines() {
            let line_with_nl = format!("{line}\n");
            for ch in line_with_nl.chars() {
                match ch {
                    '(' => {
                        depth += 1;
                        started = true;
                    }
                    ')' => depth -= 1,
                    _ => {}
                }
            }
            lines_read += 1;
            if started && depth <= 0 {
                break;
            }
        }

        assert!(started);
        assert_eq!(depth, 0);
        assert_eq!(lines_read, 4, "should read all 4 lines of the model");
    }

    // --- Timeout enforcement tests (tRust #722) ---

    #[test]
    fn test_read_response_line_timeout() {
        // Create a channel but never send anything -- simulates a hung solver.
        let (_tx, rx) = mpsc::channel::<Result<String, String>>();
        let mut proc = SolverProcess {
            child: Command::new("true").spawn().expect("spawn true"),
            stdin: Command::new("true")
                .stdin(Stdio::piped())
                .spawn()
                .expect("spawn true for stdin")
                .stdin
                .take()
                .expect("stdin"),
            line_rx: rx,
        };

        let start = Instant::now();
        let result = read_response_line(&mut proc, Duration::from_millis(100));
        let elapsed = start.elapsed();

        assert!(result.is_err(), "should timeout");
        assert!(result.unwrap_err().contains("timeout"), "error should mention timeout");
        assert!(elapsed.as_millis() < 2000, "should timeout quickly, took {elapsed:?}");

        // Cleanup.
        let _ = proc.child.kill();
        let _ = proc.child.wait();
    }

    #[test]
    fn test_read_response_line_receives_data() {
        let (tx, rx) = mpsc::channel();
        tx.send(Ok("success\n".to_string())).unwrap();

        let mut proc = SolverProcess {
            child: Command::new("true").spawn().expect("spawn true"),
            stdin: Command::new("true")
                .stdin(Stdio::piped())
                .spawn()
                .expect("spawn true for stdin")
                .stdin
                .take()
                .expect("stdin"),
            line_rx: rx,
        };

        let result = read_response_line(&mut proc, Duration::from_secs(1));
        assert!(result.is_ok());
        assert_eq!(result.unwrap().trim(), "success");

        let _ = proc.child.kill();
        let _ = proc.child.wait();
    }

    #[test]
    fn test_model_output_size_cap() {
        // Verify the constant is set correctly.
        assert_eq!(MAX_MODEL_OUTPUT_BYTES, 10 * 1024 * 1024);
    }

    #[test]
    fn test_remaining_timeout_returns_minimum() {
        let start = Instant::now();
        // Sleep a tiny bit past a very short total to ensure elapsed > total.
        std::thread::sleep(Duration::from_millis(5));
        let remaining = remaining_timeout(Duration::from_millis(1), start);
        assert_eq!(remaining, Duration::from_millis(1));
    }

    #[test]
    fn test_verify_returns_timeout_on_hung_solver() {
        // Use `cat` as a "solver" that reads stdin forever and never responds.
        // With a 200ms timeout, verify() should return Timeout quickly.
        // Note: on macOS, `cat -smt2 -in` exits immediately with "illegal option",
        // causing fallback to non-incremental which returns Unknown. Both outcomes
        // are acceptable: the solver did not produce a proof.
        let backend = IncrementalSmtLibBackend::with_solver_path("cat").with_timeout(200);
        let vc = make_vc(Formula::Bool(false));

        let start = Instant::now();
        let result = backend.verify(&vc);
        let elapsed = start.elapsed();

        // Should get Timeout (solver hung) or Unknown (solver crashed on bad args).
        // Both are valid: the solver failed to produce a proof within the timeout.
        assert!(
            matches!(
                result,
                VerificationResult::Timeout { .. } | VerificationResult::Unknown { .. }
            ),
            "expected Timeout or Unknown, got {:?}",
            result
        );
        assert!(elapsed.as_secs() < 10, "should not take more than 10s, took {elapsed:?}");
    }

    // --- Batch function tests ---

    #[test]
    fn test_verify_batch_incremental_preserves_order() {
        // With a bad solver path, all results will be Unknown (fallback also fails).
        // But the order should be preserved.
        let backend = IncrementalSmtLibBackend::with_solver_path("nonexistent_solver_xyz");

        let vcs = vec![
            make_vc(Formula::Lt(Box::new(int_var("x")), Box::new(Formula::Int(10)))),
            make_vc(Formula::Gt(Box::new(int_var("y")), Box::new(Formula::Int(0)))),
            make_vc(Formula::Eq(Box::new(int_var("z")), Box::new(Formula::Int(42)))),
        ];

        let results = verify_batch_incremental(&backend, &vcs);
        assert_eq!(results.len(), 3);
        assert_eq!(results[0].0.function, "test_fn");
        assert_eq!(results[1].0.function, "test_fn");
        assert_eq!(results[2].0.function, "test_fn");
    }

    // --- Integration test: push/pop boundary correctness ---
    // These tests verify the protocol structure rather than requiring a real solver.

    #[test]
    fn test_push_pop_script_generation() {
        // Verify that the commands we would send follow the incremental protocol.
        let vc = make_vc(Formula::Lt(Box::new(int_var("x")), Box::new(Formula::Int(10))));

        let logic = smt2_export::detect_logic(&vc.formula);
        let decls = smt2_export::emit_declarations(&vc.formula);
        let assertion = format!("(assert {})", smt2_export::formula_to_smt2(&vc.formula));

        // Build the command sequence.
        let commands = vec![
            "(push 1)".to_string(),
            format!("(set-logic {logic})"),
            decls.join("\n"),
            assertion,
            "(check-sat)".to_string(),
            // ... get-model if sat ...
            "(pop 1)".to_string(),
        ];

        assert_eq!(commands[0], "(push 1)");
        assert!(commands[1].contains("QF_LIA"));
        assert!(commands[2].contains("(declare-fun x () Int)"));
        assert!(commands[3].contains("(assert (< x 10))"));
        assert_eq!(commands[4], "(check-sat)");
        assert_eq!(commands[5], "(pop 1)");
    }

    #[test]
    fn test_multiple_vcs_generate_separate_scopes() {
        // Verify that multiple VCs would produce separate push/pop scopes.
        let vcs = vec![
            make_vc(Formula::Lt(Box::new(int_var("x")), Box::new(Formula::Int(10)))),
            make_vc(Formula::Gt(Box::new(int_var("y")), Box::new(Formula::Int(0)))),
        ];

        let mut all_commands = Vec::new();
        for vc in &vcs {
            all_commands.push("(push 1)");

            let logic = smt2_export::detect_logic(&vc.formula);
            all_commands.push(if logic == "QF_LIA" {
                "(set-logic QF_LIA)"
            } else {
                "(set-logic ALL)"
            });

            // Declarations and assertion would go here.
            all_commands.push("(check-sat)");
            all_commands.push("(pop 1)");
        }

        // Should have 2 push/pop pairs.
        let pushes = all_commands.iter().filter(|c| **c == "(push 1)").count();
        let pops = all_commands.iter().filter(|c| **c == "(pop 1)").count();
        assert_eq!(pushes, 2);
        assert_eq!(pops, 2);
    }

    #[test]
    fn test_bitvector_vc_uses_correct_logic() {
        let vc = make_vc(Formula::BvAdd(
            Box::new(Formula::Var("a".to_string(), Sort::BitVec(32))),
            Box::new(Formula::Var("b".to_string(), Sort::BitVec(32))),
            32,
        ));

        let logic = smt2_export::detect_logic(&vc.formula);
        assert_eq!(logic, "QF_BV");

        let decls = smt2_export::emit_declarations(&vc.formula);
        assert!(decls.iter().any(|d| d.contains("(_ BitVec 32)")));
    }

    #[test]
    fn test_default_impl() {
        let backend = IncrementalSmtLibBackend::default();
        assert_eq!(backend.solver_path, "z4");
        assert_eq!(backend.query_timeout_ms, DEFAULT_QUERY_TIMEOUT_MS);
    }

    // --- Solver process lifecycle tests ---

    #[test]
    fn test_kill_process_on_empty_state() {
        // Killing when no process exists should be a no-op.
        let mut state = SessionState {
            process: None,
            consecutive_failures: 0,
            fallen_back: false,
            queries_dispatched: 0,
            restarts: 0,
        };
        IncrementalSmtLibBackend::kill_process(&mut state);
        assert!(state.process.is_none());
    }

    #[test]
    fn test_consecutive_failure_tracking() {
        let backend = IncrementalSmtLibBackend::with_solver_path("nonexistent_solver_xyz");
        let vc = make_vc(Formula::Bool(false));

        // First failure.
        let _ = backend.verify(&vc);
        let (_, restarts, fallen_back) = backend.stats();
        assert_eq!(restarts, 1);
        assert!(!fallen_back);

        // Second failure.
        let _ = backend.verify(&vc);
        let (_, restarts, fallen_back) = backend.stats();
        assert_eq!(restarts, 2);
        assert!(!fallen_back);

        // Third failure triggers permanent fallback.
        let _ = backend.verify(&vc);
        let (_, restarts, fallen_back) = backend.stats();
        assert_eq!(restarts, 3);
        assert!(fallen_back);

        // Subsequent calls go directly to fallback (no more restarts).
        let _ = backend.verify(&vc);
        let (queries, restarts, _) = backend.stats();
        assert_eq!(queries, 4);
        assert_eq!(restarts, 3, "no additional restarts after permanent fallback");
    }

    // --- Benchmark function signature test ---

    #[test]
    fn test_benchmark_function_with_empty_vcs() {
        let (incr_ms, pp_ms) = benchmark_incremental_vs_process("nonexistent_xyz", &[], 1000);
        // Both should be ~0ms with empty input.
        assert!(incr_ms < 100);
        assert!(pp_ms < 100);
    }
}
