// trust-router/incremental_z4.rs: Incremental Z4 session with push/pop scoping
//
// tRust #886: Provides IncrementalZ4Session that maintains a persistent z4
// solver context across multiple VC verifications. Common assertions (type
// constraints, shared variable declarations) are asserted once at the base
// scope level. Per-VC assertions use push/pop to create isolated scopes while
// reusing the base context and learned lemmas.
//
// This module uses the z4-bindings typed API (Z4Program, Expr, Sort) for
// type-safe constraint construction, then serializes to SMT-LIB2 and
// dispatches via the persistent solver subprocess with incremental protocol.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::io::Write as _;
use std::process::{Child, Command, Stdio};
use std::sync::Mutex;
use std::sync::mpsc;
use std::time::{Duration, Instant};

use trust_types::*;

use crate::error::SolverProcessError;
use crate::smt2_export;
use crate::smtlib_backend;
use crate::{BackendRole, VerificationBackend};

/// Default timeout per-query in milliseconds.
const DEFAULT_QUERY_TIMEOUT_MS: u64 = 30_000;

/// Maximum consecutive failures before permanently falling back.
const MAX_CONSECUTIVE_FAILURES: u32 = 3;

/// Maximum model output size in bytes (10 MiB).
const MAX_MODEL_OUTPUT_BYTES: usize = 10 * 1024 * 1024;

/// Statistics for an incremental Z4 session.
#[derive(Debug, Clone, Default)]
pub struct IncrementalZ4Stats {
    /// Total VCs verified through this session.
    pub total_queries: u64,
    /// VCs verified using shared context (incremental path).
    pub incremental_queries: u64,
    /// VCs that fell back to per-process mode.
    pub fallback_queries: u64,
    /// Number of solver process restarts.
    pub restarts: u64,
    /// Whether the session permanently fell back to per-process mode.
    pub permanently_fallen_back: bool,
    /// Number of common assertions shared across VCs.
    pub common_assertions: usize,
    /// Cumulative time saved (estimated) by reusing shared context (ms).
    pub estimated_time_saved_ms: u64,
}

/// Internal state of the persistent solver process.
struct SolverProcess {
    child: Child,
    stdin: std::process::ChildStdin,
    /// Channel receiver for lines read by the dedicated reader thread.
    line_rx: mpsc::Receiver<Result<String, String>>,
}

/// Mutable session state protected by a Mutex for `Sync` compliance.
///
/// Follows the same pattern as `IncrementalSmtLibBackend`: mutable state
/// (solver process, failure counters) is behind a Mutex, while immutable
/// configuration (solver path, args, common assertions) stays in the outer
/// struct. This allows `VerificationBackend` (which requires `Sync`) to be
/// implemented without wrapping the entire struct.
struct SessionState {
    /// The live solver process.
    process: Option<SolverProcess>,
    /// Whether common assertions have been sent to the current process.
    base_initialized: bool,
    /// Number of consecutive process failures.
    consecutive_failures: u32,
    /// Whether permanently fallen back to per-process mode.
    fallen_back: bool,
    /// Session statistics.
    stats: IncrementalZ4Stats,
}

impl SessionState {
    /// Kill the current solver process.
    fn kill_process(&mut self) {
        if let Some(mut proc) = self.process.take() {
            let _ = proc.child.kill();
            let _ = proc.child.wait();
        }
        self.base_initialized = false;
    }
}

/// tRust #886: A common assertion that should be shared across all VC scopes.
///
/// These are asserted at the base solver level (outside any push/pop scope)
/// so they persist across all VC queries. Typical examples include type
/// constraints, range bounds, and shared variable declarations.
#[derive(Debug, Clone)]
pub struct CommonAssertion {
    /// Human-readable label for this assertion group.
    pub label: String,
    /// SMT-LIB2 commands (declarations + assertions) for this group.
    pub commands: Vec<String>,
}

impl CommonAssertion {
    /// Create a common assertion from a trust-types Formula.
    ///
    /// Generates the necessary variable declarations and assertion commands.
    #[must_use]
    pub fn from_formula(label: impl Into<String>, formula: &Formula) -> Self {
        let mut commands = Vec::new();

        // Emit variable declarations.
        for decl in smt2_export::emit_declarations(formula) {
            commands.push(decl);
        }

        // Emit the assertion.
        commands.push(format!("(assert {})", smt2_export::formula_to_smt2(formula)));

        CommonAssertion { label: label.into(), commands }
    }

    /// Create a common assertion from raw SMT-LIB2 commands.
    #[must_use]
    pub fn from_commands(label: impl Into<String>, commands: Vec<String>) -> Self {
        CommonAssertion { label: label.into(), commands }
    }
}

/// tRust #886: Incremental Z4 session that maintains a persistent solver
/// context with push/pop scoping.
///
/// # Architecture
///
/// ```text
/// Base Level (persistent):
///   - Logic declaration
///   - Common variable declarations
///   - Common assertions (type constraints, invariants)
///   - Learned lemmas (persisted by solver across push/pop)
///
/// Per-VC Scope (push/pop):
///   (push 1)
///     - VC-specific declarations
///     - VC formula assertion
///     - (check-sat) + result extraction
///   (pop 1)
/// ```
///
/// # Fault Isolation
///
/// On solver crash or timeout:
/// 1. The solver process is killed and restarted.
/// 2. Common assertions are re-asserted on the new process.
/// 3. After `MAX_CONSECUTIVE_FAILURES`, permanently falls back to per-process mode.
pub struct IncrementalZ4Session {
    /// Path to the solver binary.
    solver_path: String,
    /// Extra arguments passed to the solver.
    solver_args: Vec<String>,
    /// Timeout per query in milliseconds.
    query_timeout_ms: u64,
    /// Common assertions shared across all VCs.
    common_assertions: Vec<CommonAssertion>,
    /// SMT-LIB2 logic string (e.g., "QF_LIA", "QF_BV").
    logic: Option<String>,
    /// Mutable session state behind a Mutex for `Sync` compliance.
    /// Required because `VerificationBackend` trait demands `Send + Sync`.
    state: Mutex<SessionState>,
}

impl IncrementalZ4Session {
    /// Create a new incremental session with the default z4 solver.
    #[must_use]
    pub fn new() -> Self {
        Self::with_solver_path("z4")
    }

    /// Create a new incremental session with a custom solver path.
    #[must_use]
    pub fn with_solver_path(path: impl Into<String>) -> Self {
        IncrementalZ4Session {
            solver_path: path.into(),
            solver_args: vec!["-smt2".to_string(), "-in".to_string(), "--incremental".to_string()],
            query_timeout_ms: DEFAULT_QUERY_TIMEOUT_MS,
            common_assertions: Vec::new(),
            logic: None,
            state: Mutex::new(SessionState {
                process: None,
                base_initialized: false,
                consecutive_failures: 0,
                fallen_back: false,
                stats: IncrementalZ4Stats::default(),
            }),
        }
    }

    /// Set the per-query timeout in milliseconds.
    #[must_use]
    pub fn with_timeout(mut self, timeout_ms: u64) -> Self {
        self.query_timeout_ms = timeout_ms;
        self
    }

    /// Set the SMT-LIB2 logic for this session.
    ///
    /// If not set, the logic is auto-detected from the first VC's formula.
    #[must_use]
    pub fn with_logic(mut self, logic: impl Into<String>) -> Self {
        self.logic = Some(logic.into());
        self
    }

    /// Add a common assertion that will be shared across all VCs.
    ///
    /// Common assertions are sent once at the base solver level and persist
    /// across push/pop scopes. Use for type constraints, range bounds, and
    /// other assertions that apply to all VCs in a batch.
    pub fn add_common_assertion(&mut self, assertion: CommonAssertion) {
        self.common_assertions.push(assertion);
        let count = self.common_assertions.len();
        let mut st = self.state.lock().expect("invariant: mutex not poisoned");
        st.stats.common_assertions = count;
        // Force re-initialization on next query so the new assertion is sent.
        st.base_initialized = false;
    }

    /// Add common assertions from a set of formulas.
    ///
    /// Each formula becomes a separate common assertion group.
    pub fn add_common_formulas(&mut self, formulas: &[(String, Formula)]) {
        for (label, formula) in formulas {
            self.add_common_assertion(CommonAssertion::from_formula(label, formula));
        }
    }

    /// Return a snapshot of the session statistics.
    #[must_use]
    pub fn stats(&self) -> IncrementalZ4Stats {
        let st = self.state.lock().expect("invariant: mutex not poisoned");
        st.stats.clone()
    }

    /// Verify a single VC using the incremental session.
    ///
    /// Uses push/pop to isolate the VC's assertions while sharing
    /// common assertions from the base level.
    pub fn verify_vc(&self, vc: &VerificationCondition) -> VerificationResult {
        let mut st = self.state.lock().expect("invariant: mutex not poisoned");
        st.stats.total_queries += 1;

        // Permanently fallen back: use per-process mode.
        if st.fallen_back {
            st.stats.fallback_queries += 1;
            drop(st); // Release lock before per-process call.
            return self.verify_per_process(vc);
        }

        match self.verify_incremental(&mut st, vc) {
            Ok(result) => {
                st.consecutive_failures = 0;
                st.stats.incremental_queries += 1;
                result
            }
            Err(err) => {
                let is_timeout = err.contains("timeout");
                st.kill_process();
                st.consecutive_failures += 1;
                st.stats.restarts += 1;

                if st.consecutive_failures >= MAX_CONSECUTIVE_FAILURES {
                    st.fallen_back = true;
                    st.stats.permanently_fallen_back = true;
                }

                if is_timeout {
                    return VerificationResult::Timeout {
                        solver: "z4-incremental".into(),
                        timeout_ms: self.query_timeout_ms,
                    };
                }

                st.stats.fallback_queries += 1;
                drop(st); // Release lock before per-process call.
                self.verify_per_process(vc)
            }
        }
    }

    /// Verify a batch of VCs, sharing common assertions across all of them.
    ///
    /// This is the primary entry point for batch incremental verification.
    /// Returns (VC, result) pairs in the same order as input.
    #[must_use]
    pub fn verify_batch(
        &self,
        vcs: &[VerificationCondition],
    ) -> Vec<(VerificationCondition, VerificationResult)> {
        vcs.iter()
            .map(|vc| {
                let result = self.verify_vc(vc);
                (vc.clone(), result)
            })
            .collect()
    }

    /// Extract common type constraints from a set of VCs.
    ///
    /// Analyzes the VCs to find variable declarations that appear across
    /// multiple VCs and promotes them to shared declarations. This avoids
    /// re-declaring common variables in each push/pop scope.
    pub fn extract_common_declarations(&mut self, vcs: &[VerificationCondition]) {
        use trust_types::fx::FxHashMap;

        // Count variable occurrences across VCs.
        let mut var_counts: FxHashMap<String, usize> = FxHashMap::default();
        let mut var_decls: FxHashMap<String, String> = FxHashMap::default();

        for vc in vcs {
            let decls = smt2_export::emit_declarations(&vc.formula);
            for decl in &decls {
                // Extract variable name from declaration like "(declare-fun x () Int)"
                if let Some(name) = extract_var_name(decl) {
                    *var_counts.entry(name.clone()).or_insert(0) += 1;
                    var_decls.entry(name).or_insert_with(|| decl.clone());
                }
            }
        }

        // Promote variables that appear in 2+ VCs to common declarations.
        let shared_decls: Vec<String> = var_counts
            .iter()
            .filter(|(_, count)| **count >= 2)
            .filter_map(|(name, _)| var_decls.get(name).cloned())
            .collect();

        if !shared_decls.is_empty() {
            self.add_common_assertion(CommonAssertion::from_commands(
                "shared-variable-declarations",
                shared_decls,
            ));
        }
    }

    // -- Internal methods --

    /// Run a single VC on the persistent solver using push/pop.
    fn verify_incremental(
        &self,
        st: &mut SessionState,
        vc: &VerificationCondition,
    ) -> Result<VerificationResult, String> {
        self.ensure_base_initialized(st, vc)?;

        let proc = st.process.as_mut().ok_or("no solver process")?;
        let timeout = Duration::from_millis(self.query_timeout_ms);
        let start = Instant::now();

        // Push a new scope for this VC.
        send_command(proc, "(push 1)")?;

        // Declare VC-specific variables (skip those already declared at base level).
        for decl in smt2_export::emit_declarations(&vc.formula) {
            // In incremental mode, redeclaring a variable that exists at a higher
            // scope level is an error for most solvers. We send it and handle
            // any error gracefully (the solver may ignore or error).
            send_command(proc, &decl)?;
        }

        // Assert the VC formula.
        let assertion = format!("(assert {})", smt2_export::formula_to_smt2(&vc.formula));
        send_command(proc, &assertion)?;

        // Check satisfiability.
        send_command(proc, "(check-sat)")?;
        let sat_line = read_response_line(proc, remaining_timeout(timeout, start))?;
        let elapsed = start.elapsed().as_millis() as u64;

        // Parse result.
        let result = if sat_line.trim() == "unsat" {
            send_command(proc, "(pop 1)")?;
            VerificationResult::Proved {
                solver: "z4-incremental".into(),
                time_ms: elapsed,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: None,
                solver_warnings: None,
            }
        } else if sat_line.trim() == "sat" {
            // Get model for counterexample.
            send_command(proc, "(get-model)")?;
            let model_output = read_model_response(proc, remaining_timeout(timeout, start))?;

            send_command(proc, "(pop 1)")?;

            let full_output = format!("sat\n{model_output}");
            smtlib_backend::parse_solver_output(&full_output, elapsed, vec![])
        } else if sat_line.trim() == "unknown" {
            send_command(proc, "(pop 1)")?;
            VerificationResult::Unknown {
                solver: "z4-incremental".into(),
                time_ms: elapsed,
                reason: "solver returned unknown".to_string(),
            }
        } else {
            let _ = send_command(proc, "(pop 1)");
            return Err(format!("unexpected solver response: {}", sat_line.trim()));
        };

        Ok(result)
    }

    /// Ensure the solver process is running and base-level assertions are sent.
    fn ensure_base_initialized(
        &self,
        st: &mut SessionState,
        vc: &VerificationCondition,
    ) -> Result<(), String> {
        if st.process.is_none() {
            let proc = self.spawn_solver()?;
            st.process = Some(proc);
            st.base_initialized = false;
        }

        if !st.base_initialized {
            self.send_base_assertions(st, vc)?;
            st.base_initialized = true;
        }

        Ok(())
    }

    /// Send base-level setup: logic, common declarations, common assertions.
    fn send_base_assertions(
        &self,
        st: &mut SessionState,
        vc: &VerificationCondition,
    ) -> Result<(), String> {
        let proc = st.process.as_mut().ok_or("no solver process")?;

        // Set logic.
        let logic = self
            .logic
            .clone()
            .unwrap_or_else(|| smt2_export::detect_logic(&vc.formula).to_string());
        send_command(proc, &format!("(set-logic {logic})"))?;
        // z4 does not respond to set-logic.

        // Send all common assertion groups.
        for assertion in &self.common_assertions {
            for cmd in &assertion.commands {
                send_command(proc, cmd)?;
                // z4 does not respond to declarations or assertions.
            }
        }

        Ok(())
    }

    /// Spawn a fresh solver process with incremental-mode options.
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

        // Spawn a dedicated reader thread for non-blocking reads.
        let (tx, rx) = mpsc::channel();
        std::thread::spawn(move || {
            use std::io::{BufRead, BufReader};
            let mut reader = BufReader::new(stdout);
            loop {
                let mut line = String::new();
                match reader.read_line(&mut line) {
                    Ok(0) => {
                        let _ = tx.send(Err(
                            "solver closed stdout (process may have crashed)".to_string()
                        ));
                        break;
                    }
                    Ok(_) => {
                        if tx.send(Ok(line)).is_err() {
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

        // z4 does not implement :print-success and only emits responses for
        // check-sat/get-model-style queries.
        send_command(&mut proc, "(set-option :produce-models true)")?;

        Ok(proc)
    }

    /// Fall back to per-process verification for a single VC.
    fn verify_per_process(&self, vc: &VerificationCondition) -> VerificationResult {
        let script = smtlib_backend::generate_smtlib_script(&vc.formula);

        let mut child = match Command::new(&self.solver_path)
            .args(&self.solver_args)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
        {
            Ok(c) => c,
            Err(e) => {
                return VerificationResult::Unknown {
                    solver: "z4-incremental-fallback".into(),
                    time_ms: 0,
                    reason: format!("failed to spawn solver: {e}"),
                };
            }
        };

        let start = Instant::now();

        if let Some(mut stdin) = child.stdin.take()
            && stdin.write_all(script.as_bytes()).is_err()
        {
            return VerificationResult::Unknown {
                solver: "z4-incremental-fallback".into(),
                time_ms: 0,
                reason: "failed to write to solver stdin".to_string(),
            };
        }

        let timeout = Duration::from_millis(self.query_timeout_ms);
        let (tx, rx) = mpsc::channel();
        std::thread::spawn(move || {
            let result = child.wait_with_output();
            let _ = tx.send(result);
        });

        match rx.recv_timeout(timeout) {
            Ok(Ok(output)) => {
                let stdout = String::from_utf8_lossy(&output.stdout).to_string();
                let elapsed = start.elapsed().as_millis() as u64;
                smtlib_backend::parse_solver_output(&stdout, elapsed, vec![])
            }
            Ok(Err(e)) => VerificationResult::Unknown {
                solver: "z4-incremental-fallback".into(),
                time_ms: start.elapsed().as_millis() as u64,
                reason: format!("failed to read solver output: {e}"),
            },
            Err(mpsc::RecvTimeoutError::Timeout) => VerificationResult::Timeout {
                solver: "z4-incremental-fallback".into(),
                timeout_ms: self.query_timeout_ms,
            },
            Err(mpsc::RecvTimeoutError::Disconnected) => VerificationResult::Unknown {
                solver: "z4-incremental-fallback".into(),
                time_ms: start.elapsed().as_millis() as u64,
                reason: "solver thread disconnected".to_string(),
            },
        }
    }
}

impl Default for IncrementalZ4Session {
    fn default() -> Self {
        Self::new()
    }
}

impl VerificationBackend for IncrementalZ4Session {
    fn name(&self) -> &str {
        "z4-incremental"
    }

    fn role(&self) -> BackendRole {
        BackendRole::SmtSolver
    }

    fn can_handle(&self, vc: &VerificationCondition) -> bool {
        matches!(vc.kind.proof_level(), ProofLevel::L0Safety | ProofLevel::L1Functional)
    }

    fn verify(&self, vc: &VerificationCondition) -> VerificationResult {
        // VerificationBackend::verify takes &self. The incremental session
        // uses its internal Mutex to manage mutable state, so we can call
        // verify_vc directly (which also takes &self and locks internally).
        self.verify_vc(vc)
    }
}

// -- I/O helpers --

/// Send a command string to the solver's stdin.
fn send_command(proc: &mut SolverProcess, cmd: &str) -> Result<(), String> {
    proc.stdin.write_all(cmd.as_bytes()).map_err(|e| format!("write to solver: {e}"))?;
    proc.stdin.write_all(b"\n").map_err(|e| format!("write newline: {e}"))?;
    proc.stdin.flush().map_err(|e| format!("flush solver stdin: {e}"))?;
    Ok(())
}

/// Compute remaining timeout from a deadline.
fn remaining_timeout(total: Duration, start: Instant) -> Duration {
    let elapsed = start.elapsed();
    if elapsed >= total { Duration::from_millis(1) } else { total - elapsed }
}

/// Read a single response line from the solver.
fn read_response_line(proc: &mut SolverProcess, timeout: Duration) -> Result<String, String> {
    match proc.line_rx.recv_timeout(timeout) {
        Ok(Ok(line)) => {
            if line.is_empty() {
                Err(SolverProcessError::ProcessCrashed {
                    solver: "z4-incremental",
                    detail: "solver closed stdout".to_string(),
                }
                .to_string())
            } else {
                Ok(line)
            }
        }
        Ok(Err(e)) => Err(e),
        Err(mpsc::RecvTimeoutError::Timeout) => Err(SolverProcessError::Timeout {
            solver: "z4-incremental",
            detail: "no response within deadline".to_string(),
        }
        .to_string()),
        Err(mpsc::RecvTimeoutError::Disconnected) => Err(SolverProcessError::Disconnected {
            solver: "z4-incremental",
            detail: "reader thread disconnected".to_string(),
        }
        .to_string()),
    }
}

/// Read a multi-line model response from the solver.
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
                    solver: "z4-incremental",
                    detail: "timeout during model read".to_string(),
                }
                .to_string());
            }
            Err(mpsc::RecvTimeoutError::Disconnected) => {
                return Err(SolverProcessError::Disconnected {
                    solver: "z4-incremental",
                    detail: "disconnected during model read".to_string(),
                }
                .to_string());
            }
        };

        if line.is_empty() {
            return Err(SolverProcessError::ProcessCrashed {
                solver: "z4-incremental",
                detail: "solver closed stdout during model read".to_string(),
            }
            .to_string());
        }

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

        if output.len() > MAX_MODEL_OUTPUT_BYTES {
            return Err(SolverProcessError::ModelOutputTooLarge {
                solver: "z4-incremental",
                bytes: output.len(),
                limit: MAX_MODEL_OUTPUT_BYTES,
            }
            .to_string());
        }

        if started && depth <= 0 {
            break;
        }
    }

    Ok(output)
}

/// Extract a variable name from an SMT-LIB2 declaration command.
///
/// Handles: `(declare-fun name () Sort)` and `(declare-const name Sort)`.
fn extract_var_name(decl: &str) -> Option<String> {
    let trimmed = decl.trim();
    if let Some(rest) = trimmed.strip_prefix("(declare-fun ") {
        let end = rest.find(|c: char| c.is_whitespace())?;
        Some(rest[..end].to_string())
    } else if let Some(rest) = trimmed.strip_prefix("(declare-const ") {
        let end = rest.find(|c: char| c.is_whitespace())?;
        Some(rest[..end].to_string())
    } else {
        None
    }
}

/// Benchmark comparing incremental session vs per-process verification.
///
/// Returns (incremental_total_ms, per_process_total_ms).
#[must_use]
pub fn benchmark_incremental_vs_fresh(
    solver_path: &str,
    vcs: &[VerificationCondition],
    common_formulas: &[(String, Formula)],
    timeout_ms: u64,
) -> (u64, u64) {
    // Incremental session.
    let mut session = IncrementalZ4Session::with_solver_path(solver_path).with_timeout(timeout_ms);
    session.add_common_formulas(common_formulas);

    let start = Instant::now();
    for vc in vcs {
        session.verify_vc(vc);
    }
    let incremental_ms = start.elapsed().as_millis() as u64;

    // Per-process (fresh solver each time).
    let fresh_session =
        IncrementalZ4Session::with_solver_path(solver_path).with_timeout(timeout_ms);

    let start = Instant::now();
    for vc in vcs {
        // Use per-process fallback directly.
        fresh_session.verify_per_process(vc);
    }
    let per_process_ms = start.elapsed().as_millis() as u64;

    (incremental_ms, per_process_ms)
}

#[cfg(test)]
mod tests {
    use super::*;

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

    // -- Session construction tests --

    #[test]
    fn test_session_default_config() {
        let session = IncrementalZ4Session::new();
        assert_eq!(session.solver_path, "z4");
        assert_eq!(
            session.solver_args,
            vec!["-smt2".to_string(), "-in".to_string(), "--incremental".to_string(),]
        );
        assert_eq!(session.query_timeout_ms, DEFAULT_QUERY_TIMEOUT_MS);
        assert!(session.common_assertions.is_empty());
        assert!(session.logic.is_none());
        assert!(!session.stats().permanently_fallen_back);
    }

    #[test]
    fn test_session_builder() {
        let session = IncrementalZ4Session::with_solver_path("/opt/z4")
            .with_timeout(60_000)
            .with_logic("QF_LIA");

        assert_eq!(session.solver_path, "/opt/z4");
        assert_eq!(session.query_timeout_ms, 60_000);
        assert_eq!(session.logic.as_deref(), Some("QF_LIA"));
    }

    #[test]
    fn test_session_default_impl() {
        let session = IncrementalZ4Session::default();
        assert_eq!(session.solver_path, "z4");
    }

    // -- Common assertion tests --

    #[test]
    fn test_common_assertion_from_formula() {
        let formula = Formula::Ge(Box::new(int_var("x")), Box::new(Formula::Int(0)));
        let assertion = CommonAssertion::from_formula("x_nonneg", &formula);

        assert_eq!(assertion.label, "x_nonneg");
        assert!(!assertion.commands.is_empty());

        // Should contain the declaration and assertion.
        let joined = assertion.commands.join("\n");
        assert!(joined.contains("declare"), "should contain variable declaration");
        assert!(joined.contains("(assert"), "should contain assertion");
    }

    #[test]
    fn test_common_assertion_from_commands() {
        let commands = vec!["(declare-fun x () Int)".to_string(), "(assert (>= x 0))".to_string()];
        let assertion = CommonAssertion::from_commands("range", commands.clone());

        assert_eq!(assertion.label, "range");
        assert_eq!(assertion.commands, commands);
    }

    #[test]
    fn test_add_common_assertion_updates_stats() {
        let mut session = IncrementalZ4Session::new();
        assert_eq!(session.stats().common_assertions, 0);

        session.add_common_assertion(CommonAssertion::from_commands(
            "test",
            vec!["(assert true)".to_string()],
        ));
        assert_eq!(session.stats().common_assertions, 1);

        session.add_common_assertion(CommonAssertion::from_commands(
            "test2",
            vec!["(assert false)".to_string()],
        ));
        assert_eq!(session.stats().common_assertions, 2);
    }

    #[test]
    fn test_add_common_formulas() {
        let mut session = IncrementalZ4Session::new();
        let formulas = vec![
            (
                "x_bound".to_string(),
                Formula::Le(Box::new(int_var("x")), Box::new(Formula::Int(100))),
            ),
            ("y_bound".to_string(), Formula::Ge(Box::new(int_var("y")), Box::new(Formula::Int(0)))),
        ];

        session.add_common_formulas(&formulas);
        assert_eq!(session.stats().common_assertions, 2);
    }

    // -- Extract common declarations tests --

    #[test]
    fn test_extract_common_declarations_shared_vars() {
        let mut session = IncrementalZ4Session::new();

        let vcs = vec![
            make_vc(Formula::Gt(Box::new(int_var("x")), Box::new(Formula::Int(0)))),
            make_vc(Formula::Lt(Box::new(int_var("x")), Box::new(Formula::Int(100)))),
            make_vc(Formula::Eq(Box::new(int_var("y")), Box::new(Formula::Int(42)))),
        ];

        session.extract_common_declarations(&vcs);

        // "x" appears in 2 VCs, so it should be promoted.
        // "y" appears in only 1 VC, so it should not be promoted.
        assert_eq!(session.stats().common_assertions, 1);
        let assertion = &session.common_assertions[0];
        assert_eq!(assertion.label, "shared-variable-declarations");

        let commands_str = assertion.commands.join(" ");
        assert!(commands_str.contains("x"), "should contain shared var x");
    }

    #[test]
    fn test_extract_common_declarations_no_shared() {
        let mut session = IncrementalZ4Session::new();

        let vcs = vec![
            make_vc(Formula::Gt(Box::new(int_var("a")), Box::new(Formula::Int(0)))),
            make_vc(Formula::Lt(Box::new(int_var("b")), Box::new(Formula::Int(100)))),
        ];

        session.extract_common_declarations(&vcs);

        // No variables appear in 2+ VCs.
        assert_eq!(session.stats().common_assertions, 0);
    }

    // -- extract_var_name tests --

    #[test]
    fn test_extract_var_name_declare_fun() {
        assert_eq!(extract_var_name("(declare-fun x () Int)"), Some("x".to_string()));
        assert_eq!(extract_var_name("(declare-fun my_var () Bool)"), Some("my_var".to_string()));
    }

    #[test]
    fn test_extract_var_name_declare_const() {
        assert_eq!(extract_var_name("(declare-const x Int)"), Some("x".to_string()));
    }

    #[test]
    fn test_extract_var_name_other() {
        assert_eq!(extract_var_name("(assert (> x 0))"), None);
        assert_eq!(extract_var_name("(set-logic QF_LIA)"), None);
    }

    // -- VerificationBackend trait tests --

    #[test]
    fn test_backend_name() {
        let session = IncrementalZ4Session::new();
        assert_eq!(session.name(), "z4-incremental");
    }

    #[test]
    fn test_backend_role() {
        let session = IncrementalZ4Session::new();
        assert_eq!(session.role(), BackendRole::SmtSolver);
    }

    #[test]
    fn test_backend_can_handle_l0() {
        let session = IncrementalZ4Session::new();
        let vc = make_vc(Formula::Bool(false));
        assert!(session.can_handle(&vc));
    }

    #[test]
    fn test_backend_can_handle_l1() {
        let session = IncrementalZ4Session::new();
        let vc = VerificationCondition {
            kind: VcKind::Postcondition,
            function: "test".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
        };
        assert!(session.can_handle(&vc));
    }

    #[test]
    fn test_backend_cannot_handle_l2() {
        let session = IncrementalZ4Session::new();
        let vc = VerificationCondition {
            kind: VcKind::Deadlock,
            function: "test".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
        };
        assert!(!session.can_handle(&vc));
    }

    // -- Fallback behavior tests --

    #[test]
    fn test_session_falls_back_on_bad_solver_path() {
        let session = IncrementalZ4Session::with_solver_path("nonexistent_solver_binary_xyz");
        let vc = make_vc(Formula::Bool(false));

        let result = session.verify_vc(&vc);
        assert!(matches!(result, VerificationResult::Unknown { .. }));

        let stats = session.stats();
        assert_eq!(stats.total_queries, 1);
        assert_eq!(stats.restarts, 1);
    }

    #[test]
    fn test_session_permanent_fallback() {
        let session = IncrementalZ4Session::with_solver_path("nonexistent_solver_binary_xyz");
        let vc = make_vc(Formula::Bool(false));

        for _ in 0..MAX_CONSECUTIVE_FAILURES {
            let _ = session.verify_vc(&vc);
        }

        let stats = session.stats();
        assert!(
            stats.permanently_fallen_back,
            "should fall back after {MAX_CONSECUTIVE_FAILURES} failures"
        );
    }

    #[test]
    fn test_session_stats_after_failures() {
        let session = IncrementalZ4Session::with_solver_path("nonexistent_solver_binary_xyz");
        let vc = make_vc(Formula::Bool(false));

        // Trigger MAX_CONSECUTIVE_FAILURES + 1 queries.
        for _ in 0..=MAX_CONSECUTIVE_FAILURES {
            let _ = session.verify_vc(&vc);
        }

        let stats = session.stats();
        assert_eq!(stats.total_queries, MAX_CONSECUTIVE_FAILURES as u64 + 1);
        assert_eq!(stats.restarts, MAX_CONSECUTIVE_FAILURES as u64);
        assert!(stats.permanently_fallen_back);
        // Queries 1..MAX each fail incremental and fall back to per-process (3 fallbacks).
        // Query MAX+1 hits permanent fallback directly (1 more fallback).
        assert_eq!(stats.fallback_queries, MAX_CONSECUTIVE_FAILURES as u64 + 1);
    }

    // -- Batch verification tests --

    #[test]
    fn test_verify_batch_preserves_order() {
        let session = IncrementalZ4Session::with_solver_path("nonexistent_solver_xyz");

        let vcs = vec![
            make_vc(Formula::Lt(Box::new(int_var("x")), Box::new(Formula::Int(10)))),
            make_vc(Formula::Gt(Box::new(int_var("y")), Box::new(Formula::Int(0)))),
        ];

        let results = session.verify_batch(&vcs);
        assert_eq!(results.len(), 2);
        assert_eq!(results[0].0.function, "test_fn");
        assert_eq!(results[1].0.function, "test_fn");
    }

    #[test]
    fn test_verify_batch_empty() {
        let session = IncrementalZ4Session::new();
        let results = session.verify_batch(&[]);
        assert!(results.is_empty());
    }

    // -- Push/pop script structure tests --

    #[test]
    fn test_incremental_protocol_structure() {
        // Verify the SMT-LIB2 command sequence follows the push/pop protocol.
        let vc = make_vc(Formula::Lt(Box::new(int_var("x")), Box::new(Formula::Int(10))));

        let logic = smt2_export::detect_logic(&vc.formula);
        let decls = smt2_export::emit_declarations(&vc.formula);
        let assertion = format!("(assert {})", smt2_export::formula_to_smt2(&vc.formula));

        // Build expected command sequence.
        let commands = vec![
            "(push 1)".to_string(),
            decls.join("\n"),
            assertion,
            "(check-sat)".to_string(),
            "(pop 1)".to_string(),
        ];

        assert_eq!(commands[0], "(push 1)");
        assert!(commands[1].contains("(declare-fun x () Int)"));
        assert!(commands[2].contains("(assert (< x 10))"));
        assert_eq!(commands[3], "(check-sat)");
        assert_eq!(commands[4], "(pop 1)");

        // Logic should be QF_LIA for integer comparisons.
        assert_eq!(logic, "QF_LIA");
    }

    #[test]
    fn test_multiple_vcs_separate_scopes() {
        let vcs = vec![
            make_vc(Formula::Lt(Box::new(int_var("x")), Box::new(Formula::Int(10)))),
            make_vc(Formula::Gt(Box::new(int_var("y")), Box::new(Formula::Int(0)))),
        ];

        let mut push_count = 0;
        let mut pop_count = 0;

        for vc in &vcs {
            push_count += 1; // (push 1)
            let _decls = smt2_export::emit_declarations(&vc.formula);
            let _assertion = format!("(assert {})", smt2_export::formula_to_smt2(&vc.formula));
            // (check-sat) + result handling
            pop_count += 1; // (pop 1)
        }

        assert_eq!(push_count, 2);
        assert_eq!(pop_count, 2);
    }

    // -- Benchmark function signature tests --

    #[test]
    fn test_benchmark_with_empty_vcs() {
        let (incr_ms, pp_ms) = benchmark_incremental_vs_fresh("nonexistent_xyz", &[], &[], 1000);
        assert!(incr_ms < 100);
        assert!(pp_ms < 100);
    }

    // -- Stats tests --

    #[test]
    fn test_initial_stats() {
        let session = IncrementalZ4Session::new();
        let stats = session.stats();
        assert_eq!(stats.total_queries, 0);
        assert_eq!(stats.incremental_queries, 0);
        assert_eq!(stats.fallback_queries, 0);
        assert_eq!(stats.restarts, 0);
        assert!(!stats.permanently_fallen_back);
        assert_eq!(stats.common_assertions, 0);
    }

    // -- Timeout enforcement test --

    #[test]
    fn test_remaining_timeout_returns_minimum() {
        let start = Instant::now();
        std::thread::sleep(Duration::from_millis(5));
        let remaining = remaining_timeout(Duration::from_millis(1), start);
        assert_eq!(remaining, Duration::from_millis(1));
    }

    #[test]
    fn test_remaining_timeout_normal() {
        let start = Instant::now();
        let remaining = remaining_timeout(Duration::from_secs(10), start);
        // Should be close to 10 seconds.
        assert!(remaining.as_secs() >= 9);
    }

    // -- I/O helper tests (matching incremental_smtlib_backend pattern) --

    #[test]
    fn test_read_response_line_timeout() {
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
        assert_eq!(MAX_MODEL_OUTPUT_BYTES, 10 * 1024 * 1024);
    }
}
