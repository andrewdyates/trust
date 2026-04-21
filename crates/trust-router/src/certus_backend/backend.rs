// trust-router/certus_backend/backend.rs: CertusBackend struct and VerificationBackend impl
//
// Core backend implementation: binary discovery, subprocess management with
// timeout enforcement, SMT script generation, and result attribution.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::io::Write as _;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

use trust_types::*;

use crate::ownership_encoding::{generate_ownership_enriched_script, is_ownership_vc};
use crate::smtlib_backend::{generate_smtlib_script, parse_solver_output};
use crate::{BackendRole, VerificationBackend};

use super::unsafe_classify::is_unsafe_sep_vc;
use super::unsafe_script::generate_unsafe_ownership_script;
use super::{cached_certus_path, DEFAULT_TIMEOUT_MS};

// ---------------------------------------------------------------------------
// tRust #547: Run-solver error type
// ---------------------------------------------------------------------------

/// tRust #547: Error type for `run_solver()` that distinguishes timeouts from
/// other errors, allowing the caller to return `VerificationResult::Timeout`
/// for the former and `VerificationResult::Unknown` for the latter.
#[derive(Debug)]
pub(super) enum RunSolverError {
    /// The subprocess exceeded `timeout_ms` and was killed.
    Timeout { timeout_ms: u64 },
    /// Any other error (spawn failure, I/O error, stderr-reported error).
    Other(String),
}

// ---------------------------------------------------------------------------
// CertusBackend
// ---------------------------------------------------------------------------

/// tRust: Ownership-aware verification backend using certus subprocess.
///
/// Communicates with certus via SMT-LIB2 over stdin/stdout, similar to
/// `SmtLibBackend` for z4. Specializes in L1Functional properties
/// (preconditions and postconditions) where Rust ownership semantics
/// provide additional proof power.
///
/// tRust #360: Also handles unsafe-code VCs (UnsafeOperation, separation
/// logic assertions) where certus applies ownership-aware reasoning to
/// raw pointer dereferences, transmutes, FFI calls, and other unsafe ops.
///
/// Certus understands Rust's ownership model: borrow checking, lifetime
/// constraints, and move semantics are encoded as additional axioms in the
/// verification conditions, enabling proofs that general-purpose SMT
/// solvers cannot discharge.
pub struct CertusBackend {
    /// Path to the certus binary (None = use cached probe).
    pub(super) solver_path: Option<String>,
    /// Extra arguments passed to certus.
    pub(super) solver_args: Vec<String>,
    /// Timeout in milliseconds.
    pub(super) timeout_ms: u64,
}

impl CertusBackend {
    /// Create a backend using the auto-probed certus path.
    #[must_use]
    pub fn new() -> Self {
        CertusBackend {
            solver_path: None,
            solver_args: vec!["-smt2".to_string(), "-in".to_string()],
            timeout_ms: DEFAULT_TIMEOUT_MS,
        }
    }

    /// Create a backend with an explicit solver path.
    #[must_use]
    pub fn with_solver_path(path: impl Into<String>) -> Self {
        CertusBackend {
            solver_path: Some(path.into()),
            solver_args: vec!["-smt2".to_string(), "-in".to_string()],
            timeout_ms: DEFAULT_TIMEOUT_MS,
        }
    }

    /// Set the timeout in milliseconds.
    #[must_use]
    pub fn with_timeout(mut self, timeout_ms: u64) -> Self {
        self.timeout_ms = timeout_ms;
        self
    }

    /// Resolve the solver path: explicit > cached probe.
    fn resolve_path(&self) -> Option<&str> {
        if let Some(ref path) = self.solver_path {
            Some(path.as_str())
        } else {
            cached_certus_path().map(|s| s.as_str())
        }
    }

    /// tRust #547: Run certus on an SMT-LIB2 script with enforced timeout.
    ///
    /// Uses a `try_wait()` polling loop with the configured `timeout_ms` to
    /// prevent a hanging certus process from blocking the verification pipeline
    /// indefinitely. If the subprocess exceeds the timeout, it is killed via
    /// `child.kill()` (SIGKILL on Unix) and a timeout error is returned.
    pub(super) fn run_solver(&self, script: &str) -> Result<String, RunSolverError> {
        let path = self.resolve_path().ok_or_else(|| {
            RunSolverError::Other(
                "certus binary not found: set CERTUS_PATH env or install certus on PATH"
                    .to_string(),
            )
        })?;

        let mut child = Command::new(path)
            .args(&self.solver_args)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .map_err(|e| RunSolverError::Other(format!("failed to spawn certus at {path}: {e}")))?;

        if let Some(mut stdin) = child.stdin.take() {
            stdin
                .write_all(script.as_bytes())
                .map_err(|e| {
                    RunSolverError::Other(format!("failed to write to certus stdin: {e}"))
                })?;
        }

        // tRust #547: Enforce timeout via try_wait() polling loop instead of
        // blocking on wait_with_output(). Poll every 10ms up to timeout_ms.
        let deadline = Instant::now() + Duration::from_millis(self.timeout_ms);
        let poll_interval = Duration::from_millis(10);

        loop {
            match child.try_wait() {
                Ok(Some(_status)) => {
                    // Process exited -- collect output.
                    break;
                }
                Ok(None) => {
                    // Still running -- check deadline.
                    if Instant::now() >= deadline {
                        // tRust #547: Kill the hanging subprocess.
                        let _ = child.kill();
                        let _ = child.wait(); // Reap zombie
                        return Err(RunSolverError::Timeout {
                            timeout_ms: self.timeout_ms,
                        });
                    }
                    std::thread::sleep(poll_interval);
                }
                Err(e) => {
                    return Err(RunSolverError::Other(format!(
                        "failed to poll certus process: {e}"
                    )));
                }
            }
        }

        let output = child
            .wait_with_output()
            .map_err(|e| RunSolverError::Other(format!("failed to read certus output: {e}")))?;

        let stdout = String::from_utf8_lossy(&output.stdout).to_string();
        let stderr = String::from_utf8_lossy(&output.stderr).to_string();

        // tRust #547: Always report stderr -- do not suppress it when stdout
        // contains "sat". Stderr from certus may contain important warnings
        // or diagnostic information.
        if !stderr.is_empty() {
            eprintln!("[certus] stderr: {stderr}");
            if !output.status.success() {
                return Err(RunSolverError::Other(format!("certus stderr: {stderr}")));
            }
        }

        Ok(stdout)
    }
}

impl Default for CertusBackend {
    fn default() -> Self {
        Self::new()
    }
}

impl VerificationBackend for CertusBackend {
    fn name(&self) -> &str {
        "certus"
    }

    fn role(&self) -> BackendRole {
        BackendRole::Ownership
    }

    fn can_handle(&self, vc: &VerificationCondition) -> bool {
        // tRust: #178 Certus handles both traditional L1Functional VCs and
        // ownership-class VCs (region non-aliasing, borrow validity, mutation
        // exclusivity, use-after-move) generated by trust-vcgen/region_encoding.rs.
        if matches!(vc.kind, VcKind::Precondition { .. } | VcKind::Postcondition) {
            return true;
        }
        // tRust #360: Accept UnsafeOperation VCs — certus applies ownership-aware
        // reasoning to raw pointer dereferences, transmutes, FFI calls, etc.
        if matches!(vc.kind, VcKind::UnsafeOperation { .. }) {
            return true;
        }
        // tRust #360: Accept separation logic assertions from trust-vcgen/separation_logic.rs.
        // These carry [unsafe:sep:*] prefixes and encode heap/pointer safety checks.
        if is_unsafe_sep_vc(vc) {
            return true;
        }
        // Accept ownership VCs tagged with [memory:region] prefix.
        is_ownership_vc(vc)
    }

    fn verify(&self, vc: &VerificationCondition) -> VerificationResult {
        let start = Instant::now();

        // Check if certus is available
        if self.resolve_path().is_none() {
            return VerificationResult::Unknown {
                solver: "certus".to_string(),
                time_ms: 0,
                reason: "certus binary not found: set CERTUS_PATH env or install certus on PATH"
                    .to_string(),
            };
        }

        // tRust #360: Select the appropriate script generation based on VC type.
        let script = if matches!(vc.kind, VcKind::UnsafeOperation { .. }) || is_unsafe_sep_vc(vc) {
            // Unsafe-code VCs get the extended unsafe ownership script.
            generate_unsafe_ownership_script(vc)
        } else if is_ownership_vc(vc) {
            // tRust: #178 Use enriched encoding for ownership VCs.
            generate_ownership_enriched_script(vc)
        } else {
            // Traditional L1Functional VCs get the basic ownership script.
            generate_ownership_script(&vc.formula, &vc.kind)
        };

        // tRust #547: Run certus with enforced subprocess timeout.
        let output = match self.run_solver(&script) {
            Ok(out) => out,
            Err(RunSolverError::Timeout { timeout_ms }) => {
                return VerificationResult::Timeout {
                    solver: "certus".to_string(),
                    timeout_ms,
                };
            }
            Err(RunSolverError::Other(reason)) => {
                return VerificationResult::Unknown {
                    solver: "certus".to_string(),
                    time_ms: start.elapsed().as_millis() as u64,
                    reason,
                };
            }
        };

        let elapsed = start.elapsed().as_millis() as u64;

        // Parse the result, re-attributing to "certus" solver name
        let mut result = parse_solver_output(&output, elapsed, vec![]);
        attribute_to_certus(&mut result);
        result
    }
}

/// Generate an SMT-LIB2 script with ownership-specific annotations for certus.
///
/// Wraps the standard SMT-LIB2 script with certus-specific options:
/// - Enables ownership-aware reasoning via `(set-option :ownership-mode true)`
/// - Adds borrow-checking axioms via `(set-option :borrow-check true)`
/// - Annotates the VC kind so certus can apply appropriate proof strategies
fn generate_ownership_script(formula: &Formula, kind: &VcKind) -> String {
    let base_script = generate_smtlib_script(formula);

    let kind_annotation = match kind {
        VcKind::Precondition { callee } => format!("; certus VC kind: precondition of `{callee}`"),
        VcKind::Postcondition => "; certus VC kind: postcondition".to_string(),
        other => format!("; certus VC kind: {}", other.description()),
    };

    let mut script = String::with_capacity(base_script.len() + 256);
    script.push_str("; certus ownership-aware verification\n");
    script.push_str("(set-option :ownership-mode true)\n");
    script.push_str("(set-option :borrow-check true)\n");
    script.push_str(&kind_annotation);
    script.push('\n');
    script.push_str(&base_script);
    script
}

/// Re-attribute a parse_solver_output result to the certus solver.
///
/// parse_solver_output hardcodes "z4-smtlib" as the solver name.
/// We patch it to "certus" and adjust ProofStrength to OwnershipAnalysis
/// for proves, since certus proofs incorporate ownership reasoning beyond
/// pure SMT or generic deductive verification.
///
/// tRust #435: Changed from Deductive to OwnershipAnalysis to accurately
/// reflect certus's ownership-aware reasoning technique.
pub(super) fn attribute_to_certus(result: &mut VerificationResult) {
    match result {
        VerificationResult::Proved { solver, strength, .. } => {
            *solver = "certus".to_string();
            // tRust #435: Certus proofs use ownership-aware reasoning
            *strength = ProofStrength {
                reasoning: ReasoningKind::OwnershipAnalysis,
                assurance: AssuranceLevel::Sound,
            };
        }
        VerificationResult::Failed { solver, .. } => {
            *solver = "certus".to_string();
        }
        VerificationResult::Unknown { solver, .. } => {
            *solver = "certus".to_string();
        }
        VerificationResult::Timeout { solver, .. } => {
            *solver = "certus".to_string();
        }
        // tRust #734: non-panicking fallback for #[non_exhaustive] forward compat
        _ => {}
    }
}
