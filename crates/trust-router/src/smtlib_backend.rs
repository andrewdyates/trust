// trust-router/smtlib_backend.rs: SMT-LIB2 subprocess backend + shared utility functions
//
// Serializes Formula to SMT-LIB2 text, invokes z4 (or any SMT-LIB2 solver)
// as a subprocess, and parses the result. This avoids linking z4 as a Rust
// dependency (stacker version conflict with compiler crates).
//
// tRust #798: The SmtLibBackend subprocess struct is feature-gated behind
// `not(pipeline-v2)` -- Pipeline v2 uses direct library calls instead.
// Utility functions (generate_smtlib_script, parse_solver_output, etc.) remain
// always available as they are used by certus_backend and ownership_encoding.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeSet;
use std::fmt::Write;
#[cfg(not(feature = "pipeline-v2"))]
use std::io::Write as _;
#[cfg(not(feature = "pipeline-v2"))]
use std::process::{Command, Stdio};
#[cfg(not(feature = "pipeline-v2"))]
use std::sync::mpsc;
#[cfg(not(feature = "pipeline-v2"))]
use std::time::{Duration, Instant};

use trust_types::*;

use crate::smt2_export;
#[cfg(not(feature = "pipeline-v2"))]
use crate::{BackendRole, VerificationBackend};
use trust_types::fx::FxHashSet;

// tRust #798: SmtLibBackend struct and its subprocess-based impls are v1-only.
// Pipeline v2 uses direct library calls via trust-zani-lib / trust-sunder-lib.
#[cfg(not(feature = "pipeline-v2"))]
/// Default timeout for solver subprocess in milliseconds.
const DEFAULT_TIMEOUT_MS: u64 = 30_000;

/// Verification backend that communicates with z4 via SMT-LIB2 over stdin/stdout.
///
/// tRust #798: Feature-gated behind `not(pipeline-v2)`. Pipeline v2 uses
/// direct library calls instead of subprocess communication.
#[cfg(not(feature = "pipeline-v2"))]
pub struct SmtLibBackend {
    /// Path to the solver binary (default: "z4").
    pub(crate) solver_path: String,
    /// Extra arguments passed to the solver (default: ["-smt2", "-in"]).
    solver_args: Vec<String>,
    /// Timeout in milliseconds.
    pub(crate) timeout_ms: u64,
}

#[cfg(not(feature = "pipeline-v2"))]
impl SmtLibBackend {
    /// Create a backend that invokes z4 at the default path.
    pub fn new() -> Self {
        SmtLibBackend {
            solver_path: "z4".to_string(),
            solver_args: vec!["-smt2".to_string(), "-in".to_string()],
            timeout_ms: DEFAULT_TIMEOUT_MS,
        }
    }

    /// Create a backend with a custom solver path.
    pub fn with_solver_path(path: impl Into<String>) -> Self {
        SmtLibBackend {
            solver_path: path.into(),
            solver_args: vec!["-smt2".to_string(), "-in".to_string()],
            timeout_ms: DEFAULT_TIMEOUT_MS,
        }
    }

    /// Set the timeout in milliseconds.
    pub fn with_timeout(mut self, timeout_ms: u64) -> Self {
        self.timeout_ms = timeout_ms;
        self
    }

    /// Run the solver on an SMT-LIB2 script and return (stdout, stderr).
    ///
    /// tRust #732: Returns both stdout and stderr so callers can inspect solver
    /// warnings even on successful (unsat) results. Previously stderr was silently
    /// discarded when stdout started with "unsat".
    ///
    /// tRust #688: Enforces `timeout_ms` by spawning a reader thread that calls
    /// `wait_with_output()`. The main thread waits on a channel with a deadline.
    /// On timeout, we kill the child process by PID to avoid zombie processes,
    /// then return a "solver timeout" error.
    fn run_solver(&self, script: &str) -> Result<(String, String), String> {
        let mut child = Command::new(&self.solver_path)
            .args(&self.solver_args)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .map_err(|e| format!("failed to spawn {}: {e}", self.solver_path))?;

        // Capture PID before moving child into reader thread, so we can kill
        // the process on timeout.
        let child_pid = child.id();

        if let Some(mut stdin) = child.stdin.take() {
            stdin
                .write_all(script.as_bytes())
                .map_err(|e| format!("failed to write to solver stdin: {e}"))?;
            // Drop stdin to signal EOF so the solver begins processing.
        }

        // tRust #688: Use a channel + reader thread to enforce the timeout.
        // `wait_with_output()` blocks the reader thread while the main thread
        // waits on the channel with a deadline.
        let timeout = Duration::from_millis(self.timeout_ms);
        let (tx, rx) = mpsc::channel();

        // Move child into a thread that calls the blocking wait_with_output().
        std::thread::spawn(move || {
            let result = child.wait_with_output();
            // Send the result back; ignore error if receiver already dropped (timeout).
            let _ = tx.send(result);
        });

        let output = match rx.recv_timeout(timeout) {
            Ok(Ok(output)) => output,
            Ok(Err(e)) => {
                return Err(format!("failed to read solver output: {e}"));
            }
            Err(mpsc::RecvTimeoutError::Timeout) => {
                // tRust #688: Timeout expired -- kill the child process to avoid
                // zombies. The reader thread's `wait_with_output()` will then
                // return (with an error or partial output) and the thread exits.
                kill_process_by_pid(child_pid);
                return Err("solver timeout".to_string());
            }
            Err(mpsc::RecvTimeoutError::Disconnected) => {
                return Err("solver thread panicked".to_string());
            }
        };

        let stdout = String::from_utf8_lossy(&output.stdout).to_string();
        let stderr = String::from_utf8_lossy(&output.stderr).to_string();

        // tRust #732: Return both stdout and stderr. Previously stderr was
        // discarded for unsat results (#556 only fixed the sat/unsat confusion).
        // Now callers get stderr for all results and can decide how to handle it.
        //
        // For non-unsat results with stderr, we still return an error because
        // that indicates a solver crash or parsing failure.
        if !stderr.is_empty() && !stdout.trim().starts_with("unsat") {
            return Err(format!("solver stderr: {stderr}"));
        }

        Ok((stdout, stderr))
    }
}

/// tRust #688: Kill a process by PID using the platform's kill command.
///
/// Uses `kill -9` on Unix and `taskkill /F` on Windows. This avoids
/// requiring a `libc` dependency for `SIGKILL`.
///
/// tRust #798: Gated behind `not(pipeline-v2)` -- only used by subprocess backends.
#[cfg(not(feature = "pipeline-v2"))]
pub(crate) fn kill_process_by_pid(pid: u32) {
    #[cfg(unix)]
    {
        let _ = std::process::Command::new("kill").args(["-9", &pid.to_string()]).output();
    }
    #[cfg(not(unix))]
    {
        let _ =
            std::process::Command::new("taskkill").args(["/F", "/PID", &pid.to_string()]).output();
    }
}

/// tRust #732: Check if solver stderr contains patterns indicating the result
/// may be unreliable. These patterns suggest the solver hit resource limits,
/// used incomplete quantifier instantiation, or otherwise produced a result
/// that should not be trusted as a definitive proof.
///
/// Returns `true` if any unreliability indicator is found in stderr.
#[cfg(any(not(feature = "pipeline-v2"), test))]
pub(crate) fn stderr_indicates_unreliable(stderr: &str) -> bool {
    if stderr.is_empty() {
        return false;
    }
    let lower = stderr.to_lowercase();
    // Patterns that indicate the solver result may be unreliable:
    // - rlimit / resource limit exhaustion
    // - incomplete quantifier instantiation
    // - timeout within the solver (internal timeout, not our process timeout)
    // - memory limit
    // - "gave up" / "approximat" heuristic fallback
    const UNRELIABLE_PATTERNS: &[&str] = &[
        "rlimit",
        "resource limit",
        "incomplete",
        "quantifier instantiation",
        "timeout",
        "memout",
        "memory limit",
        "gave up",
        "approximat",
    ];
    UNRELIABLE_PATTERNS.iter().any(|pat| lower.contains(pat))
}

#[cfg(not(feature = "pipeline-v2"))]
impl Default for SmtLibBackend {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(not(feature = "pipeline-v2"))]
impl VerificationBackend for SmtLibBackend {
    fn name(&self) -> &str {
        "z4-smtlib"
    }

    fn role(&self) -> BackendRole {
        BackendRole::SmtSolver
    }

    fn can_handle(&self, vc: &VerificationCondition) -> bool {
        matches!(vc.kind.proof_level(), ProofLevel::L0Safety | ProofLevel::L1Functional)
    }

    fn verify(&self, vc: &VerificationCondition) -> VerificationResult {
        let start = Instant::now();

        // Generate the SMT-LIB2 script
        let script = generate_smtlib_script(&vc.formula);

        // Run the solver (tRust #688: timeout is now enforced inside run_solver)
        let (stdout, stderr) = match self.run_solver(&script) {
            Ok(pair) => pair,
            Err(e) => {
                // tRust #688: Distinguish timeout from other errors so callers
                // see VerificationResult::Timeout instead of Unknown.
                if e == "solver timeout" {
                    return VerificationResult::Timeout {
                        solver: "z4-smtlib".into(),
                        timeout_ms: self.timeout_ms,
                    };
                }
                return VerificationResult::Unknown {
                    solver: "z4-smtlib".into(),
                    time_ms: start.elapsed().as_millis() as u64,
                    reason: e,
                };
            }
        };

        let elapsed = start.elapsed().as_millis() as u64;

        // tRust #732: Log stderr warnings and downgrade to Unknown if stderr
        // contains indicators that the solver result may be unreliable.
        if !stderr.is_empty() {
            eprintln!("z4-smtlib: solver stderr (vc={}): {stderr}", vc.kind);
        }

        // tRust #732: If stderr contains unreliability indicators, downgrade
        // to Unknown before even parsing. These patterns indicate the solver
        // hit resource limits or used incomplete reasoning.
        if stderr_indicates_unreliable(&stderr) {
            return VerificationResult::Unknown {
                solver: "z4-smtlib".into(),
                time_ms: elapsed,
                reason: format!("solver stderr suggests unreliable result: {stderr}"),
            };
        }

        // tRust #732: Parse stderr into individual warning lines and pass them
        // through to the result so they are preserved in solver_warnings.
        let warnings: Vec<String> =
            stderr.lines().map(|l| l.trim().to_string()).filter(|l| !l.is_empty()).collect();

        parse_solver_output(&stdout, elapsed, warnings)
    }
}

/// Generate a complete SMT-LIB2 script for a verification condition.
///
/// The script declares variables, asserts the formula, calls check-sat,
/// and if sat, calls get-model to extract counterexample values.
pub(crate) fn generate_smtlib_script(formula: &Formula) -> String {
    let mut script = String::new();

    // tRust #556: Use detect_logic() for correct logic selection.
    // The previous `has_bitvectors() ? QF_BV : QF_LIA` missed quantified
    // formulas (QF_ prefix means quantifier-free) and array theory.
    let logic = smt2_export::detect_logic(formula);
    let _ = writeln!(script, "(set-logic {logic})");

    // tRust #556: Add :produce-models so (get-model) works correctly.
    script.push_str("(set-option :produce-models true)\n");

    // Collect and declare variables
    let mut vars = BTreeSet::new();
    collect_vars(formula, &mut vars);
    for (name, sort) in &vars {
        let _ = writeln!(script, "(declare-const {name} {})", sort_to_smtlib(sort));
    }

    // Assert the formula
    let _ = writeln!(script, "(assert {})", formula_to_smtlib(formula));

    // Check satisfiability
    script.push_str("(check-sat)\n");

    // Request model on sat for counterexample extraction
    script.push_str("(get-model)\n");

    script.push_str("(exit)\n");
    script
}

/// Delegate to the canonical `Formula::to_smtlib()` method in trust-types.
pub(crate) fn formula_to_smtlib(formula: &Formula) -> String {
    formula.to_smtlib()
}

/// Delegate to the canonical `Sort::to_smtlib()` method in trust-types.
fn sort_to_smtlib(sort: &Sort) -> String {
    sort.to_smtlib()
}

/// Recursively collect all free variables (with sorts) in a formula.
///
/// Uses `Formula::visit()` to traverse the AST, then excludes quantifier-bound
/// names. For top-level VCs (which rarely have quantifier name collisions) this
/// produces the same result as the previous manual traversal.
fn collect_vars(formula: &Formula, vars: &mut BTreeSet<(String, Sort)>) {
    // Collect all Var nodes, then subtract quantifier-bound names.
    let mut all_vars = BTreeSet::new();
    let mut bound_names: FxHashSet<String> = FxHashSet::default();

    formula.visit(&mut |node| {
        match node {
            Formula::Var(name, sort) => {
                all_vars.insert((name.clone(), sort.clone()));
            }
            // tRust #749: SymVar is semantically identical to Var but uses an
            // interned Symbol. Resolve to string so it gets a declare-const.
            Formula::SymVar(sym, sort) => {
                all_vars.insert((sym.as_str().to_string(), sort.clone()));
            }
            Formula::Forall(bindings, _) | Formula::Exists(bindings, _) => {
                for (name, _) in bindings {
                    bound_names.insert(name.to_string());
                }
            }
            _ => {}
        }
    });

    for (name, sort) in all_vars {
        if !bound_names.contains(&name) {
            vars.insert((name, sort));
        }
    }
}

// has_bitvectors: removed -- use Formula::has_bitvectors() directly.

/// Parse solver stdout into a VerificationResult.
///
/// Expected output format:
/// - First line: "sat", "unsat", or "unknown"
/// - If sat, subsequent lines contain the model in s-expression format
///
/// tRust #732: Accepts `solver_warnings` captured from stderr. These are
/// attached to `Proved` results so callers can inspect solver diagnostics.
pub(crate) fn parse_solver_output(
    output: &str,
    elapsed_ms: u64,
    solver_warnings: Vec<String>,
) -> VerificationResult {
    let trimmed = output.trim();

    if trimmed.starts_with("unsat") {
        return VerificationResult::Proved {
            solver: "z4-smtlib".into(),
            time_ms: elapsed_ms,
            strength: ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: if solver_warnings.is_empty() { None } else { Some(solver_warnings) },
        };
    }

    if trimmed.starts_with("sat") {
        let counterexample = parse_model(trimmed);
        return VerificationResult::Failed {
            solver: "z4-smtlib".into(),
            time_ms: elapsed_ms,
            counterexample,
        };
    }

    if trimmed.starts_with("unknown") {
        return VerificationResult::Unknown {
            solver: "z4-smtlib".into(),
            time_ms: elapsed_ms,
            reason: "solver returned unknown".to_string(),
        };
    }

    // Parse errors or unexpected output
    VerificationResult::Unknown {
        solver: "z4-smtlib".into(),
        time_ms: elapsed_ms,
        reason: format!("unexpected solver output: {}", &trimmed[..trimmed.len().min(200)]),
    }
}

/// Parse a model from solver output following the "sat" line.
///
/// Expected format (z4/z3 style):
/// ```text
/// sat
/// (model
///   (define-fun a () Int 42)
///   (define-fun b () Int 7)
/// )
/// ```
///
/// Or the parenthesized variant:
/// ```text
/// sat
/// (
///   (define-fun a () Int 42)
///   (define-fun b () Int 7)
/// )
/// ```
fn parse_model(output: &str) -> Option<Counterexample> {
    let mut assignments = Vec::new();

    // Find all define-fun entries
    for line in output.lines() {
        let trimmed = line.trim();
        if !trimmed.contains("define-fun") {
            continue;
        }

        // Parse: (define-fun <name> () <sort> <value>)
        if let Some(assignment) = parse_define_fun(trimmed) {
            assignments.push(assignment);
        }
    }

    if assignments.is_empty() {
        return None;
    }

    // Sort by name for deterministic output
    assignments.sort_by(|a, b| a.0.cmp(&b.0));
    Some(Counterexample::new(assignments))
}

/// Parse a single `(define-fun name () Sort value)` line.
fn parse_define_fun(line: &str) -> Option<(String, CounterexampleValue)> {
    // Strip outer parens and leading whitespace
    let content = line.trim().trim_start_matches('(');

    // Skip past "define-fun "
    let rest = content.strip_prefix("define-fun ")?;

    // Extract name (first token)
    let name_end = rest.find(|c: char| c.is_whitespace())?;
    let name = rest[..name_end].to_string();
    let rest = rest[name_end..].trim();

    // Skip past "()" (empty parameter list)
    let rest = rest.strip_prefix("()")?.trim();

    // Extract sort name (next token or parenthesized expression)
    let (sort_str, rest) = if rest.starts_with('(') {
        // Parenthesized sort like (_ BitVec 32)
        let depth = find_matching_paren(rest)?;
        (&rest[..=depth], rest[depth + 1..].trim())
    } else {
        let end = rest.find(|c: char| c.is_whitespace())?;
        (&rest[..end], rest[end..].trim())
    };

    // The rest is the value (possibly with trailing parens)
    let value_str = rest.trim_end_matches(')').trim();

    // Parse the value based on sort
    let value = parse_model_value(sort_str, value_str)?;

    Some((name, value))
}

/// Find the index of the matching closing paren for an opening paren at position 0.
fn find_matching_paren(s: &str) -> Option<usize> {
    let mut depth = 0;
    for (i, ch) in s.char_indices() {
        match ch {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return Some(i);
                }
            }
            _ => {}
        }
    }
    None
}

/// Parse a model value given its SMT-LIB2 sort and value string.
fn parse_model_value(sort_str: &str, value_str: &str) -> Option<CounterexampleValue> {
    if sort_str == "Bool" {
        return match value_str {
            "true" => Some(CounterexampleValue::Bool(true)),
            "false" => Some(CounterexampleValue::Bool(false)),
            _ => None,
        };
    }

    if sort_str == "Int" {
        return parse_int_value(value_str);
    }

    // BitVec sort: (_ BitVec N)
    if sort_str.contains("BitVec") {
        return parse_bv_value(value_str);
    }

    None
}

/// Parse an integer value, handling SMT-LIB2 negation syntax `(- N)`.
fn parse_int_value(s: &str) -> Option<CounterexampleValue> {
    let s = s.trim();
    if s.starts_with("(-") || s.starts_with("(- ") {
        // Negative: (- 42) or (-42)
        let inner = s.trim_start_matches('(').trim_start_matches('-').trim().trim_end_matches(')');
        let n: i128 = inner.parse().ok()?;
        Some(CounterexampleValue::Int(-n))
    } else if let Ok(n) = s.parse::<i128>() {
        if n >= 0 {
            Some(CounterexampleValue::Uint(n as u128))
        } else {
            Some(CounterexampleValue::Int(n))
        }
    } else {
        None
    }
}

/// Parse a bitvector value like `#x0000000a` or `#b1010` or `(_ bv10 32)`.
fn parse_bv_value(s: &str) -> Option<CounterexampleValue> {
    let s = s.trim();
    if let Some(hex) = s.strip_prefix("#x") {
        let n = u128::from_str_radix(hex, 16).ok()?;
        Some(CounterexampleValue::Uint(n))
    } else if let Some(bin) = s.strip_prefix("#b") {
        let n = u128::from_str_radix(bin, 2).ok()?;
        Some(CounterexampleValue::Uint(n))
    } else if s.starts_with("(_ bv") {
        // (_ bv<value> <width>)
        let inner = s.trim_start_matches("(_ bv").trim_end_matches(')');
        let parts: Vec<&str> = inner.split_whitespace().collect();
        if let Some(val_str) = parts.first() {
            let n: u128 = val_str.parse().ok()?;
            Some(CounterexampleValue::Uint(n))
        } else {
            None
        }
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // ---- Formula translation tests ----

    #[test]
    fn test_formula_to_smtlib_literals() {
        assert_eq!(formula_to_smtlib(&Formula::Bool(true)), "true");
        assert_eq!(formula_to_smtlib(&Formula::Bool(false)), "false");
        assert_eq!(formula_to_smtlib(&Formula::Int(42)), "42");
        assert_eq!(formula_to_smtlib(&Formula::Int(0)), "0");
        assert_eq!(formula_to_smtlib(&Formula::Int(-7)), "(- 7)");
    }

    #[test]
    fn test_formula_to_smtlib_variables() {
        let f = Formula::Var("x".to_string(), Sort::Int);
        assert_eq!(formula_to_smtlib(&f), "x");

        let f = Formula::Var("flag".to_string(), Sort::Bool);
        assert_eq!(formula_to_smtlib(&f), "flag");
    }

    #[test]
    fn test_formula_to_smtlib_arithmetic() {
        let a = Formula::Var("a".to_string(), Sort::Int);
        let b = Formula::Var("b".to_string(), Sort::Int);

        let add = Formula::Add(Box::new(a.clone()), Box::new(b.clone()));
        assert_eq!(formula_to_smtlib(&add), "(+ a b)");

        let sub = Formula::Sub(Box::new(a.clone()), Box::new(b.clone()));
        assert_eq!(formula_to_smtlib(&sub), "(- a b)");

        let mul = Formula::Mul(Box::new(a.clone()), Box::new(b.clone()));
        assert_eq!(formula_to_smtlib(&mul), "(* a b)");

        let div = Formula::Div(Box::new(a.clone()), Box::new(b.clone()));
        assert_eq!(formula_to_smtlib(&div), "(div a b)");

        let rem = Formula::Rem(Box::new(a), Box::new(b));
        assert_eq!(formula_to_smtlib(&rem), "(mod a b)");
    }

    #[test]
    fn test_formula_to_smtlib_comparisons() {
        let a = Formula::Var("a".to_string(), Sort::Int);
        let b = Formula::Var("b".to_string(), Sort::Int);

        assert_eq!(
            formula_to_smtlib(&Formula::Lt(Box::new(a.clone()), Box::new(b.clone()))),
            "(< a b)"
        );
        assert_eq!(
            formula_to_smtlib(&Formula::Le(Box::new(a.clone()), Box::new(b.clone()))),
            "(<= a b)"
        );
        assert_eq!(
            formula_to_smtlib(&Formula::Gt(Box::new(a.clone()), Box::new(b.clone()))),
            "(> a b)"
        );
        assert_eq!(
            formula_to_smtlib(&Formula::Ge(Box::new(a.clone()), Box::new(b.clone()))),
            "(>= a b)"
        );
        assert_eq!(formula_to_smtlib(&Formula::Eq(Box::new(a), Box::new(b))), "(= a b)");
    }

    #[test]
    fn test_formula_to_smtlib_boolean_connectives() {
        let a = Formula::Var("p".to_string(), Sort::Bool);
        let b = Formula::Var("q".to_string(), Sort::Bool);

        assert_eq!(formula_to_smtlib(&Formula::Not(Box::new(a.clone()))), "(not p)");
        assert_eq!(formula_to_smtlib(&Formula::And(vec![a.clone(), b.clone()])), "(and p q)");
        assert_eq!(formula_to_smtlib(&Formula::Or(vec![a.clone(), b.clone()])), "(or p q)");
        assert_eq!(formula_to_smtlib(&Formula::Implies(Box::new(a), Box::new(b))), "(=> p q)");

        // Empty and/or
        assert_eq!(formula_to_smtlib(&Formula::And(vec![])), "true");
        assert_eq!(formula_to_smtlib(&Formula::Or(vec![])), "false");
    }

    #[test]
    fn test_formula_to_smtlib_nested() {
        // (a + b) > MAX -- the midpoint overflow formula shape
        let a = Formula::Var("a".to_string(), Sort::Int);
        let b = Formula::Var("b".to_string(), Sort::Int);
        let sum = Formula::Add(Box::new(a), Box::new(b));
        let max_val = Formula::Int(18446744073709551615);
        let overflow = Formula::Gt(Box::new(sum), Box::new(max_val));

        assert_eq!(formula_to_smtlib(&overflow), "(> (+ a b) 18446744073709551615)");
    }

    #[test]
    fn test_formula_to_smtlib_bitvectors() {
        let bv = Formula::BitVec { value: 10, width: 32 };
        assert_eq!(formula_to_smtlib(&bv), "(_ bv10 32)");

        let a = Formula::Var("x".to_string(), Sort::BitVec(32));
        let b = Formula::Var("y".to_string(), Sort::BitVec(32));
        let bvadd = Formula::BvAdd(Box::new(a), Box::new(b), 32);
        assert_eq!(formula_to_smtlib(&bvadd), "(bvadd x y)");
    }

    #[test]
    fn test_formula_to_smtlib_ite() {
        let cond = Formula::Var("c".to_string(), Sort::Bool);
        let then = Formula::Int(1);
        let els = Formula::Int(0);
        let ite = Formula::Ite(Box::new(cond), Box::new(then), Box::new(els));
        assert_eq!(formula_to_smtlib(&ite), "(ite c 1 0)");
    }

    // ---- Output parsing tests ----

    #[test]
    fn test_parse_solver_output_unsat() {
        let result = parse_solver_output("unsat\n", 5, vec![]);
        assert!(result.is_proved());
        assert_eq!(result.solver_name(), "z4-smtlib");
        assert_eq!(result.time_ms(), 5);
        // tRust #732: No warnings when stderr is empty
        if let VerificationResult::Proved { solver_warnings, .. } = &result {
            assert!(solver_warnings.is_none());
        }
    }

    // tRust #732: Verify that stderr warnings are captured in Proved results
    #[test]
    fn test_parse_solver_output_unsat_with_warnings() {
        let warnings = vec![
            "WARNING: unknown option :produce-proofs".to_string(),
            "WARNING: deprecated feature used".to_string(),
        ];
        let result = parse_solver_output("unsat\n", 5, warnings.clone());
        assert!(result.is_proved());
        if let VerificationResult::Proved { solver_warnings, .. } = &result {
            let warnings = solver_warnings.as_ref().expect("should have warnings");
            assert_eq!(warnings.len(), 2);
            assert_eq!(warnings[0], "WARNING: unknown option :produce-proofs");
            assert_eq!(warnings[1], "WARNING: deprecated feature used");
        } else {
            panic!("expected Proved");
        }
    }

    #[test]
    fn test_parse_solver_output_sat_with_model() {
        let output = r#"sat
(model
  (define-fun a () Int 18446744073709551615)
  (define-fun b () Int 1)
)"#;
        let result = parse_solver_output(output, 10, vec![]);
        assert!(result.is_failed());
        if let VerificationResult::Failed { counterexample: Some(cex), .. } = &result {
            assert_eq!(cex.assignments.len(), 2);
            assert_eq!(cex.assignments[0].0, "a");
            assert_eq!(cex.assignments[1].0, "b");
        } else {
            panic!("expected Failed with counterexample");
        }
    }

    #[test]
    fn test_parse_solver_output_sat_no_model() {
        let result = parse_solver_output("sat\n", 3, vec![]);
        assert!(result.is_failed());
        if let VerificationResult::Failed { counterexample, .. } = &result {
            assert!(counterexample.is_none());
        } else {
            panic!("expected Failed");
        }
    }

    #[test]
    fn test_parse_solver_output_unknown() {
        let result = parse_solver_output("unknown\n", 1000, vec![]);
        assert!(matches!(result, VerificationResult::Unknown { .. }));
    }

    #[test]
    fn test_parse_solver_output_unexpected() {
        let result = parse_solver_output("(error \"some problem\")\n", 1, vec![]);
        assert!(matches!(result, VerificationResult::Unknown { .. }));
        if let VerificationResult::Unknown { reason, .. } = &result {
            assert!(reason.contains("unexpected solver output"));
        }
    }

    // ---- Model parsing tests ----

    #[test]
    fn test_parse_define_fun_int() {
        let line = "  (define-fun x () Int 42)";
        let (name, val) = parse_define_fun(line).expect("should parse");
        assert_eq!(name, "x");
        assert!(matches!(val, CounterexampleValue::Uint(42)));
    }

    #[test]
    fn test_parse_define_fun_negative_int() {
        let line = "  (define-fun y () Int (- 7))";
        let (name, val) = parse_define_fun(line).expect("should parse");
        assert_eq!(name, "y");
        assert!(matches!(val, CounterexampleValue::Int(-7)));
    }

    #[test]
    fn test_parse_define_fun_bool() {
        let line = "  (define-fun flag () Bool true)";
        let (name, val) = parse_define_fun(line).expect("should parse");
        assert_eq!(name, "flag");
        assert!(matches!(val, CounterexampleValue::Bool(true)));
    }

    #[test]
    fn test_parse_define_fun_bitvec_hex() {
        let line = "  (define-fun x () (_ BitVec 32) #x0000000a)";
        let (name, val) = parse_define_fun(line).expect("should parse");
        assert_eq!(name, "x");
        assert!(matches!(val, CounterexampleValue::Uint(10)));
    }

    #[test]
    fn test_parse_define_fun_bitvec_binary() {
        let line = "  (define-fun bits () (_ BitVec 4) #b1010)";
        let (name, val) = parse_define_fun(line).expect("should parse");
        assert_eq!(name, "bits");
        assert!(matches!(val, CounterexampleValue::Uint(10)));
    }

    // ---- Script generation tests ----

    #[test]
    fn test_generate_smtlib_script_simple() {
        // 2 == 0 (trivially unsat for division-by-zero check)
        let formula = Formula::Eq(Box::new(Formula::Int(2)), Box::new(Formula::Int(0)));
        let script = generate_smtlib_script(&formula);
        assert!(script.contains("(set-logic QF_LIA)"));
        assert!(script.contains("(assert (= 2 0))"));
        assert!(script.contains("(check-sat)"));
        assert!(script.contains("(exit)"));
        // No variable declarations for constant formula
        assert!(!script.contains("declare-const"));
    }

    #[test]
    fn test_generate_smtlib_script_with_vars() {
        let formula = Formula::Lt(
            Box::new(Formula::Var("x".to_string(), Sort::Int)),
            Box::new(Formula::Int(10)),
        );
        let script = generate_smtlib_script(&formula);
        assert!(script.contains("(declare-const x Int)"));
        assert!(script.contains("(assert (< x 10))"));
    }

    #[test]
    fn test_generate_smtlib_script_bitvector_logic() {
        let formula = Formula::BvAdd(
            Box::new(Formula::Var("x".to_string(), Sort::BitVec(32))),
            Box::new(Formula::Var("y".to_string(), Sort::BitVec(32))),
            32,
        );
        let script = generate_smtlib_script(&formula);
        assert!(script.contains("(set-logic QF_BV)"));
        assert!(script.contains("(declare-const x (_ BitVec 32))"));
        assert!(script.contains("(declare-const y (_ BitVec 32))"));
    }

    // ---- Variable collection tests ----

    #[test]
    fn test_collect_vars_simple() {
        let formula = Formula::And(vec![
            Formula::Var("a".to_string(), Sort::Int),
            Formula::Var("b".to_string(), Sort::Int),
            Formula::Int(42),
        ]);
        let mut vars = BTreeSet::new();
        collect_vars(&formula, &mut vars);
        assert_eq!(vars.len(), 2);
        assert!(vars.contains(&("a".to_string(), Sort::Int)));
        assert!(vars.contains(&("b".to_string(), Sort::Int)));
    }

    #[test]
    fn test_collect_vars_deduplicates() {
        let a = Formula::Var("x".to_string(), Sort::Int);
        let formula = Formula::Add(Box::new(a.clone()), Box::new(a));
        let mut vars = BTreeSet::new();
        collect_vars(&formula, &mut vars);
        assert_eq!(vars.len(), 1);
    }

    // tRust #749: SymVar must be collected just like Var.
    #[test]
    fn test_collect_vars_includes_symvar() {
        let sym = Symbol::intern("s");
        let formula = Formula::And(vec![
            Formula::Var("x".to_string(), Sort::Int),
            Formula::SymVar(sym, Sort::Bool),
        ]);
        let mut vars = BTreeSet::new();
        collect_vars(&formula, &mut vars);
        assert_eq!(vars.len(), 2);
        assert!(vars.contains(&("x".to_string(), Sort::Int)));
        assert!(vars.contains(&("s".to_string(), Sort::Bool)));

        // Also verify the generated script includes declare-const for the SymVar
        let script = generate_smtlib_script(&formula);
        assert!(script.contains("(declare-const s Bool)"));
        assert!(script.contains("(declare-const x Int)"));
    }

    // ---- Sort translation tests ----

    #[test]
    fn test_sort_to_smtlib() {
        assert_eq!(sort_to_smtlib(&Sort::Bool), "Bool");
        assert_eq!(sort_to_smtlib(&Sort::Int), "Int");
        assert_eq!(sort_to_smtlib(&Sort::BitVec(64)), "(_ BitVec 64)");
        assert_eq!(
            sort_to_smtlib(&Sort::Array(Box::new(Sort::Int), Box::new(Sort::Bool))),
            "(Array Int Bool)"
        );
    }

    // ---- Integration-style test: midpoint overflow formula ----

    #[test]
    fn test_midpoint_overflow_script() {
        // The midpoint overflow VC: exists a, b in [0, MAX] such that a + b > MAX
        let max_val = (1i128 << 64) - 1;
        let a = Formula::Var("a".to_string(), Sort::Int);
        let b = Formula::Var("b".to_string(), Sort::Int);
        let sum = Formula::Add(Box::new(a.clone()), Box::new(b.clone()));

        let formula = Formula::And(vec![
            Formula::Le(Box::new(Formula::Int(0)), Box::new(a.clone())),
            Formula::Le(Box::new(a), Box::new(Formula::Int(max_val))),
            Formula::Le(Box::new(Formula::Int(0)), Box::new(b.clone())),
            Formula::Le(Box::new(b), Box::new(Formula::Int(max_val))),
            Formula::Not(Box::new(Formula::And(vec![
                Formula::Le(Box::new(Formula::Int(0)), Box::new(sum.clone())),
                Formula::Le(Box::new(sum), Box::new(Formula::Int(max_val))),
            ]))),
        ]);

        let script = generate_smtlib_script(&formula);

        // Verify script structure
        assert!(script.contains("(set-logic QF_LIA)"));
        assert!(script.contains("(declare-const a Int)"));
        assert!(script.contains("(declare-const b Int)"));
        assert!(script.contains("(assert"));
        assert!(script.contains("(check-sat)"));
        assert!(script.contains("(get-model)"));

        // The overflow formula should contain the AND with bounds and NOT
        assert!(script.contains("(<= 0 a)"));
        assert!(script.contains(&format!("(<= a {max_val})")));
        assert!(script.contains("(not"));
    }

    // ---- VerificationBackend trait implementation tests ----
    // tRust #798: SmtLibBackend tests only compile without pipeline-v2.

    #[cfg(not(feature = "pipeline-v2"))]
    #[test]
    fn test_smtlib_backend_can_handle() {
        let backend = SmtLibBackend::new();

        let l0_vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "test".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
        };
        assert!(backend.can_handle(&l0_vc));

        let l1_vc = VerificationCondition {
            kind: VcKind::Postcondition,
            function: "test".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
        };
        assert!(backend.can_handle(&l1_vc));

        let l2_vc = VerificationCondition {
            kind: VcKind::Deadlock,
            function: "test".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
        };
        assert!(!backend.can_handle(&l2_vc));
    }

    #[cfg(not(feature = "pipeline-v2"))]
    #[test]
    fn test_smtlib_backend_name() {
        let backend = SmtLibBackend::new();
        assert_eq!(backend.name(), "z4-smtlib");
    }

    #[cfg(not(feature = "pipeline-v2"))]
    #[test]
    fn test_smtlib_backend_builder_methods() {
        let backend = SmtLibBackend::with_solver_path("/usr/local/bin/z4").with_timeout(60_000);
        assert_eq!(backend.solver_path, "/usr/local/bin/z4");
        assert_eq!(backend.timeout_ms, 60_000);
    }

    // ---- tRust #732: stderr handling tests ----

    #[test]
    fn test_stderr_indicates_unreliable_empty() {
        assert!(!stderr_indicates_unreliable(""));
    }

    #[test]
    fn test_stderr_indicates_unreliable_benign_warning() {
        // A benign warning that is not an unreliability indicator
        assert!(!stderr_indicates_unreliable("WARNING: unknown logic QF_LIA\n"));
    }

    #[test]
    fn test_stderr_indicates_unreliable_rlimit() {
        assert!(stderr_indicates_unreliable("WARNING: rlimit reached\n"));
    }

    #[test]
    fn test_stderr_indicates_unreliable_resource_limit() {
        assert!(stderr_indicates_unreliable("(error \"resource limit exceeded\")\n"));
    }

    #[test]
    fn test_stderr_indicates_unreliable_incomplete() {
        assert!(stderr_indicates_unreliable("WARNING: incomplete quantifier instantiation\n"));
    }

    #[test]
    fn test_stderr_indicates_unreliable_timeout() {
        assert!(stderr_indicates_unreliable("WARNING: solver timeout in theory combination\n"));
    }

    #[test]
    fn test_stderr_indicates_unreliable_memout() {
        assert!(stderr_indicates_unreliable("memout\n"));
    }

    #[test]
    fn test_stderr_indicates_unreliable_case_insensitive() {
        assert!(stderr_indicates_unreliable("RLIMIT REACHED\n"));
        assert!(stderr_indicates_unreliable("Incomplete reasoning\n"));
    }

    #[test]
    fn test_stderr_indicates_unreliable_gave_up() {
        assert!(stderr_indicates_unreliable("WARNING: solver gave up on subproblem\n"));
    }

    #[test]
    fn test_stderr_indicates_unreliable_approximation() {
        assert!(stderr_indicates_unreliable("using approximation for nonlinear arithmetic\n"));
    }
}
