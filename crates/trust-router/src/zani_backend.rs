// trust-router/zani_backend.rs: Bounded model checking backend via zani subprocess
//
// Invokes the zani bounded model checker as a subprocess, communicating via
// SMT-LIB2 over stdin/stdout. Specializes in L0Safety VCs and produces
// concrete counterexamples when violations are found.
//
// tRust #359: Full BMC dispatch with QueryClass routing, counterexample trace
// extraction, and bound exhaustion handling.
//
// Binary discovery order: ZANI_PATH env > PATH probe > graceful fallback.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap;
use std::io::Write as _;
use std::process::{Command, Stdio};
use std::sync::OnceLock;
use std::time::Instant;
use std::fmt::Write;

use trust_types::*;

use crate::classifier::{self, QueryClass};
use crate::ownership_encoding::{formula_references_regions, is_ownership_vc};
use crate::smtlib_backend::{generate_smtlib_script, parse_solver_output};
use crate::{BackendRole, VerificationBackend};

/// Default timeout for zani subprocess in milliseconds.
const DEFAULT_TIMEOUT_MS: u64 = 30_000;

/// Default BMC unrolling depth.
const DEFAULT_BMC_DEPTH: u32 = 100;

/// Maximum BMC depth before we consider the bound exhausted.
const MAX_BMC_DEPTH: u32 = 10_000;

/// Cached zani binary path, probed once per process.
static ZANI_PATH: OnceLock<Option<String>> = OnceLock::new();

/// tRust: Probe for the zani binary.
///
/// Priority: `ZANI_PATH` env var > `zani` on PATH.
/// Returns `None` if zani is not found.
fn probe_zani_path() -> Option<String> {
    // 1. Explicit env var
    if let Ok(path) = std::env::var("ZANI_PATH")
        && std::path::Path::new(&path).exists() {
            return Some(path);
        }

    // 2. PATH probe
    if let Ok(output) = Command::new("which").arg("zani").output()
        && output.status.success() {
            let path = String::from_utf8_lossy(&output.stdout).trim().to_string();
            if !path.is_empty() {
                return Some(path);
            }
        }

    None
}

/// Get the cached zani path, probing only once.
fn cached_zani_path() -> Option<&'static String> {
    ZANI_PATH.get_or_init(probe_zani_path).as_ref()
}

// ---------------------------------------------------------------------------
// QueryClass-based routing
// ---------------------------------------------------------------------------

/// tRust #359: Determine if a VC is well-suited for zani BMC dispatch.
///
/// Zani excels at L0Safety VCs with linear arithmetic or bitvector formulas.
/// It is NOT appropriate for ownership VCs, quantified formulas, or
/// hard nonlinear arithmetic (these should go to certus, lean5, or z4).
///
/// Returns `true` if the VC's QueryClass is in zani's sweet spot.
#[must_use]
pub fn is_suitable_for_zani(vc: &VerificationCondition) -> bool {
    // Only L0Safety VCs
    if !matches!(vc.kind.proof_level(), ProofLevel::L0Safety) {
        return false;
    }

    // Reject ownership VCs
    if is_ownership_vc(vc) || formula_references_regions(&vc.formula) {
        return false;
    }

    let class = classifier::classify_vc(vc);
    matches!(
        class,
        QueryClass::EasyLinear | QueryClass::BitVector | QueryClass::Mixed
    )
}

/// tRust #359: Classify a VC for zani dispatch and return the recommended
/// BMC depth based on formula complexity.
///
/// Returns `(suitable, recommended_depth)` where `suitable` indicates
/// whether zani should handle this VC, and `recommended_depth` is the
/// suggested unrolling depth based on formula features.
#[must_use]
pub fn classify_for_zani(vc: &VerificationCondition) -> (bool, u32) {
    if !is_suitable_for_zani(vc) {
        return (false, 0);
    }

    let features = classifier::extract_features(&vc.formula);

    // Heuristic: deeper formulas need more unrolling.
    // Small formulas (< 20 nodes): 50 depth
    // Medium formulas (20-100 nodes): 100 depth
    // Large formulas (> 100 nodes): 200 depth
    // Very large formulas (> 500 nodes): 500 depth
    let depth = match features.node_count {
        0..=19 => 50,
        20..=99 => 100,
        100..=499 => 200,
        _ => 500,
    };

    (true, depth)
}

/// tRust #359: Outcome from zani BMC analysis.
///
/// Distinguishes between successful proofs (UNSAT within depth), real
/// counterexamples (SAT with model), bound exhaustion (depth reached
/// without finding a bug), timeouts, and errors.
#[derive(Debug, Clone)]
pub enum ZaniBmcOutcome {
    /// Property holds within the BMC depth (UNSAT).
    ProvedBounded {
        depth: u32,
        time_ms: u64,
    },
    /// Found a concrete counterexample (SAT with model).
    CounterexampleFound {
        counterexample: Counterexample,
        time_ms: u64,
    },
    /// BMC depth exhausted without finding a bug -- inconclusive.
    BoundExhausted {
        depth: u32,
        time_ms: u64,
    },
    /// Solver timed out.
    Timeout {
        timeout_ms: u64,
    },
    /// Error during analysis.
    Error {
        reason: String,
        time_ms: u64,
    },
}

impl ZaniBmcOutcome {
    /// Convert this BMC outcome to a `VerificationResult` for the router.
    #[must_use]
    pub fn to_verification_result(&self) -> VerificationResult {
        match self {
            ZaniBmcOutcome::ProvedBounded { depth, time_ms } => {
                VerificationResult::Proved {
                    solver: "zani".to_string(),
                    time_ms: *time_ms,
                    strength: ProofStrength::bounded(u64::from(*depth)),
                    proof_certificate: None,
                solver_warnings: None,
                }
            }
            ZaniBmcOutcome::CounterexampleFound { counterexample, time_ms } => {
                VerificationResult::Failed {
                    solver: "zani".to_string(),
                    time_ms: *time_ms,
                    counterexample: Some(counterexample.clone()),
                }
            }
            ZaniBmcOutcome::BoundExhausted { depth, time_ms } => {
                VerificationResult::Unknown {
                    solver: "zani".to_string(),
                    time_ms: *time_ms,
                    reason: format!(
                        "BMC bound exhausted at depth {depth}: \
                         no counterexample found within unrolling limit"
                    ),
                }
            }
            ZaniBmcOutcome::Timeout { timeout_ms } => {
                VerificationResult::Timeout {
                    solver: "zani".to_string(),
                    timeout_ms: *timeout_ms,
                }
            }
            ZaniBmcOutcome::Error { reason, time_ms } => {
                VerificationResult::Unknown {
                    solver: "zani".to_string(),
                    time_ms: *time_ms,
                    reason: reason.clone(),
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Backend implementation
// ---------------------------------------------------------------------------

/// tRust: Bounded model checking backend using zani subprocess.
///
/// Communicates with zani via SMT-LIB2 over stdin/stdout, similar to
/// `SmtLibBackend` for z4. Specializes in L0Safety properties and returns
/// concrete counterexamples on failure.
///
/// tRust #359: Integrates QueryClass-based routing, counterexample trace
/// extraction, and bound exhaustion detection.
pub struct ZaniBackend {
    /// Path to the zani binary (None = use cached probe).
    solver_path: Option<String>,
    /// Extra arguments passed to zani.
    solver_args: Vec<String>,
    /// Timeout in milliseconds.
    timeout_ms: u64,
    /// BMC unrolling depth.
    bmc_depth: u32,
    /// Whether to use QueryClass-based adaptive depth selection.
    adaptive_depth: bool,
}

impl ZaniBackend {
    /// Create a backend using the auto-probed zani path.
    #[must_use]
    pub fn new() -> Self {
        ZaniBackend {
            solver_path: None,
            solver_args: vec!["-smt2".to_string(), "-in".to_string()],
            timeout_ms: DEFAULT_TIMEOUT_MS,
            bmc_depth: DEFAULT_BMC_DEPTH,
            adaptive_depth: false,
        }
    }

    /// Create a backend with an explicit solver path.
    #[must_use]
    pub fn with_solver_path(path: impl Into<String>) -> Self {
        ZaniBackend {
            solver_path: Some(path.into()),
            solver_args: vec!["-smt2".to_string(), "-in".to_string()],
            timeout_ms: DEFAULT_TIMEOUT_MS,
            bmc_depth: DEFAULT_BMC_DEPTH,
            adaptive_depth: false,
        }
    }

    /// Set the timeout in milliseconds.
    #[must_use]
    pub fn with_timeout(mut self, timeout_ms: u64) -> Self {
        self.timeout_ms = timeout_ms;
        self
    }

    /// Set the BMC unrolling depth.
    #[must_use]
    pub fn with_bmc_depth(mut self, depth: u32) -> Self {
        self.bmc_depth = depth;
        self
    }

    /// tRust #359: Enable adaptive depth selection based on QueryClass.
    ///
    /// When enabled, the BMC depth is selected based on formula complexity
    /// using `classify_for_zani()`. The configured `bmc_depth` serves as
    /// a ceiling.
    #[must_use]
    pub fn with_adaptive_depth(mut self, enabled: bool) -> Self {
        self.adaptive_depth = enabled;
        self
    }

    /// Resolve the solver path: explicit > cached probe.
    fn resolve_path(&self) -> Option<&str> {
        if let Some(ref path) = self.solver_path {
            Some(path.as_str())
        } else {
            cached_zani_path().map(|s| s.as_str())
        }
    }

    /// tRust #359: Determine the effective BMC depth for a given VC.
    ///
    /// If adaptive depth is enabled, uses `classify_for_zani()` to
    /// recommend a depth, clamped to the configured ceiling.
    fn effective_depth(&self, vc: &VerificationCondition) -> u32 {
        if self.adaptive_depth {
            let (_, recommended) = classify_for_zani(vc);
            if recommended > 0 {
                recommended.min(self.bmc_depth)
            } else {
                self.bmc_depth
            }
        } else {
            self.bmc_depth
        }
    }

    /// Run zani on an SMT-LIB2 script and return raw stdout.
    fn run_solver(&self, script: &str) -> Result<String, String> {
        let path = self.resolve_path().ok_or_else(|| {
            "zani binary not found: set ZANI_PATH env or install zani on PATH".to_string()
        })?;

        let mut child = Command::new(path)
            .args(&self.solver_args)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .map_err(|e| format!("failed to spawn zani at {path}: {e}"))?;

        if let Some(mut stdin) = child.stdin.take() {
            stdin
                .write_all(script.as_bytes())
                .map_err(|e| format!("failed to write to zani stdin: {e}"))?;
        }

        let output = child
            .wait_with_output()
            .map_err(|e| format!("failed to read zani output: {e}"))?;

        let stdout = String::from_utf8_lossy(&output.stdout).to_string();
        let stderr = String::from_utf8_lossy(&output.stderr).to_string();

        if !stderr.is_empty() && !stdout.contains("sat") {
            return Err(format!("zani stderr: {stderr}"));
        }

        Ok(stdout)
    }

    /// tRust #359: Run BMC analysis and return a structured outcome.
    ///
    /// This is the core BMC dispatch method. It generates the SMT-LIB2
    /// script, runs zani, parses the output, and classifies the result
    /// into a `ZaniBmcOutcome`.
    pub fn analyze_bmc(&self, vc: &VerificationCondition) -> ZaniBmcOutcome {
        let start = Instant::now();

        // Check if zani is available
        if self.resolve_path().is_none() {
            return ZaniBmcOutcome::Error {
                reason: "zani binary not found: set ZANI_PATH env or install zani on PATH"
                    .to_string(),
                time_ms: 0,
            };
        }

        let depth = self.effective_depth(vc);

        // Generate the SMT-LIB2 script with BMC depth annotation
        let script = generate_bmc_script(&vc.formula, depth);

        // Run zani
        let output = match self.run_solver(&script) {
            Ok(out) => out,
            Err(e) => {
                return ZaniBmcOutcome::Error {
                    reason: e,
                    time_ms: start.elapsed().as_millis() as u64,
                };
            }
        };

        let elapsed = start.elapsed().as_millis() as u64;

        // Check for timeout
        if elapsed >= self.timeout_ms {
            return ZaniBmcOutcome::Timeout {
                timeout_ms: self.timeout_ms,
            };
        }

        // Parse the result
        classify_bmc_output(&output, elapsed, depth)
    }
}

impl Default for ZaniBackend {
    fn default() -> Self {
        Self::new()
    }
}

impl VerificationBackend for ZaniBackend {
    fn name(&self) -> &str {
        "zani"
    }

    fn role(&self) -> BackendRole {
        BackendRole::BoundedModelChecker
    }

    fn can_handle(&self, vc: &VerificationCondition) -> bool {
        // tRust: #193 Reject ownership VCs -- zani (BMC) does not understand
        // region/provenance axioms. These belong to certus.
        if is_ownership_vc(vc) {
            return false;
        }
        // tRust: #193 Also reject L0Safety VCs whose formulas reference
        // region/provenance variables -- the BMC engine cannot interpret them.
        if formula_references_regions(&vc.formula) {
            return false;
        }
        matches!(vc.kind.proof_level(), ProofLevel::L0Safety)
    }

    fn verify(&self, vc: &VerificationCondition) -> VerificationResult {
        let start = Instant::now();

        // Check if zani is available
        if self.resolve_path().is_none() {
            return VerificationResult::Unknown {
                solver: "zani".to_string(),
                time_ms: 0,
                reason: "zani binary not found: set ZANI_PATH env or install zani on PATH"
                    .to_string(),
            };
        }

        let depth = self.effective_depth(vc);

        // Generate the SMT-LIB2 script with BMC depth annotation
        let script = generate_bmc_script(&vc.formula, depth);

        // Run zani
        let output = match self.run_solver(&script) {
            Ok(out) => out,
            Err(e) => {
                return VerificationResult::Unknown {
                    solver: "zani".to_string(),
                    time_ms: start.elapsed().as_millis() as u64,
                    reason: e,
                };
            }
        };

        let elapsed = start.elapsed().as_millis() as u64;

        // Check for timeout
        if elapsed >= self.timeout_ms {
            return VerificationResult::Timeout {
                solver: "zani".to_string(),
                timeout_ms: self.timeout_ms,
            };
        }

        // Parse the result, attributing to "zani" solver name
        let mut result = parse_solver_output(&output, elapsed, vec![]);
        attribute_to_zani(&mut result, depth);
        result
    }
}

// ---------------------------------------------------------------------------
// Script generation
// ---------------------------------------------------------------------------

/// Generate an SMT-LIB2 script with BMC-specific options for zani.
///
/// Wraps the standard SMT-LIB2 script with zani-specific options:
/// - Sets the BMC unrolling depth via `(set-option :bmc-depth N)`
/// - Requests counterexample generation via `(set-option :produce-models true)`
fn generate_bmc_script(formula: &Formula, bmc_depth: u32) -> String {
    let base_script = generate_smtlib_script(formula);

    // Prepend BMC-specific options before the base script
    let mut script = String::with_capacity(base_script.len() + 128);
    let _ = writeln!(script, "; zani BMC configuration (depth={bmc_depth})");
    script.push_str("(set-option :produce-models true)\n");
    let _ = writeln!(script, "(set-option :bmc-depth {bmc_depth})");
    script.push_str(&base_script);
    script
}

// ---------------------------------------------------------------------------
// Result parsing and classification
// ---------------------------------------------------------------------------

/// Re-attribute a parse_solver_output result to the zani solver.
///
/// parse_solver_output hardcodes "z4-smtlib" as the solver name.
/// We patch it to "zani" and adjust ProofStrength to Bounded for proves.
fn attribute_to_zani(result: &mut VerificationResult, bmc_depth: u32) {
    match result {
        VerificationResult::Proved { solver, strength, .. } => {
            *solver = "zani".to_string();
            // BMC proves are bounded, not full SMT UNSAT proofs
            *strength = ProofStrength::bounded(u64::from(bmc_depth));
        }
        VerificationResult::Failed { solver, .. } => {
            *solver = "zani".to_string();
        }
        VerificationResult::Unknown { solver, .. } => {
            *solver = "zani".to_string();
        }
        VerificationResult::Timeout { solver, .. } => {
            *solver = "zani".to_string();
        }
        // tRust #734: non-panicking fallback for #[non_exhaustive] forward compat
        _ => {}
    }
}

/// tRust #359: Classify raw zani BMC output into a structured outcome.
///
/// Detects: UNSAT (proved within depth), SAT (counterexample found),
/// unknown (which may indicate bound exhaustion), and unexpected output.
fn classify_bmc_output(output: &str, elapsed_ms: u64, depth: u32) -> ZaniBmcOutcome {
    let trimmed = output.trim();

    if trimmed.starts_with("unsat") {
        return ZaniBmcOutcome::ProvedBounded {
            depth,
            time_ms: elapsed_ms,
        };
    }

    if trimmed.starts_with("sat") {
        // Try to extract a counterexample from the model
        if let Some(cex) = parse_bmc_counterexample(trimmed) {
            return ZaniBmcOutcome::CounterexampleFound {
                counterexample: cex,
                time_ms: elapsed_ms,
            };
        }
        // SAT but no model -- still a counterexample, just no details
        return ZaniBmcOutcome::CounterexampleFound {
            counterexample: Counterexample::new(vec![]),
            time_ms: elapsed_ms,
        };
    }

    // "unknown" from BMC typically means bound exhaustion
    if trimmed.starts_with("unknown") {
        // Check if the output mentions bound exhaustion
        let is_bound_exhausted = trimmed.contains("bound")
            || trimmed.contains("depth")
            || trimmed.contains("resource")
            || depth >= MAX_BMC_DEPTH;

        if is_bound_exhausted {
            return ZaniBmcOutcome::BoundExhausted {
                depth,
                time_ms: elapsed_ms,
            };
        }

        return ZaniBmcOutcome::Error {
            reason: "zani returned unknown (possible bound exhaustion or unsupported theory)"
                .to_string(),
            time_ms: elapsed_ms,
        };
    }

    // Unexpected output
    ZaniBmcOutcome::Error {
        reason: format!(
            "unexpected zani output: {}",
            &trimmed[..trimmed.len().min(200)]
        ),
        time_ms: elapsed_ms,
    }
}

/// tRust #359: Parse a BMC counterexample from solver SAT output.
///
/// Extracts variable assignments from `define-fun` entries in the model.
/// Also attempts to extract multi-step trace information from step-indexed
/// variables (e.g., `x_step_0`, `x_step_1`).
fn parse_bmc_counterexample(output: &str) -> Option<Counterexample> {
    let mut assignments = Vec::new();
    let mut trace_steps: Vec<(u32, BTreeMap<String, String>)> = Vec::new();

    for line in output.lines() {
        let trimmed = line.trim();
        if !trimmed.contains("define-fun") {
            continue;
        }

        if let Some((name, value)) = parse_bmc_define_fun(trimmed) {
            // Check if this is a step-indexed variable (e.g., "x_step_3")
            if let Some((base_name, step)) = extract_step_index(&name) {
                // Add to trace (using string representation for BTreeMap)
                let step_entry = trace_steps.iter_mut().find(|(s, _)| *s == step);
                if let Some((_, assigns)) = step_entry {
                    assigns.insert(base_name, value.to_string());
                } else {
                    let mut map = BTreeMap::new();
                    map.insert(base_name, value.to_string());
                    trace_steps.push((step, map));
                }
            }
            assignments.push((name, value));
        }
    }

    if assignments.is_empty() {
        return None;
    }

    // Sort assignments by name for deterministic output
    assignments.sort_by(|a, b| a.0.cmp(&b.0));

    // Build trace if we found step-indexed variables
    let trace = if trace_steps.len() > 1 {
        trace_steps.sort_by_key(|(step, _)| *step);
        let steps: Vec<TraceStep> = trace_steps
            .into_iter()
            .map(|(step, assigns)| {
                TraceStep {
                    step,
                    assignments: assigns,
                    program_point: None,
                }
            })
            .collect();
        Some(CounterexampleTrace::new(steps))
    } else {
        None
    };

    match trace {
        Some(t) => Some(Counterexample::with_trace(assignments, t)),
        None => Some(Counterexample::new(assignments)),
    }
}

/// Parse a single `(define-fun name () Sort value)` line from BMC output.
///
/// Reuses the same parsing logic as `smtlib_backend::parse_solver_output`
/// but returns the raw name/value pair for counterexample assembly.
fn parse_bmc_define_fun(line: &str) -> Option<(String, CounterexampleValue)> {
    let content = line.trim().trim_start_matches('(');
    let rest = content.strip_prefix("define-fun ")?;

    let name_end = rest.find(|c: char| c.is_whitespace())?;
    let name = rest[..name_end].to_string();
    let rest = rest[name_end..].trim();

    let rest = rest.strip_prefix("()")?.trim();

    let (sort_str, rest) = if rest.starts_with('(') {
        let depth = find_matching_paren(rest)?;
        (&rest[..=depth], rest[depth + 1..].trim())
    } else {
        let end = rest.find(|c: char| c.is_whitespace())?;
        (&rest[..end], rest[end..].trim())
    };

    let value_str = rest.trim_end_matches(')').trim();
    let value = parse_bmc_model_value(sort_str, value_str)?;

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
fn parse_bmc_model_value(sort_str: &str, value_str: &str) -> Option<CounterexampleValue> {
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

    if sort_str.contains("BitVec") {
        return parse_bv_value(value_str);
    }

    None
}

/// Parse an integer value, handling SMT-LIB2 negation syntax `(- N)`.
fn parse_int_value(s: &str) -> Option<CounterexampleValue> {
    let s = s.trim();
    if s.starts_with("(-") || s.starts_with("(- ") {
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

/// tRust #359: Extract step index from a step-indexed variable name.
///
/// Variable names like `x_step_3` are common in BMC unrollings.
/// Returns `(base_name, step_index)` if the pattern matches.
fn extract_step_index(name: &str) -> Option<(String, u32)> {
    let parts: Vec<&str> = name.rsplitn(2, "_step_").collect();
    if parts.len() == 2 {
        let step: u32 = parts[0].parse().ok()?;
        Some((parts[1].to_string(), step))
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::portfolio::{PortfolioLane, PortfolioStrategy, race};

    // ---------------------------------------------------------------------------
    // Basic backend properties
    // ---------------------------------------------------------------------------

    #[test]
    fn test_zani_backend_name_and_role() {
        let backend = ZaniBackend::new();
        assert_eq!(backend.name(), "zani");
        assert_eq!(backend.role(), BackendRole::BoundedModelChecker);
    }

    #[test]
    fn test_zani_handles_l0_safety_only() {
        let backend = ZaniBackend::new();
        let l0 = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "f".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        };
        let l1 = VerificationCondition {
            kind: VcKind::Postcondition,
            function: "f".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        };
        let l0_overflow = VerificationCondition {
            kind: VcKind::ArithmeticOverflow {
                op: BinOp::Add,
                operand_tys: (Ty::usize(), Ty::usize()),
            },
            function: "g".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
        };

        assert!(backend.can_handle(&l0));
        assert!(!backend.can_handle(&l1));
        assert!(backend.can_handle(&l0_overflow));
    }

    #[test]
    fn test_zani_returns_unknown_when_binary_not_found() {
        // Without ZANI_PATH set and zani not on PATH, verify returns Unknown
        let backend = ZaniBackend::with_solver_path("/nonexistent/path/zani");
        let vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "f".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        };

        let result = backend.verify(&vc);
        assert!(matches!(result, VerificationResult::Unknown { .. }));
        assert_eq!(result.solver_name(), "zani");
        if let VerificationResult::Unknown { reason, .. } = &result {
            assert!(reason.contains("failed to spawn zani"));
        }
    }

    #[test]
    fn test_zani_builder_methods() {
        let backend = ZaniBackend::with_solver_path("/usr/local/bin/zani")
            .with_timeout(60_000)
            .with_bmc_depth(200)
            .with_adaptive_depth(true);
        assert_eq!(backend.solver_path.as_deref(), Some("/usr/local/bin/zani"));
        assert_eq!(backend.timeout_ms, 60_000);
        assert_eq!(backend.bmc_depth, 200);
        assert!(backend.adaptive_depth);
    }

    #[test]
    fn test_zani_default_construction() {
        let backend = ZaniBackend::default();
        assert_eq!(backend.timeout_ms, DEFAULT_TIMEOUT_MS);
        assert_eq!(backend.bmc_depth, DEFAULT_BMC_DEPTH);
        assert!(backend.solver_path.is_none());
        assert!(!backend.adaptive_depth);
    }

    // ---------------------------------------------------------------------------
    // Script generation
    // ---------------------------------------------------------------------------

    #[test]
    fn test_generate_bmc_script_includes_options() {
        let formula = Formula::Eq(Box::new(Formula::Int(2)), Box::new(Formula::Int(0)));
        let script = generate_bmc_script(&formula, 50);

        assert!(script.contains("; zani BMC configuration (depth=50)"));
        assert!(script.contains("(set-option :produce-models true)"));
        assert!(script.contains("(set-option :bmc-depth 50)"));
        // Should still contain the base SMT-LIB2 script
        assert!(script.contains("(set-logic QF_LIA)"));
        assert!(script.contains("(assert (= 2 0))"));
        assert!(script.contains("(check-sat)"));
        assert!(script.contains("(get-model)"));
    }

    #[test]
    fn test_generate_bmc_script_with_variables() {
        let formula = Formula::Lt(
            Box::new(Formula::Var("x".to_string(), Sort::Int)),
            Box::new(Formula::Int(10)),
        );
        let script = generate_bmc_script(&formula, 100);

        assert!(script.contains("(declare-const x Int)"));
        assert!(script.contains("(assert (< x 10))"));
        assert!(script.contains("(set-option :bmc-depth 100)"));
    }

    // ---------------------------------------------------------------------------
    // Result attribution
    // ---------------------------------------------------------------------------

    #[test]
    fn test_attribute_to_zani_proved() {
        let mut result = VerificationResult::Proved {
            solver: "z4-smtlib".to_string(),
            time_ms: 42,
            strength: ProofStrength::smt_unsat(), proof_certificate: None,
                solver_warnings: None, };
        attribute_to_zani(&mut result, 100);

        assert_eq!(result.solver_name(), "zani");
        if let VerificationResult::Proved { strength, time_ms, .. } = &result {
            assert_eq!(*strength, ProofStrength::bounded(100));
            assert_eq!(*time_ms, 42);
        } else {
            panic!("expected Proved");
        }
    }

    #[test]
    fn test_attribute_to_zani_failed() {
        let cex = Counterexample::new(vec![
            ("x".to_string(), CounterexampleValue::Uint(42)),
        ]);
        let mut result = VerificationResult::Failed {
            solver: "z4-smtlib".to_string(),
            time_ms: 10,
            counterexample: Some(cex),
        };
        attribute_to_zani(&mut result, 50);

        assert_eq!(result.solver_name(), "zani");
        if let VerificationResult::Failed { counterexample: Some(cex), .. } = &result {
            assert_eq!(cex.assignments.len(), 1);
            assert_eq!(cex.assignments[0].0, "x");
        } else {
            panic!("expected Failed with counterexample");
        }
    }

    #[test]
    fn test_attribute_to_zani_unknown() {
        let mut result = VerificationResult::Unknown {
            solver: "z4-smtlib".to_string(),
            time_ms: 5,
            reason: "solver returned unknown".to_string(),
        };
        attribute_to_zani(&mut result, 100);

        assert_eq!(result.solver_name(), "zani");
    }

    #[test]
    fn test_attribute_to_zani_timeout() {
        let mut result = VerificationResult::Timeout {
            solver: "z4-smtlib".to_string(),
            timeout_ms: 30_000,
        };
        attribute_to_zani(&mut result, 100);

        assert_eq!(result.solver_name(), "zani");
    }

    // ---------------------------------------------------------------------------
    // Mock zani response parsing (counterexample extraction)
    // ---------------------------------------------------------------------------

    #[test]
    fn test_zani_counterexample_parsing_sat_with_model() {
        // Simulate zani output: SAT with model
        let output = "sat\n(model\n  (define-fun divisor () Int 0)\n)\n";
        let mut result = parse_solver_output(output, 15, vec![]);
        attribute_to_zani(&mut result, 100);

        assert!(result.is_failed());
        assert_eq!(result.solver_name(), "zani");
        if let VerificationResult::Failed { counterexample: Some(cex), .. } = &result {
            assert_eq!(cex.assignments.len(), 1);
            assert_eq!(cex.assignments[0].0, "divisor");
            assert!(matches!(cex.assignments[0].1, CounterexampleValue::Uint(0)));
        } else {
            panic!("expected Failed with counterexample");
        }
    }

    #[test]
    fn test_zani_counterexample_parsing_unsat() {
        // Simulate zani output: UNSAT (property holds within BMC depth)
        let output = "unsat\n";
        let mut result = parse_solver_output(output, 8, vec![]);
        attribute_to_zani(&mut result, 50);

        assert!(result.is_proved());
        assert_eq!(result.solver_name(), "zani");
        if let VerificationResult::Proved { strength, .. } = &result {
            assert_eq!(*strength, ProofStrength::bounded(50));
        } else {
            panic!("expected Proved");
        }
    }

    #[test]
    fn test_zani_counterexample_parsing_multi_var_model() {
        // Simulate zani output with multiple counterexample variables
        let output = "sat\n(model\n  (define-fun a () Int 18446744073709551615)\n  (define-fun b () Int 1)\n)\n";
        let mut result = parse_solver_output(output, 20, vec![]);
        attribute_to_zani(&mut result, 100);

        assert!(result.is_failed());
        if let VerificationResult::Failed { counterexample: Some(cex), .. } = &result {
            assert_eq!(cex.assignments.len(), 2);
            // Sorted by name
            assert_eq!(cex.assignments[0].0, "a");
            assert_eq!(cex.assignments[1].0, "b");
        } else {
            panic!("expected Failed with counterexample");
        }
    }

    #[test]
    fn test_zani_counterexample_parsing_bitvec_model() {
        // Simulate zani output with bitvector counterexample
        let output = "sat\n(model\n  (define-fun x () (_ BitVec 32) #x0000000a)\n)\n";
        let mut result = parse_solver_output(output, 5, vec![]);
        attribute_to_zani(&mut result, 100);

        assert!(result.is_failed());
        if let VerificationResult::Failed { counterexample: Some(cex), .. } = &result {
            assert_eq!(cex.assignments.len(), 1);
            assert_eq!(cex.assignments[0].0, "x");
            assert!(matches!(cex.assignments[0].1, CounterexampleValue::Uint(10)));
        } else {
            panic!("expected Failed with counterexample");
        }
    }

    // ---------------------------------------------------------------------------
    // Portfolio integration
    // ---------------------------------------------------------------------------

    #[test]
    fn test_zani_portfolio_integration_as_bmc_lane() {
        // Test that ZaniBackend can be used as a BMC lane in the portfolio racer
        use std::sync::Arc;

        let zani: Arc<dyn VerificationBackend> = Arc::new(ZaniBackend::with_solver_path(
            "/nonexistent/zani",
        ));

        let vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "test_fn".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        };

        let lanes = vec![PortfolioLane {
            strategy: PortfolioStrategy::Bmc,
            backend: zani,
        }];

        let result = race(&vc, lanes).expect("should get a result");
        assert_eq!(result.winning_strategy, PortfolioStrategy::Bmc);
        // Since zani binary doesn't exist, we get Unknown
        assert!(matches!(result.result, VerificationResult::Unknown { .. }));
        assert_eq!(result.result.solver_name(), "zani");
        assert_eq!(result.total_lanes, 1);
    }

    // ---------------------------------------------------------------------------
    // Router integration
    // ---------------------------------------------------------------------------

    #[test]
    fn test_zani_in_router_backend_plan() {
        use crate::Router;
        use crate::mock_backend::MockBackend;

        let router = Router::with_backends(vec![
            Box::new(MockBackend),
            Box::new(ZaniBackend::new()),
        ]);

        let l0_vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "f".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
        };

        let plan = router.backend_plan(&l0_vc);
        // For L0Safety, both mock (General) and zani (BMC) can handle.
        // BMC ranks higher than General for L0Safety.
        let zani_entry = plan.iter().find(|b| b.name == "zani");
        assert!(zani_entry.is_some());
        let zani_entry = zani_entry.expect("zani should be in plan");
        assert!(zani_entry.can_handle);
        assert_eq!(zani_entry.role, BackendRole::BoundedModelChecker);
    }

    #[test]
    fn test_zani_does_not_handle_l1_or_l2() {
        let backend = ZaniBackend::new();

        let l1_vc = VerificationCondition {
            kind: VcKind::Precondition { callee: "callee".into() },
            function: "f".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        };
        let l2_vc = VerificationCondition {
            kind: VcKind::Temporal { property: "eventually done".into() },
            function: "f".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        };

        assert!(!backend.can_handle(&l1_vc));
        assert!(!backend.can_handle(&l2_vc));
    }

    // -- #193 ownership axiom rejection tests ----------------------------

    #[test]
    fn test_zani_rejects_ownership_vc() {
        // tRust: #193 Zani should not handle VCs tagged as ownership VCs.
        let backend = ZaniBackend::new();
        let ownership_vc = VerificationCondition {
            kind: VcKind::Assertion {
                message: "[memory:region] non-aliasing: region_0 vs region_1".to_string(),
            },
            function: "f".into(),
            location: SourceSpan::default(),
            formula: Formula::Eq(
                Box::new(Formula::Var("region_0_base".to_string(), Sort::Int)),
                Box::new(Formula::Var("region_1_base".to_string(), Sort::Int)),
            ),
            contract_metadata: None,
        };
        assert!(
            !backend.can_handle(&ownership_vc),
            "zani must reject ownership VCs -- certus handles these"
        );
    }

    #[test]
    fn test_zani_rejects_l0_vc_with_region_vars() {
        // tRust: #193 Even L0Safety VCs should be rejected if their formula
        // contains region/provenance variables that zani cannot interpret.
        let backend = ZaniBackend::new();
        let vc_with_regions = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "f".into(),
            location: SourceSpan::default(),
            formula: Formula::Eq(
                Box::new(Formula::Var("region_0_base".to_string(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            contract_metadata: None,
        };
        assert!(
            !backend.can_handle(&vc_with_regions),
            "zani must reject L0 VCs with region variables"
        );
    }

    #[test]
    fn test_zani_rejects_vc_with_provenance_vars() {
        // tRust: #193 VCs with provenance_ variables are ownership-class.
        let backend = ZaniBackend::new();
        let vc_with_provenance = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "f".into(),
            location: SourceSpan::default(),
            formula: Formula::Var("provenance_tag_0".to_string(), Sort::Int),
            contract_metadata: None,
        };
        assert!(
            !backend.can_handle(&vc_with_provenance),
            "zani must reject VCs with provenance variables"
        );
    }

    #[test]
    fn test_zani_still_handles_plain_l0_safety() {
        // tRust: #193 Plain L0Safety VCs without region/provenance vars should
        // still be handled by zani.
        let backend = ZaniBackend::new();
        let plain_vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "f".into(),
            location: SourceSpan::default(),
            formula: Formula::Eq(
                Box::new(Formula::Var("divisor".to_string(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            contract_metadata: None,
        };
        assert!(
            backend.can_handle(&plain_vc),
            "zani should still handle plain L0Safety VCs"
        );
    }

    // ---------------------------------------------------------------------------
    // #359: ZaniBmcOutcome tests
    // ---------------------------------------------------------------------------

    #[test]
    fn test_bmc_outcome_proved_bounded_to_verification_result() {
        let outcome = ZaniBmcOutcome::ProvedBounded { depth: 100, time_ms: 42 };
        let result = outcome.to_verification_result();

        assert!(result.is_proved());
        assert_eq!(result.solver_name(), "zani");
        assert_eq!(result.time_ms(), 42);
        if let VerificationResult::Proved { strength, .. } = &result {
            assert_eq!(*strength, ProofStrength::bounded(100));
            assert!(strength.is_bounded());
            assert_eq!(strength.bounded_depth(), Some(100));
        } else {
            panic!("expected Proved");
        }
    }

    #[test]
    fn test_bmc_outcome_counterexample_to_verification_result() {
        let cex = Counterexample::new(vec![
            ("x".to_string(), CounterexampleValue::Uint(0)),
            ("y".to_string(), CounterexampleValue::Int(-5)),
        ]);
        let outcome = ZaniBmcOutcome::CounterexampleFound {
            counterexample: cex,
            time_ms: 15,
        };
        let result = outcome.to_verification_result();

        assert!(result.is_failed());
        assert_eq!(result.solver_name(), "zani");
        if let VerificationResult::Failed { counterexample: Some(cex), .. } = &result {
            assert_eq!(cex.assignments.len(), 2);
            assert_eq!(cex.assignments[0].0, "x");
            assert_eq!(cex.assignments[1].0, "y");
        } else {
            panic!("expected Failed with counterexample");
        }
    }

    #[test]
    fn test_bmc_outcome_bound_exhausted_to_verification_result() {
        let outcome = ZaniBmcOutcome::BoundExhausted { depth: 500, time_ms: 30_000 };
        let result = outcome.to_verification_result();

        assert!(matches!(result, VerificationResult::Unknown { .. }));
        assert_eq!(result.solver_name(), "zani");
        if let VerificationResult::Unknown { reason, .. } = &result {
            assert!(reason.contains("BMC bound exhausted at depth 500"));
            assert!(reason.contains("no counterexample found"));
        } else {
            panic!("expected Unknown");
        }
    }

    #[test]
    fn test_bmc_outcome_timeout_to_verification_result() {
        let outcome = ZaniBmcOutcome::Timeout { timeout_ms: 30_000 };
        let result = outcome.to_verification_result();

        assert!(matches!(result, VerificationResult::Timeout { .. }));
        assert_eq!(result.solver_name(), "zani");
        assert_eq!(result.time_ms(), 30_000);
    }

    #[test]
    fn test_bmc_outcome_error_to_verification_result() {
        let outcome = ZaniBmcOutcome::Error {
            reason: "internal zani error".to_string(),
            time_ms: 5,
        };
        let result = outcome.to_verification_result();

        assert!(matches!(result, VerificationResult::Unknown { .. }));
        assert_eq!(result.solver_name(), "zani");
        if let VerificationResult::Unknown { reason, .. } = &result {
            assert_eq!(*reason, "internal zani error");
        } else {
            panic!("expected Unknown");
        }
    }

    // ---------------------------------------------------------------------------
    // #359: classify_bmc_output tests with mock responses
    // ---------------------------------------------------------------------------

    #[test]
    fn test_classify_bmc_output_unsat() {
        // Mock zani UNSAT response: property proved within depth
        let output = "unsat\n";
        let outcome = classify_bmc_output(output, 10, 100);
        if let ZaniBmcOutcome::ProvedBounded { depth, time_ms } = &outcome {
            assert_eq!(*depth, 100);
            assert_eq!(*time_ms, 10);
        } else {
            panic!("expected ProvedBounded, got {outcome:?}");
        }
    }

    #[test]
    fn test_classify_bmc_output_sat_with_model() {
        // Mock zani SAT response: counterexample found
        let output = "sat\n(model\n  (define-fun x () Int 42)\n  (define-fun y () Int 0)\n)\n";
        let outcome = classify_bmc_output(output, 5, 50);
        if let ZaniBmcOutcome::CounterexampleFound { counterexample, time_ms } = &outcome {
            assert_eq!(*time_ms, 5);
            assert_eq!(counterexample.assignments.len(), 2);
            assert_eq!(counterexample.assignments[0].0, "x");
            assert_eq!(counterexample.assignments[1].0, "y");
        } else {
            panic!("expected CounterexampleFound, got {outcome:?}");
        }
    }

    #[test]
    fn test_classify_bmc_output_sat_no_model() {
        // Mock zani SAT response without model (rare but possible)
        let output = "sat\n";
        let outcome = classify_bmc_output(output, 3, 50);
        if let ZaniBmcOutcome::CounterexampleFound { counterexample, .. } = &outcome {
            assert!(counterexample.assignments.is_empty());
        } else {
            panic!("expected CounterexampleFound, got {outcome:?}");
        }
    }

    #[test]
    fn test_classify_bmc_output_unknown_bound_exhausted() {
        // Mock zani "unknown" response indicating bound exhaustion
        let output = "unknown\nbound limit reached\n";
        let outcome = classify_bmc_output(output, 30_000, 500);
        if let ZaniBmcOutcome::BoundExhausted { depth, time_ms } = &outcome {
            assert_eq!(*depth, 500);
            assert_eq!(*time_ms, 30_000);
        } else {
            panic!("expected BoundExhausted, got {outcome:?}");
        }
    }

    #[test]
    fn test_classify_bmc_output_unknown_at_max_depth() {
        // Unknown at MAX_BMC_DEPTH is treated as bound exhaustion
        let output = "unknown\n";
        let outcome = classify_bmc_output(output, 50_000, MAX_BMC_DEPTH);
        if let ZaniBmcOutcome::BoundExhausted { depth, time_ms } = &outcome {
            assert_eq!(*depth, MAX_BMC_DEPTH);
            assert_eq!(*time_ms, 50_000);
        } else {
            panic!("expected BoundExhausted, got {outcome:?}");
        }
    }

    #[test]
    fn test_classify_bmc_output_unknown_depth_message() {
        // Unknown with depth-related message
        let output = "unknown\nresource limit: depth exceeded\n";
        let outcome = classify_bmc_output(output, 1000, 200);
        if let ZaniBmcOutcome::BoundExhausted { depth, time_ms } = &outcome {
            assert_eq!(*depth, 200);
            assert_eq!(*time_ms, 1000);
        } else {
            panic!("expected BoundExhausted, got {outcome:?}");
        }
    }

    #[test]
    fn test_classify_bmc_output_unknown_generic() {
        // Unknown without bound-related keywords at normal depth
        let output = "unknown\n";
        let outcome = classify_bmc_output(output, 500, 50);
        if let ZaniBmcOutcome::Error { reason, time_ms } = &outcome {
            assert_eq!(*time_ms, 500);
            assert!(reason.contains("unknown"));
        } else {
            panic!("expected Error for generic unknown, got {outcome:?}");
        }
    }

    #[test]
    fn test_classify_bmc_output_unexpected() {
        // Unexpected output (error from solver)
        let output = "(error \"bad logic\")\n";
        let outcome = classify_bmc_output(output, 1, 50);
        if let ZaniBmcOutcome::Error { reason, .. } = &outcome {
            assert!(reason.contains("unexpected zani output"));
        } else {
            panic!("expected Error for unexpected output, got {outcome:?}");
        }
    }

    #[test]
    fn test_classify_bmc_output_sat_with_negative_values() {
        // Mock zani SAT with negative integer counterexample
        let output = "sat\n(model\n  (define-fun idx () Int (- 1))\n)\n";
        let outcome = classify_bmc_output(output, 8, 100);
        if let ZaniBmcOutcome::CounterexampleFound { counterexample, .. } = &outcome {
            assert_eq!(counterexample.assignments.len(), 1);
            assert_eq!(counterexample.assignments[0].0, "idx");
            assert!(matches!(counterexample.assignments[0].1, CounterexampleValue::Int(-1)));
        } else {
            panic!("expected CounterexampleFound, got {outcome:?}");
        }
    }

    #[test]
    fn test_classify_bmc_output_sat_with_bitvector() {
        // Mock zani SAT with bitvector counterexample
        let output = "sat\n(model\n  (define-fun ptr () (_ BitVec 64) #xdeadbeef00000000)\n)\n";
        let outcome = classify_bmc_output(output, 12, 100);
        if let ZaniBmcOutcome::CounterexampleFound { counterexample, .. } = &outcome {
            assert_eq!(counterexample.assignments.len(), 1);
            assert_eq!(counterexample.assignments[0].0, "ptr");
            if let CounterexampleValue::Uint(v) = &counterexample.assignments[0].1 {
                assert_eq!(*v, 0xdeadbeef00000000u128);
            } else {
                panic!("expected Uint value");
            }
        } else {
            panic!("expected CounterexampleFound, got {outcome:?}");
        }
    }

    #[test]
    fn test_classify_bmc_output_sat_with_bool_counterexample() {
        // Mock zani SAT with boolean counterexample
        let output = "sat\n(model\n  (define-fun cond () Bool false)\n)\n";
        let outcome = classify_bmc_output(output, 3, 50);
        if let ZaniBmcOutcome::CounterexampleFound { counterexample, .. } = &outcome {
            assert_eq!(counterexample.assignments.len(), 1);
            assert_eq!(counterexample.assignments[0].0, "cond");
            assert!(matches!(counterexample.assignments[0].1, CounterexampleValue::Bool(false)));
        } else {
            panic!("expected CounterexampleFound, got {outcome:?}");
        }
    }

    // ---------------------------------------------------------------------------
    // #359: Counterexample trace extraction tests
    // ---------------------------------------------------------------------------

    #[test]
    fn test_extract_step_index_valid() {
        let (base, step) = extract_step_index("x_step_0").expect("should parse");
        assert_eq!(base, "x");
        assert_eq!(step, 0);

        let (base, step) = extract_step_index("counter_step_3").expect("should parse");
        assert_eq!(base, "counter");
        assert_eq!(step, 3);
    }

    #[test]
    fn test_extract_step_index_invalid() {
        assert!(extract_step_index("x").is_none());
        assert!(extract_step_index("x_step_").is_none());
        assert!(extract_step_index("x_step_abc").is_none());
    }

    #[test]
    fn test_parse_bmc_counterexample_with_trace() {
        // Mock zani output with step-indexed variables
        let output = "sat\n\
            (model\n\
              (define-fun x_step_0 () Int 10)\n\
              (define-fun x_step_1 () Int 5)\n\
              (define-fun x_step_2 () Int 0)\n\
              (define-fun bound () Int 10)\n\
            )\n";

        let cex = parse_bmc_counterexample(output).expect("should parse");
        assert_eq!(cex.assignments.len(), 4);

        // Should have a trace with 3 steps
        let trace = cex.trace.as_ref().expect("should have trace");
        assert_eq!(trace.len(), 3);
        assert_eq!(trace.steps[0].step, 0);
        assert_eq!(trace.steps[1].step, 1);
        assert_eq!(trace.steps[2].step, 2);
    }

    #[test]
    fn test_parse_bmc_counterexample_no_trace() {
        // Regular variables without step indexing -- no trace
        let output = "sat\n(model\n  (define-fun a () Int 5)\n  (define-fun b () Int 7)\n)\n";
        let cex = parse_bmc_counterexample(output).expect("should parse");
        assert_eq!(cex.assignments.len(), 2);
        assert!(cex.trace.is_none());
    }

    #[test]
    fn test_parse_bmc_counterexample_single_step_no_trace() {
        // Only one step-indexed variable -- not enough for a trace
        let output = "sat\n(model\n  (define-fun x_step_0 () Int 10)\n)\n";
        let cex = parse_bmc_counterexample(output).expect("should parse");
        assert_eq!(cex.assignments.len(), 1);
        // Single step does not produce a trace (need > 1 steps)
        assert!(cex.trace.is_none());
    }

    // ---------------------------------------------------------------------------
    // #359: QueryClass-based routing tests
    // ---------------------------------------------------------------------------

    #[test]
    fn test_is_suitable_for_zani_l0_linear() {
        let vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "f".into(),
            location: SourceSpan::default(),
            formula: Formula::Eq(
                Box::new(Formula::Var("x".to_string(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            contract_metadata: None,
        };
        assert!(is_suitable_for_zani(&vc), "L0 linear VC should be suitable for zani");
    }

    #[test]
    fn test_is_suitable_for_zani_l0_bitvector() {
        let vc = VerificationCondition {
            kind: VcKind::ArithmeticOverflow {
                op: BinOp::Add,
                operand_tys: (Ty::usize(), Ty::usize()),
            },
            function: "f".into(),
            location: SourceSpan::default(),
            formula: Formula::BvAdd(
                Box::new(Formula::Var("a".to_string(), Sort::BitVec(32))),
                Box::new(Formula::Var("b".to_string(), Sort::BitVec(32))),
                32,
            ),
            contract_metadata: None,
        };
        assert!(is_suitable_for_zani(&vc), "L0 BV VC should be suitable for zani");
    }

    #[test]
    fn test_is_not_suitable_for_zani_l1() {
        let vc = VerificationCondition {
            kind: VcKind::Postcondition,
            function: "f".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        };
        assert!(!is_suitable_for_zani(&vc), "L1 VC should not be suitable for zani");
    }

    #[test]
    fn test_is_not_suitable_for_zani_ownership() {
        let vc = VerificationCondition {
            kind: VcKind::Assertion {
                message: "[memory:region] non-aliasing".to_string(),
            },
            function: "f".into(),
            location: SourceSpan::default(),
            formula: Formula::Var("region_0_base".to_string(), Sort::Int),
            contract_metadata: None,
        };
        assert!(!is_suitable_for_zani(&vc), "ownership VC should not be suitable for zani");
    }

    #[test]
    fn test_classify_for_zani_small_formula() {
        let vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "f".into(),
            location: SourceSpan::default(),
            formula: Formula::Eq(
                Box::new(Formula::Var("x".to_string(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            contract_metadata: None,
        };

        let (suitable, depth) = classify_for_zani(&vc);
        assert!(suitable);
        // Small formula (3 nodes: Eq, Var, Int) => 50 depth
        assert_eq!(depth, 50);
    }

    #[test]
    fn test_classify_for_zani_unsuitable_vc() {
        let vc = VerificationCondition {
            kind: VcKind::Postcondition,
            function: "f".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
        };

        let (suitable, depth) = classify_for_zani(&vc);
        assert!(!suitable);
        assert_eq!(depth, 0);
    }

    // ---------------------------------------------------------------------------
    // #359: Adaptive depth selection tests
    // ---------------------------------------------------------------------------

    #[test]
    fn test_effective_depth_non_adaptive() {
        let backend = ZaniBackend::new().with_bmc_depth(200);
        let vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "f".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
        };
        assert_eq!(backend.effective_depth(&vc), 200);
    }

    #[test]
    fn test_effective_depth_adaptive_small() {
        let backend = ZaniBackend::new()
            .with_bmc_depth(500)
            .with_adaptive_depth(true);
        let vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "f".into(),
            location: SourceSpan::default(),
            formula: Formula::Eq(
                Box::new(Formula::Var("x".to_string(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            contract_metadata: None,
        };
        // Small formula => recommended 50, ceiling is 500 => effective 50
        assert_eq!(backend.effective_depth(&vc), 50);
    }

    #[test]
    fn test_effective_depth_adaptive_clamped_to_ceiling() {
        let backend = ZaniBackend::new()
            .with_bmc_depth(30)  // Low ceiling
            .with_adaptive_depth(true);
        let vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "f".into(),
            location: SourceSpan::default(),
            formula: Formula::Eq(
                Box::new(Formula::Var("x".to_string(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            contract_metadata: None,
        };
        // Recommended 50, but ceiling is 30 => effective 30
        assert_eq!(backend.effective_depth(&vc), 30);
    }

    // ---------------------------------------------------------------------------
    // #359: analyze_bmc structured outcome tests
    // ---------------------------------------------------------------------------

    #[test]
    fn test_analyze_bmc_returns_error_when_no_binary() {
        let backend = ZaniBackend::with_solver_path("/definitely/not/zani");
        let vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "f".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
        };

        let outcome = backend.analyze_bmc(&vc);
        if let ZaniBmcOutcome::Error { reason, .. } = &outcome {
            assert!(reason.contains("failed to spawn zani") || reason.contains("not found"));
        } else {
            // May get error from spawn attempt
            assert!(
                matches!(outcome, ZaniBmcOutcome::Error { .. }),
                "expected Error when binary not found, got {outcome:?}"
            );
        }
    }

    // ---------------------------------------------------------------------------
    // #359: Counterexample multi-step model parsing with mixed types
    // ---------------------------------------------------------------------------

    #[test]
    fn test_parse_bmc_counterexample_mixed_types() {
        let output = "sat\n\
            (model\n\
              (define-fun x () Int 42)\n\
              (define-fun flag () Bool true)\n\
              (define-fun bits () (_ BitVec 8) #b11111111)\n\
            )\n";

        let cex = parse_bmc_counterexample(output).expect("should parse mixed types");
        assert_eq!(cex.assignments.len(), 3);

        // Sorted by name: bits, flag, x
        assert_eq!(cex.assignments[0].0, "bits");
        assert!(matches!(cex.assignments[0].1, CounterexampleValue::Uint(255)));
        assert_eq!(cex.assignments[1].0, "flag");
        assert!(matches!(cex.assignments[1].1, CounterexampleValue::Bool(true)));
        assert_eq!(cex.assignments[2].0, "x");
        assert!(matches!(cex.assignments[2].1, CounterexampleValue::Uint(42)));
    }

    #[test]
    fn test_parse_bmc_counterexample_empty_model() {
        // No define-fun entries in model
        let output = "sat\n(model\n)\n";
        let result = parse_bmc_counterexample(output);
        assert!(result.is_none(), "empty model should return None");
    }

    #[test]
    fn test_classify_bmc_output_sat_large_model() {
        // Mock large counterexample with many variables
        let mut model = String::from("sat\n(model\n");
        for i in 0..20 {
            let _ = write!(model, "  (define-fun v{i} () Int {i})\n");
        }
        model.push_str(")\n");

        let outcome = classify_bmc_output(&model, 100, 200);
        if let ZaniBmcOutcome::CounterexampleFound { counterexample, .. } = &outcome {
            assert_eq!(counterexample.assignments.len(), 20);
        } else {
            panic!("expected CounterexampleFound with 20 vars, got {outcome:?}");
        }
    }

    #[test]
    fn test_classify_bmc_output_unknown_resource_limit() {
        // zani reports resource limit (memory, time)
        let output = "unknown\nresource limit exceeded\n";
        let outcome = classify_bmc_output(output, 5000, 100);
        if let ZaniBmcOutcome::BoundExhausted { depth, time_ms } = &outcome {
            assert_eq!(*depth, 100);
            assert_eq!(*time_ms, 5000);
        } else {
            panic!("expected BoundExhausted, got {outcome:?}");
        }
    }
}
