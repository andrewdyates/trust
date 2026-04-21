// trust-zani-lib subprocess backend
//
// Phase 1 implementation: delegates to zani CLI via subprocess.
// Will be replaced by direct in-process integration in Phase 2.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

//! Subprocess-based zani backend.
//!
//! Invokes the zani bounded model checker as a subprocess, communicating
//! via SMT-LIB2 over stdin/stdout. This is the Phase 1 implementation;
//! Phase 2 (trust-build feature) will call zani's codegen_z4 in-process.

use std::collections::BTreeMap;
use std::io::Write as _;
use std::process::{Command, Stdio};
use std::sync::OnceLock;
use std::time::Instant;

use crate::config::{DiagConfig, ZaniConfig};
use crate::error::ZaniLibError;
use crate::result::{
    DiagLevel, DiagnosticMessage, TraceStep, TypedCounterexample, TypedValue, Verdict,
    ViolationInfo, ZaniResult,
};

/// Cached zani binary path, probed once per process.
static ZANI_PATH: OnceLock<Option<String>> = OnceLock::new();

/// Probe for the zani binary.
///
/// Priority: `ZANI_PATH` env var > `zani` on PATH.
fn probe_zani_path() -> Option<String> {
    if let Ok(path) = std::env::var("ZANI_PATH")
        && std::path::Path::new(&path).exists() {
            return Some(path);
        }

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

/// Subprocess-based zani backend.
///
/// Communicates with zani via SMT-LIB2 over stdin/stdout. This is the
/// Phase 1 implementation that will be superseded by direct in-process
/// integration when the `trust-build` feature is enabled.
pub struct SubprocessBackend {
    /// Resolved solver path.
    solver_path: Option<String>,
    /// Extra solver arguments.
    solver_args: Vec<String>,
    /// Timeout in milliseconds.
    timeout_ms: u64,
    /// BMC depth.
    bmc_depth: u32,
    /// Diagnostic configuration.
    diag_config: DiagConfig,
    /// Whether to produce models.
    produce_models: bool,
}

impl SubprocessBackend {
    /// Create a new subprocess backend from config.
    pub(crate) fn new(config: &ZaniConfig) -> Self {
        Self {
            solver_path: config.solver_path.clone(),
            solver_args: config.solver_args.clone(),
            timeout_ms: config.timeout_ms,
            bmc_depth: config.bmc_depth,
            diag_config: config.diagnostics.clone(),
            produce_models: config.produce_models,
        }
    }

    /// Resolve the solver path: explicit config > cached probe.
    fn resolve_path(&self) -> Result<&str, ZaniLibError> {
        if let Some(ref path) = self.solver_path {
            Ok(path.as_str())
        } else {
            cached_zani_path().map(|s| s.as_str()).ok_or_else(|| {
                ZaniLibError::BinaryNotFound {
                    reason: "set ZANI_PATH env or install zani on PATH".to_string(),
                }
            })
        }
    }

    /// Run zani on an SMT-LIB2 script and return raw stdout + stderr.
    fn run_solver(&self, script: &str) -> Result<(String, String), ZaniLibError> {
        let path = self.resolve_path()?;

        let mut child = Command::new(path)
            .args(&self.solver_args)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()?;

        if let Some(mut stdin) = child.stdin.take() {
            stdin.write_all(script.as_bytes()).map_err(|e| {
                ZaniLibError::InputError {
                    reason: e.to_string(),
                }
            })?;
        }

        let output = child.wait_with_output()?;

        let stdout = String::from_utf8_lossy(&output.stdout).to_string();
        let stderr = String::from_utf8_lossy(&output.stderr).to_string();

        Ok((stdout, stderr))
    }

    /// Verify a function using the subprocess backend.
    pub(crate) fn verify(
        &self,
        function_name: &str,
        smtlib_script: &str,
    ) -> Result<ZaniResult, ZaniLibError> {
        let start = Instant::now();

        // Generate the BMC-wrapped script
        let script = self.wrap_bmc_script(smtlib_script);

        // Run the solver
        let (stdout, stderr) = self.run_solver(&script)?;
        let elapsed = start.elapsed().as_millis() as u64;

        // Parse diagnostics from stderr
        let diagnostics = if self.diag_config == DiagConfig::Capture {
            parse_diagnostics(&stderr)
        } else {
            Vec::new()
        };

        // Check for timeout
        if elapsed >= self.timeout_ms {
            return Ok(ZaniResult {
                verdict: Verdict::Timeout,
                counterexample: None,
                proof_certificate: None,
                violations: Vec::new(),
                time_ms: elapsed,
                diagnostics,
                bmc_depth: self.bmc_depth,
                function_name: function_name.to_string(),
            });
        }

        // Parse the result
        let (verdict, counterexample, violations) = parse_solver_output(&stdout, self.bmc_depth);

        Ok(ZaniResult {
            verdict,
            counterexample,
            proof_certificate: None,
            violations,
            time_ms: elapsed,
            diagnostics,
            bmc_depth: self.bmc_depth,
            function_name: function_name.to_string(),
        })
    }

    /// Wrap an SMT-LIB2 script with BMC-specific options for zani.
    fn wrap_bmc_script(&self, base_script: &str) -> String {
        let mut script = String::with_capacity(base_script.len() + 128);
        script.push_str("; zani-lib BMC configuration\n");
        if self.produce_models {
            script.push_str("(set-option :produce-models true)\n");
        }
        script.push_str(&format!("(set-option :bmc-depth {})\n", self.bmc_depth));
        script.push_str(base_script);
        script
    }
}

/// Parse solver stdout into verdict, counterexample, and violations.
fn parse_solver_output(
    output: &str,
    bmc_depth: u32,
) -> (Verdict, Option<TypedCounterexample>, Vec<ViolationInfo>) {
    let trimmed = output.trim();

    if trimmed.starts_with("unsat") {
        return (Verdict::Proved, None, Vec::new());
    }

    if trimmed.starts_with("sat") {
        let cex = parse_counterexample(trimmed);
        let violations = Vec::new(); // Violations parsed from model in Phase 2
        return (Verdict::Failed, cex, violations);
    }

    if trimmed.starts_with("unknown") {
        let is_bound_exhausted = trimmed.contains("bound")
            || trimmed.contains("depth")
            || trimmed.contains("resource");

        let reason = if is_bound_exhausted {
            format!("BMC bound exhausted at depth {bmc_depth}")
        } else {
            "solver returned unknown".to_string()
        };

        return (Verdict::Unknown { reason }, None, Vec::new());
    }

    (
        Verdict::Unknown {
            reason: format!(
                "unexpected solver output: {}",
                &trimmed[..trimmed.len().min(200)]
            ),
        },
        None,
        Vec::new(),
    )
}

/// Parse a counterexample from solver SAT output.
fn parse_counterexample(output: &str) -> Option<TypedCounterexample> {
    let mut variables = BTreeMap::new();
    let mut trace_steps: Vec<(u32, BTreeMap<String, TypedValue>)> = Vec::new();

    for line in output.lines() {
        let trimmed = line.trim();
        if !trimmed.contains("define-fun") {
            continue;
        }

        if let Some((name, value)) = parse_define_fun(trimmed) {
            // Check for step-indexed variables (e.g., "x_step_3")
            if let Some((base_name, step)) = extract_step_index(&name) {
                let entry = trace_steps.iter_mut().find(|(s, _)| *s == step);
                if let Some((_, assigns)) = entry {
                    assigns.insert(base_name, value.clone());
                } else {
                    let mut map = BTreeMap::new();
                    map.insert(base_name, value.clone());
                    trace_steps.push((step, map));
                }
            }
            variables.insert(name, value);
        }
    }

    if variables.is_empty() {
        return None;
    }

    let trace = if trace_steps.len() > 1 {
        trace_steps.sort_by_key(|(step, _)| *step);
        Some(
            trace_steps
                .into_iter()
                .map(|(step, assignments)| TraceStep {
                    step,
                    assignments,
                    program_point: None,
                })
                .collect(),
        )
    } else {
        None
    };

    let mut cex = TypedCounterexample::new(variables);
    if let Some(trace) = trace {
        cex = cex.with_trace(trace);
    }
    Some(cex)
}

/// Parse a single `(define-fun name () Sort value)` line.
fn parse_define_fun(line: &str) -> Option<(String, TypedValue)> {
    let content = line.trim().trim_start_matches('(');
    let rest = content.strip_prefix("define-fun ")?;

    let name_end = rest.find(|c: char| c.is_whitespace())?;
    let name = rest[..name_end].to_string();
    let rest = rest[name_end..].trim();

    // Skip "()" parameter list
    let rest = rest.strip_prefix("()")?.trim();

    // Parse sort
    let (sort_str, rest) = if rest.starts_with('(') {
        let depth = find_matching_paren(rest)?;
        (&rest[..=depth], rest[depth + 1..].trim())
    } else {
        let end = rest.find(|c: char| c.is_whitespace())?;
        (&rest[..end], rest[end..].trim())
    };

    let value_str = rest.trim_end_matches(')').trim();
    let value = parse_model_value(sort_str, value_str)?;

    Some((name, value))
}

/// Find the index of the matching closing paren.
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
fn parse_model_value(sort_str: &str, value_str: &str) -> Option<TypedValue> {
    if sort_str == "Bool" {
        return match value_str {
            "true" => Some(TypedValue::Bool(true)),
            "false" => Some(TypedValue::Bool(false)),
            _ => None,
        };
    }

    if sort_str == "Int" {
        return parse_int_value(value_str);
    }

    if sort_str.contains("BitVec") {
        // Extract width from (_ BitVec N)
        let width = sort_str
            .trim_start_matches("(_ BitVec ")
            .trim_end_matches(')')
            .trim()
            .parse::<u32>()
            .unwrap_or(64);
        return parse_bv_value(value_str, width);
    }

    // Fallback: store as string
    Some(TypedValue::String(value_str.to_string()))
}

/// Parse an integer value, handling SMT-LIB2 negation syntax `(- N)`.
fn parse_int_value(s: &str) -> Option<TypedValue> {
    let s = s.trim();
    if s.starts_with("(-") || s.starts_with("(- ") {
        let inner = s
            .trim_start_matches('(')
            .trim_start_matches('-')
            .trim()
            .trim_end_matches(')');
        let n: i128 = inner.parse().ok()?;
        Some(TypedValue::Int(-n))
    } else if let Ok(n) = s.parse::<u128>() {
        Some(TypedValue::Uint(n))
    } else if let Ok(n) = s.parse::<i128>() {
        Some(TypedValue::Int(n))
    } else {
        None
    }
}

/// Parse a bitvector value like `#x0000000a` or `#b1010` or `(_ bv10 32)`.
fn parse_bv_value(s: &str, width: u32) -> Option<TypedValue> {
    let s = s.trim();
    if let Some(hex) = s.strip_prefix("#x") {
        let value = u128::from_str_radix(hex, 16).ok()?;
        Some(TypedValue::BitVec { value, width })
    } else if let Some(bin) = s.strip_prefix("#b") {
        let value = u128::from_str_radix(bin, 2).ok()?;
        Some(TypedValue::BitVec { value, width })
    } else if s.starts_with("(_ bv") {
        let inner = s.trim_start_matches("(_ bv").trim_end_matches(')');
        let parts: Vec<&str> = inner.split_whitespace().collect();
        if let Some(val_str) = parts.first() {
            let value: u128 = val_str.parse().ok()?;
            Some(TypedValue::BitVec { value, width })
        } else {
            None
        }
    } else {
        None
    }
}

/// Extract step index from a step-indexed variable name.
fn extract_step_index(name: &str) -> Option<(String, u32)> {
    let parts: Vec<&str> = name.rsplitn(2, "_step_").collect();
    if parts.len() == 2 {
        let step: u32 = parts[0].parse().ok()?;
        Some((parts[1].to_string(), step))
    } else {
        None
    }
}

/// Parse diagnostic messages from stderr.
fn parse_diagnostics(stderr: &str) -> Vec<DiagnosticMessage> {
    stderr
        .lines()
        .filter(|line| !line.trim().is_empty())
        .map(|line| {
            let (level, message) = if line.contains("error") {
                (DiagLevel::Error, line.to_string())
            } else if line.contains("warning") {
                (DiagLevel::Warning, line.to_string())
            } else {
                (DiagLevel::Note, line.to_string())
            };
            DiagnosticMessage {
                level,
                message,
                location: None,
            }
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_solver_output_unsat() {
        let (verdict, cex, violations) = parse_solver_output("unsat\n", 100);
        assert_eq!(verdict, Verdict::Proved);
        assert!(cex.is_none());
        assert!(violations.is_empty());
    }

    #[test]
    fn test_parse_solver_output_sat_with_model() {
        let output = "sat\n(model\n  (define-fun x () Int 42)\n  (define-fun y () Bool false)\n)\n";
        let (verdict, cex, _) = parse_solver_output(output, 100);
        assert_eq!(verdict, Verdict::Failed);
        let cex = cex.expect("should have counterexample");
        assert_eq!(cex.variables.len(), 2);
        assert_eq!(cex.variables["x"], TypedValue::Uint(42));
        assert_eq!(cex.variables["y"], TypedValue::Bool(false));
    }

    #[test]
    fn test_parse_solver_output_sat_no_model() {
        let (verdict, cex, _) = parse_solver_output("sat\n", 100);
        assert_eq!(verdict, Verdict::Failed);
        assert!(cex.is_none());
    }

    #[test]
    fn test_parse_solver_output_unknown_bound_exhausted() {
        let output = "unknown\nbound limit reached\n";
        let (verdict, _, _) = parse_solver_output(output, 500);
        match verdict {
            Verdict::Unknown { reason } => {
                assert!(reason.contains("BMC bound exhausted at depth 500"));
            }
            _ => panic!("expected Unknown"),
        }
    }

    #[test]
    fn test_parse_solver_output_unknown_generic() {
        let (verdict, _, _) = parse_solver_output("unknown\n", 50);
        match verdict {
            Verdict::Unknown { reason } => {
                assert_eq!(reason, "solver returned unknown");
            }
            _ => panic!("expected Unknown"),
        }
    }

    #[test]
    fn test_parse_solver_output_unexpected() {
        let (verdict, _, _) = parse_solver_output("(error \"bad logic\")\n", 50);
        assert!(matches!(verdict, Verdict::Unknown { .. }));
    }

    #[test]
    fn test_parse_counterexample_int_and_bool() {
        let output = "sat\n(model\n  (define-fun a () Int 10)\n  (define-fun b () Bool true)\n)\n";
        let cex = parse_counterexample(output).expect("should parse");
        assert_eq!(cex.variables.len(), 2);
        assert_eq!(cex.variables["a"], TypedValue::Uint(10));
        assert_eq!(cex.variables["b"], TypedValue::Bool(true));
        assert!(cex.trace.is_none());
    }

    #[test]
    fn test_parse_counterexample_negative_int() {
        let output = "sat\n(model\n  (define-fun x () Int (- 5))\n)\n";
        let cex = parse_counterexample(output).expect("should parse");
        assert_eq!(cex.variables["x"], TypedValue::Int(-5));
    }

    #[test]
    fn test_parse_counterexample_bitvector() {
        let output =
            "sat\n(model\n  (define-fun ptr () (_ BitVec 64) #xdeadbeef00000000)\n)\n";
        let cex = parse_counterexample(output).expect("should parse");
        assert_eq!(
            cex.variables["ptr"],
            TypedValue::BitVec {
                value: 0xdeadbeef00000000,
                width: 64,
            }
        );
    }

    #[test]
    fn test_parse_counterexample_binary_bitvector() {
        let output = "sat\n(model\n  (define-fun bits () (_ BitVec 8) #b11111111)\n)\n";
        let cex = parse_counterexample(output).expect("should parse");
        assert_eq!(
            cex.variables["bits"],
            TypedValue::BitVec {
                value: 255,
                width: 8,
            }
        );
    }

    #[test]
    fn test_parse_counterexample_with_trace() {
        let output = "sat\n\
            (model\n\
              (define-fun x_step_0 () Int 10)\n\
              (define-fun x_step_1 () Int 5)\n\
              (define-fun x_step_2 () Int 0)\n\
            )\n";
        let cex = parse_counterexample(output).expect("should parse");
        assert_eq!(cex.variables.len(), 3);
        let trace = cex.trace.as_ref().expect("should have trace");
        assert_eq!(trace.len(), 3);
        assert_eq!(trace[0].step, 0);
        assert_eq!(trace[1].step, 1);
        assert_eq!(trace[2].step, 2);
    }

    #[test]
    fn test_parse_counterexample_single_step_no_trace() {
        let output = "sat\n(model\n  (define-fun x_step_0 () Int 10)\n)\n";
        let cex = parse_counterexample(output).expect("should parse");
        assert!(cex.trace.is_none(), "single step should not produce trace");
    }

    #[test]
    fn test_parse_counterexample_empty_model() {
        let output = "sat\n(model\n)\n";
        assert!(parse_counterexample(output).is_none());
    }

    #[test]
    fn test_extract_step_index_valid() {
        let (base, step) = extract_step_index("x_step_3").expect("should parse");
        assert_eq!(base, "x");
        assert_eq!(step, 3);
    }

    #[test]
    fn test_extract_step_index_invalid() {
        assert!(extract_step_index("x").is_none());
        assert!(extract_step_index("x_step_").is_none());
        assert!(extract_step_index("x_step_abc").is_none());
    }

    #[test]
    fn test_parse_diagnostics() {
        let stderr = "error: something failed\nwarning: check this\nnote: fyi\n";
        let diags = parse_diagnostics(stderr);
        assert_eq!(diags.len(), 3);
        assert_eq!(diags[0].level, DiagLevel::Error);
        assert_eq!(diags[1].level, DiagLevel::Warning);
        assert_eq!(diags[2].level, DiagLevel::Note);
    }

    #[test]
    fn test_zani_result_verdict_helpers() {
        let proved = ZaniResult {
            verdict: Verdict::Proved,
            counterexample: None,
            proof_certificate: None,
            violations: Vec::new(),
            time_ms: 10,
            diagnostics: Vec::new(),
            bmc_depth: 100,
            function_name: "test".to_string(),
        };
        assert!(proved.is_proved());
        assert!(!proved.is_failed());
        assert!(!proved.is_unknown());

        let failed = ZaniResult {
            verdict: Verdict::Failed,
            counterexample: None,
            proof_certificate: None,
            violations: Vec::new(),
            time_ms: 10,
            diagnostics: Vec::new(),
            bmc_depth: 100,
            function_name: "test".to_string(),
        };
        assert!(!failed.is_proved());
        assert!(failed.is_failed());

        let unknown = ZaniResult {
            verdict: Verdict::Unknown {
                reason: "test".to_string(),
            },
            counterexample: None,
            proof_certificate: None,
            violations: Vec::new(),
            time_ms: 10,
            diagnostics: Vec::new(),
            bmc_depth: 100,
            function_name: "test".to_string(),
        };
        assert!(unknown.is_unknown());
    }

    #[test]
    fn test_zani_result_to_verification_result_proved() {
        let result = ZaniResult {
            verdict: Verdict::Proved,
            counterexample: None,
            proof_certificate: None,
            violations: Vec::new(),
            time_ms: 42,
            diagnostics: Vec::new(),
            bmc_depth: 100,
            function_name: "test_fn".to_string(),
        };
        let vr = result.to_verification_result();
        assert!(vr.is_proved());
        assert_eq!(vr.solver_name(), "zani-lib");
        assert_eq!(vr.time_ms(), 42);
    }

    #[test]
    fn test_zani_result_to_verification_result_failed() {
        let mut vars = BTreeMap::new();
        vars.insert("x".to_string(), TypedValue::Uint(0));
        let result = ZaniResult {
            verdict: Verdict::Failed,
            counterexample: Some(TypedCounterexample::new(vars)),
            proof_certificate: None,
            violations: Vec::new(),
            time_ms: 15,
            diagnostics: Vec::new(),
            bmc_depth: 100,
            function_name: "test_fn".to_string(),
        };
        let vr = result.to_verification_result();
        assert!(vr.is_failed());
        assert_eq!(vr.solver_name(), "zani-lib");
    }

    #[test]
    fn test_zani_result_to_verification_result_timeout() {
        let result = ZaniResult {
            verdict: Verdict::Timeout,
            counterexample: None,
            proof_certificate: None,
            violations: Vec::new(),
            time_ms: 30_000,
            diagnostics: Vec::new(),
            bmc_depth: 100,
            function_name: "test_fn".to_string(),
        };
        let vr = result.to_verification_result();
        assert!(matches!(vr, trust_types::VerificationResult::Timeout { .. }));
    }

    #[test]
    fn test_zani_config_builder() {
        let config = ZaniConfig::new()
            .with_bmc_depth(200)
            .with_timeout(60_000)
            .with_solver_path("/usr/local/bin/zani")
            .with_diagnostics(DiagConfig::Capture)
            .with_proofs(true)
            .with_adaptive_depth(true);

        assert_eq!(config.bmc_depth, 200);
        assert_eq!(config.timeout_ms, 60_000);
        assert_eq!(config.solver_path.as_deref(), Some("/usr/local/bin/zani"));
        assert_eq!(config.diagnostics, DiagConfig::Capture);
        assert!(config.produce_proofs);
        assert!(config.adaptive_depth);
    }

    #[test]
    fn test_encoding_context_extracts_variables() {
        let script = "(declare-const x Int)\n(declare-const y Bool)\n(assert (= x 0))\n";
        let ctx = crate::result::EncodingContext::from_smtlib(
            "test_fn".to_string(),
            script.to_string(),
            100,
        );
        assert_eq!(ctx.variable_names, vec!["x", "y"]);
        assert_eq!(ctx.function_name, "test_fn");
        assert_eq!(ctx.bmc_depth, 100);
    }
}
