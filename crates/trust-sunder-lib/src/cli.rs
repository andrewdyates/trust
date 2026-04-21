// trust-sunder-lib CLI backend
//
// Phase 1 implementation: delegates to sunder CLI via subprocess.
// Will be replaced by direct in-process integration in Phase 2.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

//! Subprocess-based sunder backend.
//!
//! Invokes the sunder deductive verifier as a subprocess, passing contracts
//! via stdin/files and parsing the structured result protocol from stderr.
//! This is the Phase 1 implementation; Phase 2 (trust-build feature) will
//! call sunder's verification context in-process via `TyCtxt`.

use std::process::{Command, Stdio};
use std::sync::OnceLock;
use std::time::Instant;

use crate::backend::SunderBackend;
use crate::config::{DiagConfig, SunderConfig};
use crate::contract::ContractSet;
use crate::error::SunderLibError;
use crate::result::{
    DiagLevel, DiagnosticMessage, FunctionVerdict, LoopInvariant, SunderResult,
    VerificationCounts, Verdict,
};

/// Wire line prefix for sunder's structured result protocol.
const WIRE_PREFIX: &str = "SUNDER_RESULT:v1";

/// Cached sunder binary path, probed once per process.
static SUNDER_PATH: OnceLock<Option<String>> = OnceLock::new();

/// Probe for the sunder binary.
///
/// Priority: `SUNDER_PATH` env var > `cargo-sunder` on PATH > `sunder` on PATH.
fn probe_sunder_path() -> Option<String> {
    if let Ok(path) = std::env::var("SUNDER_PATH")
        && std::path::Path::new(&path).exists() {
            return Some(path);
        }

    // Try cargo-sunder first (the standard entry point)
    for name in &["cargo-sunder", "sunder"] {
        if let Ok(output) = Command::new("which").arg(name).output()
            && output.status.success() {
                let path = String::from_utf8_lossy(&output.stdout).trim().to_string();
                if !path.is_empty() {
                    return Some(path);
                }
            }
    }

    None
}

/// Get the cached sunder path, probing only once.
fn cached_sunder_path() -> Option<&'static String> {
    SUNDER_PATH.get_or_init(probe_sunder_path).as_ref()
}

/// Subprocess-based sunder backend.
///
/// Communicates with sunder via the CLI, parsing the structured result
/// protocol for machine-readable output. This is the Phase 1 implementation
/// that will be superseded by direct in-process integration when the
/// `trust-build` feature is enabled.
pub struct CliBackend {
    /// Resolved solver path.
    solver_path: Option<String>,
    /// Extra solver arguments.
    solver_args: Vec<String>,
    /// Timeout in milliseconds.
    timeout_ms: u64,
    /// Diagnostic configuration.
    diag_config: DiagConfig,
    /// Memory tracking level.
    track_level: String,
    /// Whether to use structured result protocol.
    structured_results: bool,
}

impl CliBackend {
    /// Create a new CLI backend from config.
    pub(crate) fn new(config: &SunderConfig) -> Self {
        Self {
            solver_path: config.solver_path.clone(),
            solver_args: config.solver_args.clone(),
            timeout_ms: config.timeout_ms,
            diag_config: config.diagnostics.clone(),
            track_level: config.track_level.clone(),
            structured_results: config.structured_results,
        }
    }

    /// Resolve the solver path: explicit config > cached probe.
    fn resolve_path(&self) -> Result<&str, SunderLibError> {
        if let Some(ref path) = self.solver_path {
            Ok(path.as_str())
        } else {
            cached_sunder_path().map(|s| s.as_str()).ok_or_else(|| {
                SunderLibError::BinaryNotFound {
                    reason: "set SUNDER_PATH env or install cargo-sunder on PATH".to_string(),
                }
            })
        }
    }

    /// Build the command arguments for a verification run.
    fn build_verify_args(&self, function_name: &str, contracts: &ContractSet) -> Vec<String> {
        let mut args = vec![
            "--function".to_string(),
            function_name.to_string(),
            "--track".to_string(),
            self.track_level.clone(),
        ];

        // Contract arguments
        for contract in &contracts.requires {
            args.push("--requires".to_string());
            args.push(contract.expression.clone());
        }
        for contract in &contracts.ensures {
            args.push("--ensures".to_string());
            args.push(contract.expression.clone());
        }
        for contract in &contracts.invariants {
            args.push("--invariant".to_string());
            args.push(contract.expression.clone());
        }

        if contracts.trusted {
            args.push("--trusted".to_string());
        }

        // Extra user args
        args.extend(self.solver_args.iter().cloned());

        args
    }

    /// Run sunder and capture stdout + stderr.
    fn run_subprocess(&self, args: &[String]) -> Result<(String, String, i32), SunderLibError> {
        let path = self.resolve_path()?;

        let mut cmd = Command::new(path);
        cmd.args(args)
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());

        // Enable structured result protocol
        if self.structured_results {
            cmd.env("SUNDER_RESULT_PROTOCOL", "1");
        }

        let child = cmd.spawn()?;
        let output = child.wait_with_output()?;

        let stdout = String::from_utf8_lossy(&output.stdout).to_string();
        let stderr = String::from_utf8_lossy(&output.stderr).to_string();
        let code = output.status.code().unwrap_or(-1);

        Ok((stdout, stderr, code))
    }

    /// Parse the structured result wire line from stderr.
    fn parse_wire_line(stderr: &str) -> Option<VerificationCounts> {
        for line in stderr.lines() {
            if let Some(rest) = line.strip_prefix(WIRE_PREFIX) {
                let rest = rest.trim();
                return Some(parse_counts(rest));
            }
        }
        None
    }

    /// Parse diagnostics from stderr, excluding the wire line.
    fn parse_diagnostics(stderr: &str) -> Vec<DiagnosticMessage> {
        stderr
            .lines()
            .filter(|line| !line.trim().is_empty() && !line.starts_with(WIRE_PREFIX))
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
}

impl SunderBackend for CliBackend {
    fn verify(
        &self,
        function_name: &str,
        contracts: &ContractSet,
    ) -> Result<SunderResult, SunderLibError> {
        let start = Instant::now();
        let args = self.build_verify_args(function_name, contracts);
        let (stdout, stderr, exit_code) = self.run_subprocess(&args)?;
        let elapsed = start.elapsed().as_millis() as u64;

        // Check timeout
        if elapsed >= self.timeout_ms {
            return Ok(SunderResult {
                verdict: Verdict::Timeout,
                function_verdicts: Vec::new(),
                loop_invariants: Vec::new(),
                proof_certificate: None,
                time_ms: elapsed,
                diagnostics: Vec::new(),
                function_name: function_name.to_string(),
                counts: VerificationCounts::default(),
            });
        }

        // Parse diagnostics
        let diagnostics = if self.diag_config == DiagConfig::Capture {
            Self::parse_diagnostics(&stderr)
        } else {
            Vec::new()
        };

        // Parse structured results if available
        let counts = Self::parse_wire_line(&stderr).unwrap_or_default();

        // Derive verdict from exit code and counts
        let verdict = derive_verdict(exit_code, &counts, &stdout);

        // Parse function-level verdicts from stdout
        let function_verdicts = parse_function_verdicts(&stdout, function_name);

        // Parse any inferred invariants from stdout
        let loop_invariants = parse_inferred_invariants(&stdout, function_name);

        Ok(SunderResult {
            verdict,
            function_verdicts,
            loop_invariants,
            proof_certificate: None,
            time_ms: elapsed,
            diagnostics,
            function_name: function_name.to_string(),
            counts,
        })
    }

    fn infer_invariants(
        &self,
        function_name: &str,
    ) -> Result<Vec<LoopInvariant>, SunderLibError> {
        let mut args = vec![
            "--function".to_string(),
            function_name.to_string(),
            "--infer-invariants".to_string(),
        ];
        args.extend(self.solver_args.iter().cloned());

        let (_stdout, _stderr, _exit_code) = self.run_subprocess(&args)?;

        // Parse invariants from output
        let invariants = parse_inferred_invariants(&_stdout, function_name);
        Ok(invariants)
    }
}

/// Derive the overall verdict from exit code and counts.
fn derive_verdict(exit_code: i32, counts: &VerificationCounts, _stdout: &str) -> Verdict {
    match exit_code {
        0 => Verdict::Verified,
        1 => Verdict::Failed,
        2 => {
            if counts.errors > 0 {
                Verdict::Error {
                    message: format!("{} verification errors", counts.errors),
                }
            } else if counts.assumed > 0 {
                Verdict::Unknown {
                    reason: format!("{} functions assumed (not proven)", counts.assumed),
                }
            } else {
                Verdict::Unknown {
                    reason: "verification inconclusive (exit code 2)".to_string(),
                }
            }
        }
        3 => Verdict::Error {
            message: "contract parse errors".to_string(),
        },
        _ => Verdict::Error {
            message: format!("unexpected exit code: {exit_code}"),
        },
    }
}

/// Parse per-function verdicts from sunder's stdout.
///
/// Sunder emits lines like:
///   `Verified: module::function (3/3 obligations)`
///   `Failed: module::function (1/3 obligations)`
fn parse_function_verdicts(stdout: &str, default_name: &str) -> Vec<FunctionVerdict> {
    let mut verdicts = Vec::new();

    for line in stdout.lines() {
        let trimmed = line.trim();

        let (verdict, rest) = if let Some(rest) = trimmed.strip_prefix("Verified: ") {
            (Verdict::Verified, rest)
        } else if let Some(rest) = trimmed.strip_prefix("Failed: ") {
            (Verdict::Failed, rest)
        } else if let Some(rest) = trimmed.strip_prefix("Error: ") {
            (
                Verdict::Error {
                    message: rest.to_string(),
                },
                rest,
            )
        } else {
            continue;
        };

        // Parse "function_name (N/M obligations)"
        let (name, obligations) = if let Some(paren_start) = rest.find('(') {
            let name = rest[..paren_start].trim().to_string();
            let obligation_str = &rest[paren_start..];
            let (discharged, total) = parse_obligation_counts(obligation_str);
            (name, (discharged, total))
        } else {
            (rest.trim().to_string(), (0, 0))
        };

        verdicts.push(FunctionVerdict {
            function_name: name,
            verdict,
            obligation_count: obligations.1,
            discharged_count: obligations.0,
            has_axiom_deps: false,
        });
    }

    // If no function verdicts parsed, create a default one
    if verdicts.is_empty() && !stdout.trim().is_empty() {
        verdicts.push(FunctionVerdict {
            function_name: default_name.to_string(),
            verdict: Verdict::Unknown {
                reason: "could not parse function-level verdicts".to_string(),
            },
            obligation_count: 0,
            discharged_count: 0,
            has_axiom_deps: false,
        });
    }

    verdicts
}

/// Parse "(N/M obligations)" from a verdict line.
fn parse_obligation_counts(s: &str) -> (u32, u32) {
    let inner = s.trim_start_matches('(').trim_end_matches(')').trim();
    if let Some(slash_pos) = inner.find('/') {
        let discharged = inner[..slash_pos].trim().parse::<u32>().unwrap_or(0);
        let rest = &inner[slash_pos + 1..];
        let total_str = rest.split_whitespace().next().unwrap_or("0");
        let total = total_str.parse::<u32>().unwrap_or(0);
        (discharged, total)
    } else {
        (0, 0)
    }
}

/// Parse inferred loop invariants from sunder's output.
///
/// Sunder emits invariant candidates as:
///   `Invariant: loop@bb5 in module::function: x > 0 [confidence=0.95]`
fn parse_inferred_invariants(stdout: &str, default_function: &str) -> Vec<LoopInvariant> {
    let mut invariants = Vec::new();

    for line in stdout.lines() {
        let trimmed = line.trim();
        if let Some(rest) = trimmed.strip_prefix("Invariant: ")
            && let Some(inv) = parse_invariant_line(rest, default_function) {
                invariants.push(inv);
            }
    }

    invariants
}

/// Parse a single invariant line.
fn parse_invariant_line(line: &str, default_function: &str) -> Option<LoopInvariant> {
    // Expected format: "loop@bb5 in module::function: x > 0 [confidence=0.95]"
    let (loop_id, rest) = if let Some(in_pos) = line.find(" in ") {
        (line[..in_pos].to_string(), &line[in_pos + 4..])
    } else {
        return None;
    };

    let (function_name, rest) = if let Some(colon_pos) = rest.find(": ") {
        (rest[..colon_pos].to_string(), &rest[colon_pos + 2..])
    } else {
        (default_function.to_string(), line)
    };

    // Extract confidence from [confidence=X.XX] suffix
    let (expression, confidence, verified) = if let Some(bracket_pos) = rest.rfind('[') {
        let expr = rest[..bracket_pos].trim().to_string();
        let meta = &rest[bracket_pos..];
        let conf = extract_confidence(meta);
        let ver = meta.contains("verified");
        (expr, conf, ver)
    } else {
        (rest.trim().to_string(), 0.5, false)
    };

    Some(LoopInvariant {
        function_name,
        loop_id,
        expression,
        confidence,
        verified,
    })
}

/// Extract confidence value from "[confidence=0.95]" or similar.
fn extract_confidence(meta: &str) -> f64 {
    if let Some(eq_pos) = meta.find("confidence=") {
        let rest = &meta[eq_pos + 11..];
        let end = rest.find(|c: char| !c.is_ascii_digit() && c != '.').unwrap_or(rest.len());
        rest[..end].parse::<f64>().unwrap_or(0.5)
    } else {
        0.5
    }
}

/// Parse key=value pairs from the wire line into counts.
fn parse_counts(rest: &str) -> VerificationCounts {
    let mut counts = VerificationCounts::default();

    for pair in rest.split_whitespace() {
        if let Some((key, value)) = pair.split_once('=') {
            let val: u64 = value.parse().unwrap_or(0);
            match key {
                "verified" => counts.verified = val,
                "failed" => counts.failed = val,
                "errors" => counts.errors = val,
                "warnings" => counts.warnings = val,
                "assumed" => counts.assumed = val,
                "trusted" => counts.trusted = val,
                "skipped" => counts.skipped = val,
                "verified_with_axiom_deps" => counts.verified_with_axiom_deps = val,
                _ => {} // Forward compatibility: ignore unknown keys
            }
        }
    }

    counts
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::contract::Contract;

    #[test]
    fn test_derive_verdict_exit_0_verified() {
        let counts = VerificationCounts {
            verified: 3,
            ..Default::default()
        };
        let verdict = derive_verdict(0, &counts, "");
        assert_eq!(verdict, Verdict::Verified);
    }

    #[test]
    fn test_derive_verdict_exit_1_failed() {
        let counts = VerificationCounts {
            failed: 1,
            ..Default::default()
        };
        let verdict = derive_verdict(1, &counts, "");
        assert_eq!(verdict, Verdict::Failed);
    }

    #[test]
    fn test_derive_verdict_exit_2_errors() {
        let counts = VerificationCounts {
            errors: 2,
            ..Default::default()
        };
        let verdict = derive_verdict(2, &counts, "");
        assert!(matches!(verdict, Verdict::Error { .. }));
    }

    #[test]
    fn test_derive_verdict_exit_3_parse_errors() {
        let counts = VerificationCounts::default();
        let verdict = derive_verdict(3, &counts, "");
        assert!(matches!(verdict, Verdict::Error { .. }));
    }

    #[test]
    fn test_parse_wire_line_valid() {
        let stderr = "some output\nSUNDER_RESULT:v1 verified=5 failed=1 errors=0 warnings=2 assumed=0 trusted=1 skipped=0 verified_with_axiom_deps=0\nmore output\n";
        let counts = CliBackend::parse_wire_line(stderr).expect("should parse");
        assert_eq!(counts.verified, 5);
        assert_eq!(counts.failed, 1);
        assert_eq!(counts.warnings, 2);
        assert_eq!(counts.trusted, 1);
    }

    #[test]
    fn test_parse_wire_line_none() {
        let stderr = "no wire line here\njust regular output\n";
        assert!(CliBackend::parse_wire_line(stderr).is_none());
    }

    #[test]
    fn test_parse_function_verdicts() {
        let stdout = "Verified: my::module::func (3/3 obligations)\nFailed: my::module::bad_func (1/5 obligations)\n";
        let verdicts = parse_function_verdicts(stdout, "default");
        assert_eq!(verdicts.len(), 2);
        assert_eq!(verdicts[0].function_name, "my::module::func");
        assert_eq!(verdicts[0].verdict, Verdict::Verified);
        assert_eq!(verdicts[0].discharged_count, 3);
        assert_eq!(verdicts[0].obligation_count, 3);
        assert_eq!(verdicts[1].function_name, "my::module::bad_func");
        assert_eq!(verdicts[1].verdict, Verdict::Failed);
        assert_eq!(verdicts[1].discharged_count, 1);
        assert_eq!(verdicts[1].obligation_count, 5);
    }

    #[test]
    fn test_parse_function_verdicts_empty() {
        let verdicts = parse_function_verdicts("", "default");
        assert!(verdicts.is_empty());
    }

    #[test]
    fn test_parse_obligation_counts() {
        assert_eq!(parse_obligation_counts("(3/5 obligations)"), (3, 5));
        assert_eq!(parse_obligation_counts("(0/0)"), (0, 0));
        assert_eq!(parse_obligation_counts("invalid"), (0, 0));
    }

    #[test]
    fn test_parse_inferred_invariants() {
        let stdout = "Invariant: loop@bb5 in my::func: x > 0 [confidence=0.95]\nInvariant: loop@bb8 in my::func: y >= 0 [confidence=0.80, verified]\n";
        let invariants = parse_inferred_invariants(stdout, "my::func");
        assert_eq!(invariants.len(), 2);
        assert_eq!(invariants[0].loop_id, "loop@bb5");
        assert_eq!(invariants[0].expression, "x > 0");
        assert!((invariants[0].confidence - 0.95).abs() < f64::EPSILON);
        assert!(!invariants[0].verified);
        assert_eq!(invariants[1].loop_id, "loop@bb8");
        assert!(invariants[1].verified);
    }

    #[test]
    fn test_parse_inferred_invariants_empty() {
        let invariants = parse_inferred_invariants("no invariants here", "func");
        assert!(invariants.is_empty());
    }

    #[test]
    fn test_extract_confidence() {
        assert!((extract_confidence("[confidence=0.95]") - 0.95).abs() < f64::EPSILON);
        assert!((extract_confidence("[confidence=1.0, verified]") - 1.0).abs() < f64::EPSILON);
        assert!((extract_confidence("[no confidence]") - 0.5).abs() < f64::EPSILON);
    }

    #[test]
    fn test_parse_counts() {
        let counts = parse_counts("verified=3 failed=1 errors=0 warnings=0 assumed=0 trusted=0 skipped=2 verified_with_axiom_deps=0");
        assert_eq!(counts.verified, 3);
        assert_eq!(counts.failed, 1);
        assert_eq!(counts.skipped, 2);
    }

    #[test]
    fn test_parse_counts_unknown_keys() {
        let counts = parse_counts("verified=1 future_field=42");
        assert_eq!(counts.verified, 1);
    }

    #[test]
    fn test_parse_diagnostics() {
        let stderr = "SUNDER_RESULT:v1 verified=1\nerror: something failed\nwarning: check this\nnote here\n";
        let diags = CliBackend::parse_diagnostics(stderr);
        assert_eq!(diags.len(), 3); // wire line excluded
        assert_eq!(diags[0].level, DiagLevel::Error);
        assert_eq!(diags[1].level, DiagLevel::Warning);
        assert_eq!(diags[2].level, DiagLevel::Note);
    }

    #[test]
    fn test_build_verify_args() {
        let config = SunderConfig::new().with_track_level("mem");
        let backend = CliBackend::new(&config);
        let contracts = ContractSet::new()
            .with_requires(Contract::requires("x > 0"))
            .with_ensures(Contract::ensures("result >= x"));
        let args = backend.build_verify_args("my::func", &contracts);
        assert!(args.contains(&"--function".to_string()));
        assert!(args.contains(&"my::func".to_string()));
        assert!(args.contains(&"--track".to_string()));
        assert!(args.contains(&"mem".to_string()));
        assert!(args.contains(&"--requires".to_string()));
        assert!(args.contains(&"x > 0".to_string()));
        assert!(args.contains(&"--ensures".to_string()));
        assert!(args.contains(&"result >= x".to_string()));
    }

    #[test]
    fn test_contract_set_builder() {
        let contracts = ContractSet::new()
            .with_requires(Contract::requires("x > 0"))
            .with_requires(Contract::requires("y != 0"))
            .with_ensures(Contract::ensures("result == x / y"))
            .with_invariant(Contract::invariant("i < n"))
            .with_trusted(false);
        assert_eq!(contracts.requires.len(), 2);
        assert_eq!(contracts.ensures.len(), 1);
        assert_eq!(contracts.invariants.len(), 1);
        assert!(!contracts.trusted);
        assert_eq!(contracts.len(), 4);
        assert!(!contracts.is_empty());
    }

    #[test]
    fn test_contract_set_empty() {
        let contracts = ContractSet::new();
        assert!(contracts.is_empty());
        assert_eq!(contracts.len(), 0);
    }

    #[test]
    fn test_sunder_result_verdict_helpers() {
        let verified = SunderResult {
            verdict: Verdict::Verified,
            function_verdicts: Vec::new(),
            loop_invariants: Vec::new(),
            proof_certificate: None,
            time_ms: 100,
            diagnostics: Vec::new(),
            function_name: "test".to_string(),
            counts: VerificationCounts::default(),
        };
        assert!(verified.is_verified());
        assert!(!verified.is_failed());
        assert!(!verified.is_unknown());

        let failed = SunderResult {
            verdict: Verdict::Failed,
            function_verdicts: Vec::new(),
            loop_invariants: Vec::new(),
            proof_certificate: None,
            time_ms: 100,
            diagnostics: Vec::new(),
            function_name: "test".to_string(),
            counts: VerificationCounts::default(),
        };
        assert!(!failed.is_verified());
        assert!(failed.is_failed());

        let unknown = SunderResult {
            verdict: Verdict::Unknown {
                reason: "test".to_string(),
            },
            function_verdicts: Vec::new(),
            loop_invariants: Vec::new(),
            proof_certificate: None,
            time_ms: 100,
            diagnostics: Vec::new(),
            function_name: "test".to_string(),
            counts: VerificationCounts::default(),
        };
        assert!(unknown.is_unknown());
    }

    #[test]
    fn test_sunder_result_to_verification_result_verified() {
        let result = SunderResult {
            verdict: Verdict::Verified,
            function_verdicts: Vec::new(),
            loop_invariants: Vec::new(),
            proof_certificate: None,
            time_ms: 42,
            diagnostics: Vec::new(),
            function_name: "test_fn".to_string(),
            counts: VerificationCounts::default(),
        };
        let vr = result.to_verification_result();
        assert!(vr.is_proved());
        assert_eq!(vr.solver_name(), "sunder-lib");
        assert_eq!(vr.time_ms(), 42);
    }

    #[test]
    fn test_sunder_result_to_verification_result_failed() {
        let result = SunderResult {
            verdict: Verdict::Failed,
            function_verdicts: Vec::new(),
            loop_invariants: Vec::new(),
            proof_certificate: None,
            time_ms: 15,
            diagnostics: Vec::new(),
            function_name: "test_fn".to_string(),
            counts: VerificationCounts::default(),
        };
        let vr = result.to_verification_result();
        assert!(vr.is_failed());
        assert_eq!(vr.solver_name(), "sunder-lib");
    }

    #[test]
    fn test_sunder_result_to_verification_result_timeout() {
        let result = SunderResult {
            verdict: Verdict::Timeout,
            function_verdicts: Vec::new(),
            loop_invariants: Vec::new(),
            proof_certificate: None,
            time_ms: 60_000,
            diagnostics: Vec::new(),
            function_name: "test_fn".to_string(),
            counts: VerificationCounts::default(),
        };
        let vr = result.to_verification_result();
        assert!(matches!(vr, trust_types::VerificationResult::Timeout { .. }));
    }

    #[test]
    fn test_sunder_config_builder() {
        let config = SunderConfig::new()
            .with_timeout(120_000)
            .with_solver_path("/usr/local/bin/sunder")
            .with_diagnostics(DiagConfig::Capture)
            .with_proofs(true)
            .with_track_level("mem")
            .with_infer_invariants(true);

        assert_eq!(config.timeout_ms, 120_000);
        assert_eq!(config.solver_path.as_deref(), Some("/usr/local/bin/sunder"));
        assert_eq!(config.diagnostics, DiagConfig::Capture);
        assert!(config.produce_proofs);
        assert_eq!(config.track_level, "mem");
        assert!(config.infer_invariants);
    }
}
