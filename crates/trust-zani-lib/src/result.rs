// trust-zani-lib result types
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

//! Result types for zani verification.
//!
//! `ZaniResult` is the primary output type, containing the verdict,
//! optional counterexample, proof certificate, and violation details.

use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

use zani_core::PropertyKind;

/// The outcome of a zani verification run.
///
/// Matches the `ZaniResult` signature from the Pipeline v2 design
/// (designs/2026-04-14-verification-pipeline-v2.md, section 3.2.1).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ZaniResult {
    /// The verification verdict.
    pub verdict: Verdict,

    /// Concrete counterexample if the property was falsified.
    pub counterexample: Option<TypedCounterexample>,

    /// Proof certificate bytes if the property was proved and
    /// `ZaniConfig::produce_proofs` was enabled.
    pub proof_certificate: Option<Vec<u8>>,

    /// Detailed violation information from the solver.
    pub violations: Vec<ViolationInfo>,

    /// Wall-clock time for the verification in milliseconds.
    pub time_ms: u64,

    /// Diagnostic messages captured during verification
    /// (populated when `DiagConfig::Capture` is used).
    pub diagnostics: Vec<DiagnosticMessage>,

    /// The BMC depth used for this verification.
    pub bmc_depth: u32,

    /// The function that was verified.
    pub function_name: String,
}

impl ZaniResult {
    /// Returns `true` if the property was proved to hold.
    #[must_use]
    pub fn is_proved(&self) -> bool {
        matches!(self.verdict, Verdict::Proved)
    }

    /// Returns `true` if a counterexample was found.
    #[must_use]
    pub fn is_failed(&self) -> bool {
        matches!(self.verdict, Verdict::Failed)
    }

    /// Returns `true` if the result is inconclusive.
    #[must_use]
    pub fn is_unknown(&self) -> bool {
        matches!(self.verdict, Verdict::Unknown { .. })
    }

    /// Convert to a `trust_types::VerificationResult` for the router.
    #[must_use]
    pub fn to_verification_result(&self) -> trust_types::VerificationResult {
        match &self.verdict {
            Verdict::Proved => trust_types::VerificationResult::Proved {
                solver: "zani-lib".into(),
                time_ms: self.time_ms,
                strength: trust_types::ProofStrength::bounded(u64::from(self.bmc_depth)),
                proof_certificate: self.proof_certificate.clone(),
                solver_warnings: None,
            },
            Verdict::Failed => {
                let cex = self.counterexample.as_ref().map(|tc| {
                    let assignments: Vec<(String, trust_types::CounterexampleValue)> = tc
                        .variables
                        .iter()
                        .map(|(name, value)| (name.clone(), typed_value_to_cex_value(value)))
                        .collect();
                    trust_types::Counterexample::new(assignments)
                });
                trust_types::VerificationResult::Failed {
                    solver: "zani-lib".into(),
                    time_ms: self.time_ms,
                    counterexample: cex,
                }
            }
            Verdict::Unknown { reason } => trust_types::VerificationResult::Unknown {
                solver: "zani-lib".into(),
                time_ms: self.time_ms,
                reason: reason.clone(),
            },
            Verdict::Timeout => trust_types::VerificationResult::Timeout {
                solver: "zani-lib".into(),
                timeout_ms: self.time_ms,
            },
        }
    }
}

/// Convert a `TypedValue` to a `trust_types::CounterexampleValue`.
fn typed_value_to_cex_value(value: &TypedValue) -> trust_types::CounterexampleValue {
    match value {
        TypedValue::Bool(b) => trust_types::CounterexampleValue::Bool(*b),
        TypedValue::Int(n) => trust_types::CounterexampleValue::Int(*n),
        TypedValue::Uint(n) => trust_types::CounterexampleValue::Uint(*n),
        TypedValue::BitVec { value, .. } => trust_types::CounterexampleValue::Uint(*value),
        TypedValue::String(s) => {
            trust_types::CounterexampleValue::Uint(s.parse::<u128>().unwrap_or(0))
        }
    }
}

/// The verification verdict.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Verdict {
    /// The property holds within the BMC depth (UNSAT).
    Proved,

    /// A counterexample was found (SAT).
    Failed,

    /// The result is inconclusive.
    Unknown {
        /// Reason the result is inconclusive (e.g., bound exhaustion).
        reason: String,
    },

    /// The solver timed out.
    Timeout,
}

/// A typed counterexample from the solver.
///
/// Contains concrete variable assignments that demonstrate a property violation.
/// Unlike the text-based `Counterexample` in `trust-types`, these values retain
/// their SMT sorts (bitvector width, signedness, etc.).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TypedCounterexample {
    /// Variable assignments mapping names to typed values.
    pub variables: BTreeMap<String, TypedValue>,

    /// Multi-step execution trace if the counterexample involves loops or
    /// step-indexed variables.
    pub trace: Option<Vec<TraceStep>>,

    /// The violated property kinds from this counterexample.
    pub violated_properties: Vec<PropertyKind>,
}

impl TypedCounterexample {
    /// Create a new counterexample with the given variable assignments.
    pub fn new(variables: BTreeMap<String, TypedValue>) -> Self {
        Self { variables, trace: None, violated_properties: Vec::new() }
    }

    /// Add a trace to this counterexample.
    #[must_use]
    pub fn with_trace(mut self, trace: Vec<TraceStep>) -> Self {
        self.trace = Some(trace);
        self
    }

    /// Add violated property information.
    #[must_use]
    pub fn with_violations(mut self, properties: Vec<PropertyKind>) -> Self {
        self.violated_properties = properties;
        self
    }
}

/// A typed value from the solver model.
///
/// Preserves the SMT sort information that text-based counterexamples lose.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum TypedValue {
    /// Boolean value.
    Bool(bool),
    /// Signed integer.
    Int(i128),
    /// Unsigned integer.
    Uint(u128),
    /// Bitvector with explicit width.
    BitVec {
        /// The bitvector value.
        value: u128,
        /// Width in bits.
        width: u32,
    },
    /// String representation for complex values.
    String(String),
}

/// A step in a multi-step counterexample trace.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TraceStep {
    /// Step index (0-based).
    pub step: u32,
    /// Variable assignments at this step.
    pub assignments: BTreeMap<String, TypedValue>,
    /// Program point (basic block or line number) if available.
    pub program_point: Option<String>,
}

/// A diagnostic message from zani during verification.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DiagnosticMessage {
    /// Severity level.
    pub level: DiagLevel,
    /// The message text.
    pub message: String,
    /// Source location if available.
    pub location: Option<String>,
}

/// Diagnostic severity level.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum DiagLevel {
    /// Error diagnostic.
    Error,
    /// Warning diagnostic.
    Warning,
    /// Note/info diagnostic.
    Note,
}

/// Information about a specific violation found during verification.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ViolationInfo {
    /// The kind of property that was violated.
    pub kind: PropertyKind,
    /// Human-readable description of the violation.
    pub message: String,
    /// Source location if available.
    pub location: Option<String>,
}

/// Encoding context from `encode_function`.
///
/// In Phase 1 (subprocess mode), this contains the SMT-LIB2 script and metadata.
/// In Phase 2 (trust-build / direct mode), this will contain z4 `Context`,
/// local variable mappings (`MirLocal -> z4::Expr`), and the base constraint set.
#[derive(Debug, Clone)]
pub struct EncodingContext {
    /// The function being encoded.
    pub function_name: String,

    /// The SMT-LIB2 script representing the encoding.
    pub smtlib_script: String,

    /// BMC depth used for the encoding.
    pub bmc_depth: u32,

    /// Variable declarations extracted from the script.
    pub variable_names: Vec<String>,
}

impl EncodingContext {
    /// Create an encoding context from an SMT-LIB2 script.
    pub(crate) fn from_smtlib(
        function_name: String,
        smtlib_script: String,
        bmc_depth: u32,
    ) -> Self {
        // Extract variable names from declare-const lines
        let variable_names = smtlib_script
            .lines()
            .filter_map(|line| {
                let trimmed = line.trim();
                if trimmed.starts_with("(declare-const ") {
                    let rest = trimmed.strip_prefix("(declare-const ")?;
                    let name_end = rest.find(|c: char| c.is_whitespace())?;
                    Some(rest[..name_end].to_string())
                } else {
                    None
                }
            })
            .collect();

        Self { function_name, smtlib_script, bmc_depth, variable_names }
    }
}
