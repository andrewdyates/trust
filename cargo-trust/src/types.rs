// cargo-trust types: core data structures for verification results
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use anyhow::Result;
use serde::{Deserialize, Serialize};
use trust_types::{Counterexample, SourceSpan};

// ---------------------------------------------------------------------------
// Output format
// ---------------------------------------------------------------------------

/// Report output format for verification results.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum OutputFormat {
    Terminal,
    Json,
    Html,
}

impl OutputFormat {
    pub(crate) fn from_str(s: &str) -> Result<Self> {
        match s {
            "terminal" => Ok(Self::Terminal),
            "json" => Ok(Self::Json),
            "html" => Ok(Self::Html),
            other => anyhow::bail!("unknown format `{other}`: expected terminal, json, or html"),
        }
    }
}

// ---------------------------------------------------------------------------
// Subcommand
// ---------------------------------------------------------------------------

/// Top-level subcommands.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Subcommand {
    /// Check-only: verify without producing a binary.
    Check,
    /// Build: verify and produce a binary.
    Build,
    /// Report: generate a verification report in the requested format.
    Report,
    /// Loop: run the prove-strengthen-backprop convergence loop.
    Loop,
    /// Diff: compare current verification state against a baseline.
    Diff,
    /// Solvers: detect and report status of dMATH solver binaries.
    Solvers,
    /// Init: scaffold verification annotations for a crate.
    #[allow(dead_code)]
    Init,
}

// ---------------------------------------------------------------------------
// Binary lift report
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum BinaryLiftStatus {
    Ok,
    Incomplete,
    Failed,
}

impl BinaryLiftStatus {
    pub(crate) fn label(self) -> &'static str {
        match self {
            Self::Ok => "ok",
            Self::Incomplete => "incomplete",
            Self::Failed => "failed",
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub(crate) struct BinaryLiftFunctionReport {
    pub(crate) name: String,
    pub(crate) entry: Option<String>,
    pub(crate) blocks: usize,
    pub(crate) statements: usize,
    pub(crate) vcs: usize,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub(crate) struct BinaryLiftReport {
    pub(crate) binary: String,
    pub(crate) format: Option<String>,
    pub(crate) architecture: Option<String>,
    pub(crate) entry: Option<String>,
    pub(crate) binary_entry: Option<String>,
    pub(crate) strict: bool,
    pub(crate) status: BinaryLiftStatus,
    pub(crate) functions_lifted: usize,
    pub(crate) blocks: usize,
    pub(crate) statements: usize,
    pub(crate) vcs: usize,
    pub(crate) unsupported: usize,
    pub(crate) failures: usize,
    pub(crate) functions: Vec<BinaryLiftFunctionReport>,
    pub(crate) unsupported_items: Vec<String>,
    pub(crate) failure_items: Vec<String>,
}

// ---------------------------------------------------------------------------
// Verification result parsing
// ---------------------------------------------------------------------------

/// Outcome of a single verification obligation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum VerificationOutcome {
    Proved,
    Failed,
    RuntimeChecked,
    Timeout,
    Unknown,
}

impl VerificationOutcome {
    pub(crate) fn label(self) -> &'static str {
        match self {
            Self::Proved => "PROVED",
            Self::Failed => "FAILED",
            Self::RuntimeChecked => "RUNTIME-CHECKED",
            Self::Timeout => "TIMEOUT",
            Self::Unknown => "UNKNOWN",
        }
    }

    pub(crate) fn is_proved(self) -> bool {
        matches!(self, Self::Proved)
    }

    pub(crate) fn is_failed(self) -> bool {
        matches!(self, Self::Failed)
    }

    pub(crate) fn is_runtime_checked(self) -> bool {
        matches!(self, Self::RuntimeChecked)
    }

    pub(crate) fn is_inconclusive(self) -> bool {
        matches!(self, Self::Unknown | Self::Timeout)
    }
}

/// A single verification result parsed from compiler output.
///
/// Matches lines like:
///   note: tRust [overflow:add]: arithmetic overflow (Add) -- PROVED (z4-smtlib, 8ms)
///   note: tRust [overflow:add]: arithmetic overflow (Add) -- FAILED (z4-smtlib, 8ms)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct VerificationResult {
    pub(crate) function: String,
    pub(crate) kind: String,
    pub(crate) message: String,
    pub(crate) outcome: VerificationOutcome,
    pub(crate) backend: String,
    pub(crate) time_ms: Option<u64>,
    pub(crate) location: Option<SourceSpan>,
    pub(crate) counterexample: Option<Counterexample>,
    pub(crate) reason: Option<String>,
    pub(crate) raw_line: String,
}

/// Parse a tRust verification note from a compiler stderr line.
///
/// Expected format:
///   note: tRust [<kind>]: <message> -- <OUTCOME> (<backend>, <time>)
///   note: tRust [<kind>]: <message> — <OUTCOME> (<backend>, <time>)
///
/// Also handles the unicode em-dash variant.
pub(crate) fn parse_trust_note(line: &str) -> Option<VerificationResult> {
    let line = line.trim_start();

    // Find the "tRust [" marker after "note:"
    let trust_idx = line.find("tRust [")?;
    let after_trust = &line[trust_idx + 7..]; // skip "tRust ["

    // Extract kind: everything up to "]"
    let bracket_end = after_trust.find(']')?;
    let kind = after_trust[..bracket_end].to_string();

    // After "]: " comes the message, then " -- " or " — " separator
    let after_bracket = &after_trust[bracket_end + 1..];
    let after_colon = after_bracket.strip_prefix(": ")?;

    // Find outcome separator: " -- " (ASCII) or " — " (em-dash, encoded as \u{2014})
    let (message_part, outcome_part) = if let Some(sep_pos) = after_colon.find(" -- ") {
        (&after_colon[..sep_pos], &after_colon[sep_pos + 4..])
    } else if let Some(sep_pos) = after_colon.find(" \u{2014} ") {
        // em-dash is 3 bytes in UTF-8
        let em_dash_len = '\u{2014}'.len_utf8();
        (&after_colon[..sep_pos], &after_colon[sep_pos + 2 + em_dash_len..])
    } else {
        return None;
    };

    let message = message_part.trim().to_string();

    // Parse outcome: "PROVED (backend, time)" or "FAILED (backend, time)"
    let outcome = if outcome_part.starts_with("PROVED") {
        VerificationOutcome::Proved
    } else if outcome_part.starts_with("FAILED") {
        VerificationOutcome::Failed
    } else if outcome_part.starts_with("RUNTIME-CHECKED") {
        VerificationOutcome::RuntimeChecked
    } else if outcome_part.starts_with("TIMEOUT") {
        VerificationOutcome::Timeout
    } else {
        VerificationOutcome::Unknown
    };

    // Extract backend and time from parenthesized suffix
    let (backend, time_ms) = if let Some(paren_start) = outcome_part.find('(') {
        let paren_end = outcome_part.rfind(')').unwrap_or(outcome_part.len());
        let inner = &outcome_part[paren_start + 1..paren_end];
        let parts: Vec<&str> = inner.splitn(2, ',').collect();
        let backend = parts.first().unwrap_or(&"unknown").trim().to_string();
        let time = parts
            .get(1)
            .and_then(|t| t.trim().strip_suffix("ms").and_then(|n| n.trim().parse::<u64>().ok()));
        (backend, time)
    } else {
        ("unknown".to_string(), None)
    };

    Some(VerificationResult {
        function: "unknown".to_string(),
        kind,
        message,
        outcome,
        backend,
        time_ms,
        location: None,
        counterexample: None,
        reason: None,
        raw_line: line.to_string(),
    })
}

/// tRust #542: Convert a structured `TransportObligationResult` into a cargo-trust
/// `VerificationResult`. This is used when structured JSON transport lines are
/// available, replacing the fragile text parsing of compiler diagnostics.
pub(crate) fn transport_to_verification_result(
    function: &str,
    r: &trust_types::TransportObligationResult,
) -> VerificationResult {
    let outcome = match r.outcome.as_str() {
        "proved" => VerificationOutcome::Proved,
        "failed" => VerificationOutcome::Failed,
        "runtime_checked" => VerificationOutcome::RuntimeChecked,
        "timeout" => VerificationOutcome::Timeout,
        _ => VerificationOutcome::Unknown,
    };
    VerificationResult {
        function: function.to_string(),
        kind: r.kind.clone(),
        message: r.description.to_string(),
        outcome,
        backend: r.solver.clone(),
        time_ms: Some(r.time_ms),
        location: r.location.clone(),
        counterexample: r.counterexample_model.clone(),
        reason: r.reason.clone(),
        raw_line: String::new(),
    }
}
