// cargo-trust types: core data structures for verification results
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use anyhow::Result;
use serde::{Deserialize, Serialize};

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
            other => anyhow::bail!(
                "unknown format `{other}`: expected terminal, json, or html"
            ),
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
// Verification result parsing
// ---------------------------------------------------------------------------

/// Outcome of a single verification obligation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum VerificationOutcome {
    Proved,
    Failed,
    Unknown,
}

/// A single verification result parsed from compiler output.
///
/// Matches lines like:
///   note: tRust [overflow:add]: arithmetic overflow (Add) -- PROVED (z4-smtlib, 8ms)
///   note: tRust [overflow:add]: arithmetic overflow (Add) -- FAILED (z4-smtlib, 8ms)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct VerificationResult {
    pub(crate) kind: String,
    pub(crate) message: String,
    pub(crate) outcome: VerificationOutcome,
    pub(crate) backend: String,
    pub(crate) time_ms: Option<u64>,
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
    let (message_part, outcome_part) =
        if let Some(sep_pos) = after_colon.find(" -- ") {
            (
                &after_colon[..sep_pos],
                &after_colon[sep_pos + 4..],
            )
        } else if let Some(sep_pos) = after_colon.find(" \u{2014} ") {
            // em-dash is 3 bytes in UTF-8
            let em_dash_len = '\u{2014}'.len_utf8();
            (
                &after_colon[..sep_pos],
                &after_colon[sep_pos + 2 + em_dash_len..],
            )
        } else {
            return None;
        };

    let message = message_part.trim().to_string();

    // Parse outcome: "PROVED (backend, time)" or "FAILED (backend, time)"
    let outcome = if outcome_part.starts_with("PROVED") {
        VerificationOutcome::Proved
    } else if outcome_part.starts_with("FAILED") {
        VerificationOutcome::Failed
    } else {
        VerificationOutcome::Unknown
    };

    // Extract backend and time from parenthesized suffix
    let (backend, time_ms) = if let Some(paren_start) = outcome_part.find('(') {
        let paren_end = outcome_part.rfind(')').unwrap_or(outcome_part.len());
        let inner = &outcome_part[paren_start + 1..paren_end];
        let parts: Vec<&str> = inner.splitn(2, ',').collect();
        let backend = parts.first().unwrap_or(&"unknown").trim().to_string();
        let time = parts.get(1).and_then(|t| {
            t.trim().strip_suffix("ms").and_then(|n| n.trim().parse::<u64>().ok())
        });
        (backend, time)
    } else {
        ("unknown".to_string(), None)
    };

    Some(VerificationResult {
        kind,
        message,
        outcome,
        backend,
        time_ms,
        raw_line: line.to_string(),
    })
}

/// tRust #542: Convert a structured `TransportObligationResult` into a cargo-trust
/// `VerificationResult`. This is used when structured JSON transport lines are
/// available, replacing the fragile text parsing of compiler diagnostics.
pub(crate) fn transport_to_verification_result(
    r: &trust_types::TransportObligationResult,
) -> VerificationResult {
    let outcome = match r.outcome.as_str() {
        "proved" => VerificationOutcome::Proved,
        "failed" => VerificationOutcome::Failed,
        _ => VerificationOutcome::Unknown,
    };
    VerificationResult {
        kind: r.kind.clone(),
        message: r.description.to_string(),
        outcome,
        backend: r.solver.clone(),
        time_ms: Some(r.time_ms),
        raw_line: String::new(),
    }
}

