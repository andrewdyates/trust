// trust-lsp/progress.rs: $/progress notification helpers
//
// Provides helpers for emitting LSP work-done progress notifications
// during verification. The lifecycle is:
//
//   1. begin("tRust verification", "Checking src/lib.rs")
//   2. end("Verification complete: 2 proved, 1 failed")
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::protocol::{ProgressParams, ProgressToken, WorkDoneProgress};

/// A progress reporter that tracks a single verification run.
///
/// Generates `ProgressParams` values ready to be sent as `$/progress`
/// notifications. The caller is responsible for the actual transport.
pub(crate) struct ProgressReporter {
    token: ProgressToken,
}

impl ProgressReporter {
    /// Create a reporter with an integer token.
    #[must_use]
    pub(crate) fn with_id(id: i64) -> Self {
        Self { token: ProgressToken::Integer(id) }
    }

    /// Build a `begin` progress notification.
    #[must_use]
    pub(crate) fn begin(&self, title: &str, message: Option<&str>) -> ProgressParams {
        ProgressParams {
            token: self.token.clone(),
            value: WorkDoneProgress::Begin {
                title: title.to_string(),
                message: message.map(ToString::to_string),
                percentage: Some(0),
                cancellable: Some(true),
            },
        }
    }

    /// Build an `end` progress notification.
    #[must_use]
    pub(crate) fn end(&self, message: &str) -> ProgressParams {
        ProgressParams {
            token: self.token.clone(),
            value: WorkDoneProgress::End { message: Some(message.to_string()) },
        }
    }
}

/// Format a verification summary message for the end notification.
#[must_use]
pub(crate) fn format_summary(proved: usize, failed: usize, unknown: usize, time_ms: u64) -> String {
    let mut parts = Vec::new();
    if proved > 0 {
        parts.push(format!("{proved} proved"));
    }
    if failed > 0 {
        parts.push(format!("{failed} failed"));
    }
    if unknown > 0 {
        parts.push(format!("{unknown} unknown"));
    }
    if parts.is_empty() {
        format!("No obligations checked ({time_ms}ms)")
    } else {
        format!("{} ({time_ms}ms)", parts.join(", "))
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_progress_reporter_begin() {
        let reporter =
            ProgressReporter { token: ProgressToken::String("trust-verify-1".to_string()) };
        let params = reporter.begin("tRust verification", Some("Checking src/lib.rs"));

        let json = serde_json::to_string(&params).expect("serialize");
        assert!(json.contains("\"token\":\"trust-verify-1\""));
        assert!(json.contains("\"kind\":\"begin\""));
        assert!(json.contains("\"title\":\"tRust verification\""));
        assert!(json.contains("\"percentage\":0"));
    }

    #[test]
    fn test_progress_reporter_end() {
        let reporter = ProgressReporter::with_id(42);
        let params = reporter.end("Done");

        let json = serde_json::to_string(&params).expect("serialize");
        assert!(json.contains("\"token\":42"));
        assert!(json.contains("\"kind\":\"end\""));
        assert!(json.contains("\"message\":\"Done\""));
    }

    #[test]
    fn test_format_summary_all_proved() {
        let msg = format_summary(5, 0, 0, 100);
        assert_eq!(msg, "5 proved (100ms)");
    }

    #[test]
    fn test_format_summary_mixed() {
        let msg = format_summary(3, 1, 2, 250);
        assert_eq!(msg, "3 proved, 1 failed, 2 unknown (250ms)");
    }

    #[test]
    fn test_format_summary_no_obligations() {
        let msg = format_summary(0, 0, 0, 10);
        assert_eq!(msg, "No obligations checked (10ms)");
    }

    #[test]
    fn test_format_summary_only_failed() {
        let msg = format_summary(0, 3, 0, 50);
        assert_eq!(msg, "3 failed (50ms)");
    }
}
