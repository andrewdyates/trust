// trust-lsp/verification.rs: On-save verification runner with debouncing
//
// Manages verification state for the LSP server. When a file is saved,
// a new verification generation is created. If a previous verification
// is still in progress (tracked by generation number), it is logically
// cancelled — its results are discarded when it completes.
//
// The verification runner spawns `cargo trust check --format json` as a
// subprocess and parses the resulting `JsonProofReport`.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;
use std::path::{Path, PathBuf};
use std::process::Command;

use trust_types::JsonProofReport;

/// Error type for verification operations.
#[derive(Debug, thiserror::Error)]
pub(crate) enum VerificationError {
    #[error("verification command failed: {0}")]
    CommandFailed(String),
    #[error("failed to parse verification output: {0}")]
    ParseError(#[from] serde_json::Error),
    #[error("I/O error: {0}")]
    Io(#[from] std::io::Error),
    #[error("verification cancelled (superseded by generation {0})")]
    Cancelled(u64),
    #[error("no workspace root configured")]
    NoWorkspaceRoot,
}

/// Tracks the state of ongoing verification runs.
///
/// Uses a generation counter to implement debouncing: each new save
/// increments the generation. When a verification completes, its result
/// is only accepted if its generation matches the current one.
pub(crate) struct VerificationState {
    /// Monotonically increasing generation counter.
    generation: u64,
    /// Per-file generation tracking (the generation when we last requested
    /// verification for each file).
    file_generations: FxHashMap<String, u64>,
    /// Workspace root path (from `rootUri` in initialize).
    workspace_root: Option<PathBuf>,
    /// The most recent verification report per file URI.
    last_reports: FxHashMap<String, JsonProofReport>,
}

impl VerificationState {
    /// Create new verification state.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            generation: 0,
            file_generations: FxHashMap::default(),
            workspace_root: None,
            last_reports: FxHashMap::default(),
        }
    }

    /// Set the workspace root (called during initialize).
    pub(crate) fn set_workspace_root(&mut self, root: Option<&str>) {
        self.workspace_root = root.and_then(|uri| {
            uri.strip_prefix("file://").map(PathBuf::from)
        });
    }

    /// Get the workspace root path.
    #[must_use]
    pub(crate) fn workspace_root(&self) -> Option<&Path> {
        self.workspace_root.as_deref()
    }

    /// Record a save event for a file URI and return the new generation.
    ///
    /// The caller should use this generation to check whether the verification
    /// result is still current when it completes.
    pub(crate) fn on_save(&mut self, uri: &str) -> u64 {
        self.generation += 1;
        self.file_generations
            .insert(uri.to_string(), self.generation);
        self.generation
    }

    /// Check whether a generation is still current for a file URI.
    ///
    /// Returns `true` if no newer save has occurred for this file.
    #[must_use]
    pub(crate) fn is_current(&self, uri: &str, generation: u64) -> bool {
        self.file_generations
            .get(uri)
            .is_some_and(|&g| g == generation)
    }

    /// Current global generation counter.
    #[must_use]
    pub(crate) fn generation(&self) -> u64 {
        self.generation
    }

    /// Store a verification report for a file URI.
    pub(crate) fn set_report(&mut self, uri: &str, report: JsonProofReport) {
        self.last_reports.insert(uri.to_string(), report);
    }

    /// Get the most recent verification report for a file URI.
    #[must_use]
    pub(crate) fn get_report(&self, uri: &str) -> Option<&JsonProofReport> {
        self.last_reports.get(uri)
    }
}

impl Default for VerificationState {
    fn default() -> Self {
        Self::new()
    }
}

/// Run `cargo trust check --format json` for the given file.
///
/// Returns the parsed `JsonProofReport` on success.
///
/// This is a blocking call — the LSP server processes messages sequentially,
/// so this blocks the main loop. For large crates this may take >30s; the
/// debounce mechanism ensures only the most recent save triggers a full run.
pub(crate) fn run_verification(
    workspace_root: &Path,
    _file_uri: &str,
) -> Result<JsonProofReport, VerificationError> {
    let output = Command::new("cargo")
        .arg("trust")
        .arg("check")
        .arg("--format")
        .arg("json")
        .current_dir(workspace_root)
        .output()?;

    if !output.status.success() {
        // Try to parse stderr for a JSON report even on failure —
        // verification failures still produce valid JSON output.
        let stderr = String::from_utf8_lossy(&output.stderr);

        // Check stdout first (normal path for verification failures).
        if !output.stdout.is_empty() {
            let report: JsonProofReport = serde_json::from_slice(&output.stdout)?;
            return Ok(report);
        }

        return Err(VerificationError::CommandFailed(
            stderr.lines().take(5).collect::<Vec<_>>().join("\n"),
        ));
    }

    let report: JsonProofReport = serde_json::from_slice(&output.stdout)?;
    Ok(report)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_verification_state_generation_increments() {
        let mut state = VerificationState::new();
        assert_eq!(state.generation(), 0);

        let gen1 = state.on_save("file:///src/lib.rs");
        assert_eq!(gen1, 1);
        assert_eq!(state.generation(), 1);

        let gen2 = state.on_save("file:///src/main.rs");
        assert_eq!(gen2, 2);
        assert_eq!(state.generation(), 2);
    }

    #[test]
    fn test_verification_state_is_current() {
        let mut state = VerificationState::new();

        let gen1 = state.on_save("file:///src/lib.rs");
        assert!(state.is_current("file:///src/lib.rs", gen1));

        // Same file, new save => old generation is stale.
        let gen2 = state.on_save("file:///src/lib.rs");
        assert!(!state.is_current("file:///src/lib.rs", gen1));
        assert!(state.is_current("file:///src/lib.rs", gen2));
    }

    #[test]
    fn test_verification_state_different_files_independent() {
        let mut state = VerificationState::new();

        let gen_a = state.on_save("file:///a.rs");
        let _gen_b = state.on_save("file:///b.rs");

        // Saving b.rs should not affect a.rs generation.
        assert!(state.is_current("file:///a.rs", gen_a));
    }

    #[test]
    fn test_verification_state_workspace_root() {
        let mut state = VerificationState::new();
        assert!(state.workspace_root().is_none());

        state.set_workspace_root(Some("file://./project"));
        assert_eq!(
            state.workspace_root(),
            Some(Path::new("./project"))
        );
    }

    #[test]
    fn test_verification_state_store_report() {
        let mut state = VerificationState::new();
        let report = trust_types::JsonProofReport {
            metadata: trust_types::ReportMetadata {
                schema_version: "1.0".to_string(),
                trust_version: "0.1.0".to_string(),
                timestamp: "2026-01-01T00:00:00Z".to_string(),
                total_time_ms: 10,
            },
            crate_name: "test".to_string(),
            summary: trust_types::CrateSummary {
                functions_analyzed: 0,
                functions_verified: 0,
                functions_runtime_checked: 0,
                functions_with_violations: 0,
                functions_inconclusive: 0,
                total_obligations: 0,
                total_proved: 0,
                total_runtime_checked: 0,
                total_failed: 0,
                total_unknown: 0,
                verdict: trust_types::CrateVerdict::Verified,
            },
            functions: vec![],
        };

        assert!(state.get_report("file:///src/lib.rs").is_none());
        state.set_report("file:///src/lib.rs", report);
        assert!(state.get_report("file:///src/lib.rs").is_some());
    }

    #[test]
    fn test_verification_state_default() {
        let state = VerificationState::default();
        assert_eq!(state.generation(), 0);
        assert!(state.workspace_root().is_none());
    }

    #[test]
    fn test_is_current_unknown_uri_returns_false() {
        let state = VerificationState::new();
        assert!(!state.is_current("file:///unknown.rs", 1));
    }
}
