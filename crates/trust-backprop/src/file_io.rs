//! File I/O for trust-backprop: read source, apply rewrites, write modified files.
//!
//! Bridges the gap between the in-memory `RewriteEngine` and the filesystem.
//! Reads `.rs` source files, converts proposals into offset-aware rewrites via
//! `proposal_converter`, applies them via `RewriteEngine`, and writes results.
//!
//! Author: Andrew Yates <andrew@andrewdyates.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;
use std::io::Write;
use std::path::Path;

use crate::proposal_converter::{convert_proposal, ConvertError};
use crate::rewriter::{RewriteEngine, RewriteError};
use crate::{RewritePlan, SourceRewrite};
use trust_strengthen::Proposal;

/// Errors from file-level rewrite operations.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum FileRewriteError {
    /// An I/O error reading or writing a file.
    #[error("I/O error on `{path}`: {source}")]
    Io {
        path: String,
        source: std::io::Error,
    },
    /// A proposal conversion error (function not found, etc.).
    #[error(transparent)]
    Convert(#[from] ConvertError),
    /// A rewrite engine error (offset mismatch, etc.).
    #[error(transparent)]
    Rewrite(#[from] RewriteError),
}

/// Result of applying rewrites to a single file.
#[derive(Debug)]
pub struct FileRewriteResult {
    /// The file path that was rewritten.
    pub path: String,
    /// The original source text.
    pub original: String,
    /// The modified source text.
    pub modified: String,
    /// Number of rewrites applied.
    pub rewrite_count: usize,
}

/// Read a source file from disk.
///
/// # Errors
///
/// Returns `FileRewriteError::Io` if the file cannot be read.
pub fn read_source(path: impl AsRef<Path>) -> Result<String, FileRewriteError> {
    let path_ref = path.as_ref();
    std::fs::read_to_string(path_ref).map_err(|e| FileRewriteError::Io {
        path: path_ref.display().to_string(),
        source: e,
    })
}

/// Write modified source back to disk atomically.
///
/// Uses the tempfile + rename pattern to prevent partial writes: content is
/// written to a temporary file in the same directory as the target, then
/// atomically renamed into place. If the process crashes mid-write, the
/// original file remains intact.
///
/// # Errors
///
/// Returns `FileRewriteError::Io` if the file cannot be written.
pub fn write_source(path: impl AsRef<Path>, content: &str) -> Result<(), FileRewriteError> {
    let path_ref = path.as_ref();
    let parent = path_ref.parent().unwrap_or(Path::new("."));

    // Create temp file in the same directory to ensure same-filesystem rename.
    let mut tmp = tempfile::NamedTempFile::new_in(parent).map_err(|e| FileRewriteError::Io {
        path: path_ref.display().to_string(),
        source: e,
    })?;

    tmp.write_all(content.as_bytes())
        .map_err(|e| FileRewriteError::Io {
            path: path_ref.display().to_string(),
            source: e,
        })?;

    tmp.flush().map_err(|e| FileRewriteError::Io {
        path: path_ref.display().to_string(),
        source: e,
    })?;

    // Atomic rename into the target path.
    tmp.persist(path_ref)
        .map_err(|e| FileRewriteError::Io {
            path: path_ref.display().to_string(),
            source: e.error,
        })?;

    Ok(())
}

/// Convert proposals into a `RewritePlan` with real byte offsets by reading source files.
///
/// Groups proposals by file, reads each file, locates functions, and produces
/// a sorted `RewritePlan` ready for application.
///
/// # Errors
///
/// Returns `FileRewriteError::Io` if a source file cannot be read.
/// Returns `FileRewriteError::Convert` if a function cannot be located.
pub fn proposals_to_plan(
    proposals: &[Proposal],
    source_root: impl AsRef<Path>,
) -> Result<RewritePlan, FileRewriteError> {
    let root = source_root.as_ref();
    let mut plan = RewritePlan::new(format!("File-aware plan: {} proposals", proposals.len()));

    // Cache source contents by file path to avoid re-reading
    let mut source_cache: FxHashMap<String, String> = FxHashMap::default();

    for proposal in proposals {
        let file_path_str = &proposal.function_path;
        let full_path = root.join(file_path_str);
        let full_path_str = full_path.display().to_string();

        // Read source if not cached
        if !source_cache.contains_key(file_path_str) {
            let source = read_source(&full_path)?;
            source_cache.insert(file_path_str.clone(), source);
        }

        let source = source_cache
            .get(file_path_str)
            // SAFETY: We just inserted into source_cache above.
            .unwrap_or_else(|| unreachable!("key missing from cache after insertion"));

        let rewrites = convert_proposal(proposal, source, &full_path_str)?;
        plan.rewrites.extend(rewrites);
    }

    plan.sort_for_application();
    Ok(plan)
}

/// Apply a `RewritePlan` to files on disk, returning results for each modified file.
///
/// Groups rewrites by file, reads each file, applies all rewrites (in descending
/// offset order), and writes the result back. Returns a `FileRewriteResult` per file.
///
/// # Errors
///
/// Returns `FileRewriteError::Io` on read/write failures.
/// Returns `FileRewriteError::Rewrite` on rewrite engine failures.
pub fn apply_plan_to_files(plan: &RewritePlan) -> Result<Vec<FileRewriteResult>, FileRewriteError> {
    let engine = RewriteEngine::new();

    // Group rewrites by file
    let mut by_file: FxHashMap<&str, Vec<&SourceRewrite>> = FxHashMap::default();
    for rewrite in &plan.rewrites {
        by_file
            .entry(rewrite.file_path.as_str())
            .or_default()
            .push(rewrite);
    }

    let mut results = Vec::new();

    for (file_path, rewrites) in &by_file {
        let original = read_source(file_path)?;
        let mut modified = original.clone();

        for rewrite in rewrites {
            modified = engine.apply_rewrite(&modified, rewrite)?;
        }

        let rewrite_count = rewrites.len();
        write_source(file_path, &modified)?;

        results.push(FileRewriteResult {
            path: (*file_path).to_owned(),
            original,
            modified,
            rewrite_count,
        });
    }

    Ok(results)
}

/// Apply a rewrite plan to source text in memory (no file I/O).
///
/// Convenience wrapper around `RewriteEngine::apply_plan_to_source` for callers
/// that already have the source in memory.
///
/// # Errors
///
/// Returns `RewriteError` on rewrite failures (wrapped in `FileRewriteError`).
pub fn apply_plan_to_source(
    source: &str,
    plan: &RewritePlan,
) -> Result<String, FileRewriteError> {
    let engine = RewriteEngine::new();
    Ok(engine.apply_plan_to_source(source, plan)?)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{RewriteKind, SourceRewrite};

    #[test]
    fn test_read_source_success() {
        let dir = std::env::temp_dir().join("trust_backprop_test_read");
        std::fs::create_dir_all(&dir).unwrap();
        let file = dir.join("test_read.rs");
        std::fs::write(&file, "fn main() {}\n").unwrap();

        let content = read_source(&file).unwrap();
        assert_eq!(content, "fn main() {}\n");

        std::fs::remove_file(&file).unwrap();
        std::fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn test_read_source_not_found() {
        let result = read_source("/nonexistent/path/test.rs");
        assert!(result.is_err());
        assert!(matches!(result.unwrap_err(), FileRewriteError::Io { .. }));
    }

    #[test]
    fn test_write_source_success() {
        let dir = std::env::temp_dir().join("trust_backprop_test_write");
        std::fs::create_dir_all(&dir).unwrap();
        let file = dir.join("test_write.rs");

        write_source(&file, "fn modified() {}\n").unwrap();

        let content = std::fs::read_to_string(&file).unwrap();
        assert_eq!(content, "fn modified() {}\n");

        std::fs::remove_file(&file).unwrap();
        std::fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn test_write_source_creates_file() {
        let dir = std::env::temp_dir().join("trust_backprop_test_create");
        std::fs::create_dir_all(&dir).unwrap();
        let file = dir.join("new_file.rs");

        // Remove if exists from prior test run
        std::fs::remove_file(&file).ok();

        write_source(&file, "fn new() {}\n").unwrap();
        assert!(file.exists());

        std::fs::remove_file(&file).unwrap();
        std::fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn test_apply_plan_to_files_roundtrip() {
        let dir = std::env::temp_dir().join("trust_backprop_test_roundtrip");
        std::fs::create_dir_all(&dir).unwrap();
        let file = dir.join("roundtrip.rs");
        let source = "fn get_midpoint(a: u64, b: u64) -> u64 {\n    (a + b) / 2\n}\n";
        std::fs::write(&file, source).unwrap();

        let file_str = file.display().to_string();
        let mut plan = RewritePlan::new("roundtrip test");
        plan.rewrites.push(SourceRewrite {
            file_path: file_str.clone(),
            offset: 0,
            kind: RewriteKind::InsertAttribute {
                attribute: "#[requires(\"a + b < u64::MAX\")]".into(),
            },
            function_name: "get_midpoint".into(),
            rationale: "test".into(),
        });
        plan.sort_for_application();

        let results = apply_plan_to_files(&plan).unwrap();
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].rewrite_count, 1);

        // Verify the file on disk was modified
        let on_disk = std::fs::read_to_string(&file).unwrap();
        assert!(on_disk.contains("#[requires(\"a + b < u64::MAX\")]"));
        assert!(on_disk.contains("fn get_midpoint"));

        std::fs::remove_file(&file).unwrap();
        std::fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn test_apply_plan_to_source_in_memory() {
        let source = "fn foo() {}\n";
        let mut plan = RewritePlan::new("in-memory test");
        plan.rewrites.push(SourceRewrite {
            file_path: "test.rs".into(),
            offset: 0,
            kind: RewriteKind::InsertAttribute {
                attribute: "#[ensures(\"true\")]".into(),
            },
            function_name: "foo".into(),
            rationale: "test".into(),
        });

        let result = apply_plan_to_source(source, &plan).unwrap();
        assert!(result.contains("#[ensures(\"true\")]"));
        assert!(result.contains("fn foo()"));
    }

    #[test]
    fn test_proposals_to_plan_with_real_file() {
        let dir = std::env::temp_dir().join("trust_backprop_test_proposals");
        std::fs::create_dir_all(&dir).unwrap();

        // Create a source file at the path matching proposal.function_path
        let src_dir = dir.join("src");
        std::fs::create_dir_all(&src_dir).unwrap();
        let file = src_dir.join("lib.rs");
        std::fs::write(&file, "pub fn compute(x: u64) -> u64 {\n    x * 2\n}\n").unwrap();

        let proposal = Proposal {
            function_path: "src/lib.rs".into(),
            function_name: "compute".into(),
            kind: trust_strengthen::ProposalKind::AddPrecondition {
                spec_body: "x < u64::MAX / 2".into(),
            },
            confidence: 0.9,
            rationale: "overflow".into(),
        };

        let plan = proposals_to_plan(&[proposal], &dir).unwrap();
        assert_eq!(plan.len(), 1);
        assert!(matches!(
            &plan.rewrites[0].kind,
            RewriteKind::InsertAttribute { attribute } if attribute.contains("requires")
        ));

        std::fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn test_proposals_to_plan_file_not_found() {
        let dir = std::env::temp_dir().join("trust_backprop_test_notfound");
        std::fs::create_dir_all(&dir).unwrap();

        let proposal = Proposal {
            function_path: "nonexistent.rs".into(),
            function_name: "foo".into(),
            kind: trust_strengthen::ProposalKind::AddPrecondition {
                spec_body: "true".into(),
            },
            confidence: 0.9,
            rationale: "test".into(),
        };

        let result = proposals_to_plan(&[proposal], &dir);
        assert!(result.is_err());

        std::fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn test_file_rewrite_result_fields() {
        let result = FileRewriteResult {
            path: "test.rs".into(),
            original: "fn foo() {}".into(),
            modified: "#[requires(\"true\")]\nfn foo() {}".into(),
            rewrite_count: 1,
        };
        assert_eq!(result.path, "test.rs");
        assert_ne!(result.original, result.modified);
        assert_eq!(result.rewrite_count, 1);
    }
}
