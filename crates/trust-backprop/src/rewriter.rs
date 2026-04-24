//! Source-level rewrite engine.
//!
//! Applies a `RewritePlan` to source files: inserting attributes before functions,
//! replacing expressions, and inserting assertions. Operates on raw source text
//! to avoid requiring a full parse tree.
//!
//! Author: Andrew Yates <andrew@andrewdyates.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::{RewriteKind, RewritePlan, SourceRewrite};

/// Errors that can occur during source rewriting.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub enum RewriteError {
    /// A governance rule was violated.
    #[error("governance violation in `{function}`: {violations:?}")]
    Governance { function: String, violations: Vec<crate::GovernanceViolation> },
    /// The source text did not contain the expected content at the rewrite site.
    #[error("source mismatch at offset {offset} in `{file_path}`: expected `{expected}`")]
    SourceMismatch { file_path: String, offset: usize, expected: String },
    /// The offset is out of bounds for the source text.
    #[error("offset {offset} out of bounds for `{file_path}` (length {length})")]
    OffsetOutOfBounds { file_path: String, offset: usize, length: usize },
}

/// Engine that applies rewrite plans to source text.
///
/// The engine works on in-memory source strings. File I/O is the caller's
/// responsibility -- this keeps the engine testable and side-effect free.
#[derive(Debug)]
pub struct RewriteEngine {
    /// The current indentation string to use for inserted lines.
    pub(crate) indent: String,
}

impl Default for RewriteEngine {
    fn default() -> Self {
        Self { indent: "    ".into() }
    }
}

impl RewriteEngine {
    /// Create a new rewrite engine with default settings.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a rewrite engine with custom indentation.
    #[must_use]
    pub fn with_indent(indent: impl Into<String>) -> Self {
        Self { indent: indent.into() }
    }

    /// Apply a single rewrite to source text, returning the modified text.
    ///
    /// # Errors
    ///
    /// Returns `RewriteError::OffsetOutOfBounds` if the offset exceeds the source length.
    /// Returns `RewriteError::SourceMismatch` for `ReplaceExpression` when the old text
    /// is not found at the specified offset.
    pub fn apply_rewrite(
        &self,
        source: &str,
        rewrite: &SourceRewrite,
    ) -> Result<String, RewriteError> {
        if rewrite.offset > source.len() {
            return Err(RewriteError::OffsetOutOfBounds {
                file_path: rewrite.file_path.clone(),
                offset: rewrite.offset,
                length: source.len(),
            });
        }

        match &rewrite.kind {
            RewriteKind::InsertAttribute { attribute } => {
                Ok(self.insert_at(source, rewrite.offset, &format!("{attribute}\n")))
            }
            RewriteKind::ReplaceExpression { old_text, new_text } => {
                self.replace_at(source, rewrite, old_text, new_text)
            }
            RewriteKind::InsertAssertion { assertion } => {
                let line = format!("{}{assertion}\n", self.indent);
                Ok(self.insert_at(source, rewrite.offset, &line))
            }
        }
    }

    /// Apply all rewrites in a plan to a single source string.
    ///
    /// The plan MUST be sorted (via `sort_for_application`) with descending offsets
    /// so that earlier rewrites do not invalidate later offsets.
    ///
    /// # Errors
    ///
    /// Returns the first `RewriteError` encountered.
    pub fn apply_plan_to_source(
        &self,
        source: &str,
        plan: &RewritePlan,
    ) -> Result<String, RewriteError> {
        let mut result = source.to_owned();
        for rewrite in &plan.rewrites {
            result = self.apply_rewrite(&result, rewrite)?;
        }
        Ok(result)
    }

    /// Insert text at a byte offset.
    fn insert_at(&self, source: &str, offset: usize, text: &str) -> String {
        let mut result = String::with_capacity(source.len() + text.len());
        result.push_str(&source[..offset]);
        result.push_str(text);
        result.push_str(&source[offset..]);
        result
    }

    /// Replace text at a byte offset.
    fn replace_at(
        &self,
        source: &str,
        rewrite: &SourceRewrite,
        old_text: &str,
        new_text: &str,
    ) -> Result<String, RewriteError> {
        let end = rewrite.offset + old_text.len();
        if end > source.len() || &source[rewrite.offset..end] != old_text {
            return Err(RewriteError::SourceMismatch {
                file_path: rewrite.file_path.clone(),
                offset: rewrite.offset,
                expected: old_text.into(),
            });
        }

        let mut result = String::with_capacity(source.len() - old_text.len() + new_text.len());
        result.push_str(&source[..rewrite.offset]);
        result.push_str(new_text);
        result.push_str(&source[end..]);
        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{RewriteKind, SourceRewrite};

    fn make_rewrite(offset: usize, kind: RewriteKind) -> SourceRewrite {
        SourceRewrite {
            file_path: "test.rs".into(),
            offset,
            kind,
            function_name: "test_fn".into(),
            rationale: "test".into(),
        }
    }

    #[test]
    fn test_insert_attribute_at_start() {
        let engine = RewriteEngine::new();
        let source = "fn foo() {}\n";
        let rewrite = make_rewrite(
            0,
            RewriteKind::InsertAttribute { attribute: "#[requires(\"x > 0\")]".into() },
        );

        let result = engine.apply_rewrite(source, &rewrite).unwrap();
        assert_eq!(result, "#[requires(\"x > 0\")]\nfn foo() {}\n");
    }

    #[test]
    fn test_insert_attribute_at_offset() {
        let engine = RewriteEngine::new();
        let source = "// comment\nfn foo() {}\n";
        let rewrite = make_rewrite(
            11, // after "// comment\n"
            RewriteKind::InsertAttribute { attribute: "#[ensures(\"result >= 0\")]".into() },
        );

        let result = engine.apply_rewrite(source, &rewrite).unwrap();
        assert!(result.contains("#[ensures(\"result >= 0\")]"));
        assert!(result.starts_with("// comment\n"));
    }

    #[test]
    fn test_replace_expression() {
        let engine = RewriteEngine::new();
        let source = "let x = a + b;\n";
        let rewrite = make_rewrite(
            8, // offset of "a + b"
            RewriteKind::ReplaceExpression {
                old_text: "a + b".into(),
                new_text: "a.checked_add(b).unwrap()".into(),
            },
        );

        let result = engine.apply_rewrite(source, &rewrite).unwrap();
        assert_eq!(result, "let x = a.checked_add(b).unwrap();\n");
    }

    #[test]
    fn test_replace_expression_mismatch() {
        let engine = RewriteEngine::new();
        let source = "let x = a + b;\n";
        let rewrite = make_rewrite(
            8,
            RewriteKind::ReplaceExpression {
                old_text: "a * b".into(),
                new_text: "a.checked_mul(b).unwrap()".into(),
            },
        );

        let result = engine.apply_rewrite(source, &rewrite);
        assert!(result.is_err());
        assert!(matches!(result, Err(RewriteError::SourceMismatch { .. })));
    }

    #[test]
    fn test_insert_assertion() {
        let engine = RewriteEngine::new();
        let source = "    let x = v[i];\n";
        let rewrite = make_rewrite(
            0,
            RewriteKind::InsertAssertion {
                assertion: "assert!(i < v.len(), \"index out of bounds\");".into(),
            },
        );

        let result = engine.apply_rewrite(source, &rewrite).unwrap();
        assert!(result.starts_with("    assert!(i < v.len()"));
        assert!(result.contains("let x = v[i]"));
    }

    #[test]
    fn test_offset_out_of_bounds() {
        let engine = RewriteEngine::new();
        let source = "short";
        let rewrite = make_rewrite(
            100,
            RewriteKind::InsertAttribute { attribute: "#[requires(\"true\")]".into() },
        );

        let result = engine.apply_rewrite(source, &rewrite);
        assert!(result.is_err());
        assert!(matches!(result, Err(RewriteError::OffsetOutOfBounds { .. })));
    }

    #[test]
    fn test_apply_plan_multiple_rewrites() {
        let engine = RewriteEngine::new();
        let source = "fn foo(a: u64, b: u64) -> u64 {\n    a + b\n}\n";

        let mut plan = crate::RewritePlan::new("test plan");
        // Insert attribute at start (offset 0)
        plan.rewrites.push(make_rewrite(
            0,
            RewriteKind::InsertAttribute { attribute: "#[requires(\"a + b < u64::MAX\")]".into() },
        ));
        plan.sort_for_application();

        let result = engine.apply_plan_to_source(source, &plan).unwrap();
        assert!(result.starts_with("#[requires(\"a + b < u64::MAX\")]"));
        assert!(result.contains("fn foo"));
    }

    #[test]
    fn test_apply_plan_empty() {
        let engine = RewriteEngine::new();
        let source = "fn foo() {}\n";
        let plan = crate::RewritePlan::new("empty plan");
        let result = engine.apply_plan_to_source(source, &plan).unwrap();
        assert_eq!(result, source);
    }

    #[test]
    fn test_custom_indent() {
        let engine = RewriteEngine::with_indent("\t");
        let source = "let x = 1;\n";
        let rewrite =
            make_rewrite(0, RewriteKind::InsertAssertion { assertion: "assert!(x > 0);".into() });

        let result = engine.apply_rewrite(source, &rewrite).unwrap();
        assert!(result.starts_with("\tassert!(x > 0);"));
    }

    #[test]
    fn test_replace_at_end_of_source() {
        let engine = RewriteEngine::new();
        let source = "a + b";
        let rewrite = make_rewrite(
            0,
            RewriteKind::ReplaceExpression {
                old_text: "a + b".into(),
                new_text: "a.wrapping_add(b)".into(),
            },
        );

        let result = engine.apply_rewrite(source, &rewrite).unwrap();
        assert_eq!(result, "a.wrapping_add(b)");
    }

    #[test]
    fn test_insert_at_end_of_source() {
        let engine = RewriteEngine::new();
        let source = "fn foo() {}";
        let rewrite = make_rewrite(
            source.len(),
            RewriteKind::InsertAttribute { attribute: "\n// end".into() },
        );

        let result = engine.apply_rewrite(source, &rewrite).unwrap();
        assert!(result.ends_with("\n// end\n"));
    }
}
