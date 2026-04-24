//! AST-aware source rewriting using `syn` for semantic targeting.
//!
//! Resolves rewrite targets by parsing source with `syn`, locating AST nodes,
//! and extracting byte offsets from their spans. This replaces the fragile
//! string-matching approach in `locator.rs` with structurally correct targeting
//! while preserving the existing `RewriteEngine` for actual text mutation.
//!
//! Author: Andrew Yates <andrew@andrewdyates.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};
use syn::visit::Visit;

use crate::{RewriteKind, SourceRewrite};

// ---------------------------------------------------------------------------
// Error types
// ---------------------------------------------------------------------------

/// Errors from AST-aware rewriting.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum AstRewriteError {
    /// The source file could not be parsed by syn.
    #[error("source parse error: {0}")]
    SourceParseError(String),

    /// The target function was not found in the AST.
    #[error("function `{name}` not found (occurrence {occurrence})")]
    FunctionNotFound { name: String, occurrence: usize },

    /// The function appears to be inside a macro invocation.
    #[error("function `{name}` is inside a macro and cannot be targeted")]
    FunctionInMacro { name: String },

    /// The target expression was not found in the function body.
    #[error(
        "expression `{pattern}` not found in function (occurrence {occurrence}, total matches: {total_matches})"
    )]
    ExpressionNotFound { pattern: String, occurrence: usize, total_matches: usize },

    /// The expression pattern could not be parsed by syn.
    #[error("expression pattern parse error for `{pattern}`: {error}")]
    PatternParseError { pattern: String, error: String },

    /// A statement index was out of range.
    #[error("statement index {index} out of range (function has {total} statements)")]
    StatementIndexOutOfRange { index: usize, total: usize },

    /// The rewrite produced source that does not parse.
    #[error("rewrite produced unparseable source")]
    ResultParseError,

    /// The underlying rewrite engine reported an error.
    #[error("rewrite engine error: {0}")]
    RewriteEngine(#[from] crate::RewriteError),
}

// ---------------------------------------------------------------------------
// Rewrite target types
// ---------------------------------------------------------------------------

/// A rewrite target identified by AST structure, not byte offset.
///
/// Targets are resolved against the parsed AST at application time,
/// producing byte offsets that are guaranteed to be correct for the
/// current source text.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub enum AstRewriteTarget {
    /// Insert an attribute before a function item.
    ///
    /// Resolves to the byte offset of the first token of the function item
    /// (after any doc comments, before the first attribute or visibility keyword).
    FunctionAttribute {
        fn_name: String,
        /// Which occurrence if the function name appears multiple times
        /// (e.g., in different impl blocks). 0-based.
        occurrence: usize,
    },

    /// Replace a specific expression within a function body.
    ///
    /// Uses syn's expression visitor to find the exact AST node matching
    /// the pattern, disambiguating multiple textual occurrences.
    ExpressionInFunction {
        fn_name: String,
        /// The expression to match, as a parseable Rust expression string.
        /// Matched structurally (AST equality via token stream), not textually.
        expr_pattern: String,
        /// Which occurrence of the matching expression (0-based).
        occurrence: usize,
    },

    /// Insert a statement at the beginning of a function body.
    ///
    /// Resolves to the byte offset just after the opening `{` of the
    /// function body.
    FunctionBodyStart { fn_name: String, occurrence: usize },

    /// Insert a statement before a specific statement index in a function body.
    FunctionBodyBefore { fn_name: String, stmt_index: usize, occurrence: usize },
}

/// A source rewrite identified by semantic target rather than byte offset.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SemanticRewrite {
    /// Path to the source file to modify.
    pub file_path: String,
    /// What to target in the AST.
    pub target: AstRewriteTarget,
    /// What kind of rewrite to perform.
    pub kind: RewriteKind,
    /// The function this rewrite targets.
    pub function_name: String,
    /// Human-readable rationale.
    pub rationale: String,
}

// ---------------------------------------------------------------------------
// Resolved target
// ---------------------------------------------------------------------------

/// The result of resolving an `AstRewriteTarget` against parsed source.
#[derive(Debug, Clone)]
pub(crate) struct ResolvedTarget {
    /// Byte offset for insertion or replacement start.
    pub(crate) offset: usize,
}

// ---------------------------------------------------------------------------
// Line offset table
// ---------------------------------------------------------------------------

/// Pre-computed line-offset table for converting Span positions to byte offsets.
struct LineOffsets {
    /// Byte offset of the start of each line (0-indexed in the vec,
    /// representing 1-based line numbers: offsets[0] = line 1 start).
    offsets: Vec<usize>,
}

impl LineOffsets {
    fn new(source: &str) -> Self {
        let mut offsets = vec![0];
        for (i, byte) in source.as_bytes().iter().enumerate() {
            if *byte == b'\n' {
                offsets.push(i + 1);
            }
        }
        Self { offsets }
    }

    /// Convert a line/column position to a byte offset.
    ///
    /// `line` is 1-based (as returned by `Span::start().line`).
    /// `column` is 0-based (as returned by `Span::start().column`).
    fn byte_offset(&self, line: usize, column: usize) -> usize {
        let line_start = self.offsets.get(line.saturating_sub(1)).copied().unwrap_or(0);
        line_start + column
    }
}

fn span_start_byte_offset(source: &str, span: proc_macro2::Span) -> usize {
    let table = LineOffsets::new(source);
    let start = span.start();
    table.byte_offset(start.line, start.column)
}

fn span_end_byte_offset(source: &str, span: proc_macro2::Span) -> usize {
    let table = LineOffsets::new(source);
    let end = span.end();
    table.byte_offset(end.line, end.column)
}

// ---------------------------------------------------------------------------
// Indentation preservation
// ---------------------------------------------------------------------------

/// Compute the indentation string for an insertion point.
///
/// For attribute insertion: matches the indentation of the function item.
/// For assertion insertion: matches the indentation of the containing block + one level.
#[must_use]
pub fn compute_indentation(source: &str, offset: usize, kind: &RewriteKind) -> String {
    // Find the start of the line containing `offset`
    let line_start = source[..offset].rfind('\n').map_or(0, |i| i + 1);

    // Extract leading whitespace from that line
    let base_indent: String =
        source[line_start..].chars().take_while(|c| *c == ' ' || *c == '\t').collect();

    match kind {
        RewriteKind::InsertAttribute { .. } => {
            // Attributes go at the same indentation as the function
            base_indent
        }
        RewriteKind::InsertAssertion { .. } => {
            // Assertions go inside the function body, one level deeper.
            let indent_unit = detect_indent_unit(source);
            format!("{base_indent}{indent_unit}")
        }
        RewriteKind::ReplaceExpression { .. } => {
            // Expression replacement preserves existing indentation
            base_indent
        }
    }
}

/// Detect the indentation unit used in the source (spaces vs tabs, width).
#[must_use]
pub fn detect_indent_unit(source: &str) -> &'static str {
    let mut spaces_4 = 0usize;
    let mut spaces_2 = 0usize;
    let mut tabs = 0usize;

    for line in source.lines().take(100) {
        if line.starts_with("    ") && !line.starts_with("     ") {
            spaces_4 += 1;
        } else if line.starts_with("  ") && !line.starts_with("   ") {
            spaces_2 += 1;
        } else if line.starts_with('\t') {
            tabs += 1;
        }
    }

    if tabs > spaces_4 && tabs > spaces_2 {
        "\t"
    } else if spaces_2 > spaces_4 {
        "  "
    } else {
        "    "
    }
}

// ---------------------------------------------------------------------------
// Core: resolve_target
// ---------------------------------------------------------------------------

/// Resolve a `SemanticRewrite` against parsed source to produce a `SourceRewrite`.
///
/// Parses the source file with `syn`, locates the target AST node, and
/// extracts its byte offset to produce a `SourceRewrite` that can be
/// applied by the existing `RewriteEngine`.
///
/// # Errors
///
/// Returns `AstRewriteError` if the source cannot be parsed, the target
/// cannot be found, or the expression pattern is invalid.
pub fn resolve_target(
    source: &str,
    rewrite: &SemanticRewrite,
) -> Result<SourceRewrite, AstRewriteError> {
    let file =
        syn::parse_file(source).map_err(|e| AstRewriteError::SourceParseError(e.to_string()))?;

    let resolved = resolve_target_from_ast(&file, source, &rewrite.target)?;

    Ok(SourceRewrite {
        file_path: rewrite.file_path.clone(),
        offset: resolved.offset,
        kind: rewrite.kind.clone(),
        function_name: rewrite.function_name.clone(),
        rationale: rewrite.rationale.clone(),
    })
}

/// Resolve a target against an already-parsed AST.
pub(crate) fn resolve_target_from_ast(
    file: &syn::File,
    source: &str,
    target: &AstRewriteTarget,
) -> Result<ResolvedTarget, AstRewriteError> {
    match target {
        AstRewriteTarget::FunctionAttribute { fn_name, occurrence } => {
            let offset = resolve_function_attribute(file, source, fn_name, *occurrence)?;
            Ok(ResolvedTarget { offset })
        }
        AstRewriteTarget::ExpressionInFunction { fn_name, expr_pattern, occurrence } => {
            let (start, _end) =
                resolve_expression_in_function(file, source, fn_name, expr_pattern, *occurrence)?;
            Ok(ResolvedTarget { offset: start })
        }
        AstRewriteTarget::FunctionBodyStart { fn_name, occurrence } => {
            let offset = resolve_function_body_start(file, source, fn_name, *occurrence)?;
            Ok(ResolvedTarget { offset })
        }
        AstRewriteTarget::FunctionBodyBefore { fn_name, stmt_index, occurrence } => {
            let offset =
                resolve_function_body_before(file, source, fn_name, *stmt_index, *occurrence)?;
            Ok(ResolvedTarget { offset })
        }
    }
}

// ---------------------------------------------------------------------------
// Target resolvers
// ---------------------------------------------------------------------------

/// Collected function info for target resolution.
struct FoundFn<'a> {
    attrs_span_start: Option<proc_macro2::Span>,
    /// Span of the first visible token of the function item (visibility keyword
    /// or `fn` keyword if visibility is inherited).
    item_start_span: proc_macro2::Span,
    block: &'a syn::Block,
}

/// Find the Nth occurrence of a function by name, searching both top-level
/// items and methods inside impl blocks.
fn find_function_in_ast<'a>(
    file: &'a syn::File,
    fn_name: &str,
    occurrence: usize,
) -> Result<FoundFn<'a>, AstRewriteError> {
    let mut found = 0;

    for item in &file.items {
        if let syn::Item::Fn(item_fn) = item
            && item_fn.sig.ident == fn_name
        {
            if found == occurrence {
                return Ok(FoundFn {
                    attrs_span_start: item_fn.attrs.first().map(|a| a.pound_token.span),
                    item_start_span: item_start_span_fn(&item_fn.vis, &item_fn.sig),
                    block: &item_fn.block,
                });
            }
            found += 1;
        }
        if let syn::Item::Impl(item_impl) = item {
            for impl_item in &item_impl.items {
                if let syn::ImplItem::Fn(method) = impl_item
                    && method.sig.ident == fn_name
                {
                    if found == occurrence {
                        return Ok(FoundFn {
                            attrs_span_start: method.attrs.first().map(|a| a.pound_token.span),
                            item_start_span: item_start_span_fn(&method.vis, &method.sig),
                            block: &method.block,
                        });
                    }
                    found += 1;
                }
            }
        }
    }

    Err(AstRewriteError::FunctionNotFound { name: fn_name.to_string(), occurrence })
}

/// Get the span of the first real token in a function declaration.
///
/// For `pub fn foo`, this is the span of `pub`.
/// For `fn foo` (inherited visibility), this is the span of `fn`.
fn item_start_span_fn(vis: &syn::Visibility, sig: &syn::Signature) -> proc_macro2::Span {
    use quote::ToTokens;
    // Try visibility first
    let vis_tokens: proc_macro2::TokenStream = vis.to_token_stream();
    if let Some(first) = vis_tokens.into_iter().next() {
        return first.span();
    }
    // Fall back to the fn keyword
    sig.fn_token.span
}

/// Resolve the insertion point for a function attribute.
///
/// Returns the byte offset where an attribute should be inserted -- before
/// the first existing attribute, or before the visibility/fn keyword.
fn resolve_function_attribute(
    file: &syn::File,
    source: &str,
    fn_name: &str,
    occurrence: usize,
) -> Result<usize, AstRewriteError> {
    let found = find_function_in_ast(file, fn_name, occurrence)?;

    let target_span = found.attrs_span_start.unwrap_or(found.item_start_span);

    let offset = span_start_byte_offset(source, target_span);

    // Walk back to the start of the line so the attribute gets its own line.
    let line_start = source[..offset].rfind('\n').map_or(0, |i| i + 1);
    let between = &source[line_start..offset];
    if between.chars().all(|c| c == ' ' || c == '\t') { Ok(line_start) } else { Ok(offset) }
}

/// Resolve the byte offset just after the opening `{` of a function body.
fn resolve_function_body_start(
    file: &syn::File,
    source: &str,
    fn_name: &str,
    occurrence: usize,
) -> Result<usize, AstRewriteError> {
    let found = find_function_in_ast(file, fn_name, occurrence)?;
    let brace_span = found.block.brace_token.span.open();
    let brace_offset = span_start_byte_offset(source, brace_span);
    // The insertion point is just after the `{`.
    Ok(brace_offset + 1)
}

/// Resolve the byte offset before a specific statement in a function body.
fn resolve_function_body_before(
    file: &syn::File,
    source: &str,
    fn_name: &str,
    stmt_index: usize,
    occurrence: usize,
) -> Result<usize, AstRewriteError> {
    let found = find_function_in_ast(file, fn_name, occurrence)?;

    if stmt_index >= found.block.stmts.len() {
        return Err(AstRewriteError::StatementIndexOutOfRange {
            index: stmt_index,
            total: found.block.stmts.len(),
        });
    }

    let stmt = &found.block.stmts[stmt_index];
    let stmt_span = stmt_span(stmt);
    let offset = span_start_byte_offset(source, stmt_span);

    // Walk back to line start for clean insertion.
    let line_start = source[..offset].rfind('\n').map_or(0, |i| i + 1);
    let between = &source[line_start..offset];
    if between.chars().all(|c| c == ' ' || c == '\t') { Ok(line_start) } else { Ok(offset) }
}

/// Get the span of a statement.
fn stmt_span(stmt: &syn::Stmt) -> proc_macro2::Span {
    use quote::ToTokens;
    stmt.to_token_stream()
        .into_iter()
        .next()
        .map(|t| t.span())
        .unwrap_or_else(proc_macro2::Span::call_site)
}

// ---------------------------------------------------------------------------
// Expression resolution
// ---------------------------------------------------------------------------

/// Find the byte span of a specific expression occurrence within a function.
fn resolve_expression_in_function(
    file: &syn::File,
    source: &str,
    fn_name: &str,
    expr_pattern: &str,
    occurrence: usize,
) -> Result<(usize, usize), AstRewriteError> {
    // 1. Parse the pattern as a syn::Expr
    let pattern: syn::Expr =
        syn::parse_str(expr_pattern).map_err(|e| AstRewriteError::PatternParseError {
            pattern: expr_pattern.to_string(),
            error: e.to_string(),
        })?;

    // 2. Find the function in the file
    let found = find_function_in_ast(file, fn_name, 0)?;

    // 3. Walk the function body with a visitor that matches expressions
    struct ExprFinder<'a> {
        pattern: &'a syn::Expr,
        matches: Vec<proc_macro2::Span>,
    }

    impl<'ast, 'a> Visit<'ast> for ExprFinder<'a> {
        fn visit_expr(&mut self, expr: &'ast syn::Expr) {
            if exprs_structurally_equal(expr, self.pattern) {
                self.matches.push(expr_full_span(expr));
            }
            syn::visit::visit_expr(self, expr);
        }
    }

    let mut finder = ExprFinder { pattern: &pattern, matches: Vec::new() };
    syn::visit::visit_block(&mut finder, found.block);

    // 4. Select the requested occurrence
    let span =
        finder.matches.get(occurrence).ok_or_else(|| AstRewriteError::ExpressionNotFound {
            pattern: expr_pattern.to_string(),
            occurrence,
            total_matches: finder.matches.len(),
        })?;

    let start = span_start_byte_offset(source, *span);
    let end = span_end_byte_offset(source, *span);
    Ok((start, end))
}

/// Get a span covering the full expression (from first to last token).
fn expr_full_span(expr: &syn::Expr) -> proc_macro2::Span {
    use quote::ToTokens;
    let tokens: Vec<proc_macro2::TokenTree> = expr.to_token_stream().into_iter().collect();
    match (tokens.first(), tokens.last()) {
        (Some(first), Some(last)) => first.span().join(last.span()).unwrap_or(first.span()),
        (Some(only), None) | (None, Some(only)) => only.span(),
        (None, None) => proc_macro2::Span::call_site(),
    }
}

/// Compare two expressions for structural equality, ignoring spans.
///
/// Uses the `quote::ToTokens` representation normalized to strings.
fn exprs_structurally_equal(a: &syn::Expr, b: &syn::Expr) -> bool {
    use quote::ToTokens;
    let a_tokens = a.to_token_stream().to_string();
    let b_tokens = b.to_token_stream().to_string();
    a_tokens == b_tokens
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::RewriteKind;

    // --- LineOffsets ---

    #[test]
    fn test_line_offsets_single_line() {
        let table = LineOffsets::new("hello world");
        assert_eq!(table.byte_offset(1, 0), 0);
        assert_eq!(table.byte_offset(1, 5), 5);
    }

    #[test]
    fn test_line_offsets_multi_line() {
        let source = "line1\nline2\nline3\n";
        let table = LineOffsets::new(source);
        assert_eq!(table.byte_offset(1, 0), 0); // start of line1
        assert_eq!(table.byte_offset(2, 0), 6); // start of line2
        assert_eq!(table.byte_offset(3, 0), 12); // start of line3
        assert_eq!(table.byte_offset(2, 3), 9); // "e" in "line2"
    }

    #[test]
    fn test_line_offsets_no_trailing_newline() {
        let source = "abc\ndef";
        let table = LineOffsets::new(source);
        assert_eq!(table.byte_offset(1, 0), 0);
        assert_eq!(table.byte_offset(2, 0), 4);
        assert_eq!(table.byte_offset(2, 2), 6);
    }

    // --- Indentation detection ---

    #[test]
    fn test_detect_indent_unit_4_spaces() {
        let source = "fn foo() {\n    let x = 1;\n    let y = 2;\n}\n";
        assert_eq!(detect_indent_unit(source), "    ");
    }

    #[test]
    fn test_detect_indent_unit_2_spaces() {
        let source = "fn foo() {\n  let x = 1;\n  let y = 2;\n}\n";
        assert_eq!(detect_indent_unit(source), "  ");
    }

    #[test]
    fn test_detect_indent_unit_tabs() {
        let source = "fn foo() {\n\tlet x = 1;\n\tlet y = 2;\n}\n";
        assert_eq!(detect_indent_unit(source), "\t");
    }

    #[test]
    fn test_detect_indent_unit_default_no_indentation() {
        let source = "fn foo() {}\n";
        assert_eq!(detect_indent_unit(source), "    ");
    }

    // --- Indentation computation ---

    #[test]
    fn test_compute_indentation_attribute() {
        let source = "    fn foo() {}\n";
        let indent = compute_indentation(
            source,
            4, // offset of "fn"
            &RewriteKind::InsertAttribute { attribute: "#[requires(\"x > 0\")]".into() },
        );
        assert_eq!(indent, "    ");
    }

    #[test]
    fn test_compute_indentation_assertion() {
        let source = "fn foo() {\n    let x = 1;\n}\n";
        let indent = compute_indentation(
            source,
            11, // offset of "    let"
            &RewriteKind::InsertAssertion { assertion: "assert!(x > 0);".into() },
        );
        assert_eq!(indent, "        ");
    }

    // --- Function attribute resolution ---

    #[test]
    fn test_resolve_function_attribute_simple() {
        let source = "fn foo() {}\n";
        let file = syn::parse_file(source).unwrap();
        let offset = resolve_function_attribute(&file, source, "foo", 0).unwrap();
        assert_eq!(offset, 0);
    }

    #[test]
    fn test_resolve_function_attribute_pub() {
        let source = "pub fn foo() {}\n";
        let file = syn::parse_file(source).unwrap();
        let offset = resolve_function_attribute(&file, source, "foo", 0).unwrap();
        assert_eq!(offset, 0);
    }

    #[test]
    fn test_resolve_function_attribute_with_existing_attrs() {
        let source = "#[inline]\nfn foo() {}\n";
        let file = syn::parse_file(source).unwrap();
        let offset = resolve_function_attribute(&file, source, "foo", 0).unwrap();
        assert_eq!(offset, 0);
    }

    #[test]
    fn test_resolve_function_attribute_indented() {
        let source = "impl Foo {\n    fn bar() {}\n}\n";
        let file = syn::parse_file(source).unwrap();
        let offset = resolve_function_attribute(&file, source, "bar", 0).unwrap();
        // Should point to start of the line containing "    fn bar"
        assert_eq!(&source[offset..offset + 6], "    fn");
    }

    #[test]
    fn test_resolve_function_attribute_not_found() {
        let source = "fn foo() {}\n";
        let file = syn::parse_file(source).unwrap();
        let result = resolve_function_attribute(&file, source, "bar", 0);
        assert!(matches!(result, Err(AstRewriteError::FunctionNotFound { .. })));
    }

    #[test]
    fn test_resolve_function_attribute_occurrence() {
        let source = "fn process() {}\n\nfn process() {}\n";
        let file = syn::parse_file(source).unwrap();

        let offset0 = resolve_function_attribute(&file, source, "process", 0).unwrap();
        let offset1 = resolve_function_attribute(&file, source, "process", 1).unwrap();
        assert!(offset1 > offset0);

        // Occurrence 2 should not exist
        assert!(matches!(
            resolve_function_attribute(&file, source, "process", 2),
            Err(AstRewriteError::FunctionNotFound { .. })
        ));
    }

    // --- Function body start resolution ---

    #[test]
    fn test_resolve_function_body_start() {
        let source = "fn foo() {\n    let x = 1;\n}\n";
        let file = syn::parse_file(source).unwrap();
        let offset = resolve_function_body_start(&file, source, "foo", 0).unwrap();
        // Should be right after the `{`
        assert_eq!(&source[offset - 1..offset], "{");
    }

    #[test]
    fn test_resolve_function_body_start_empty() {
        let source = "fn foo() {}\n";
        let file = syn::parse_file(source).unwrap();
        let offset = resolve_function_body_start(&file, source, "foo", 0).unwrap();
        assert_eq!(&source[offset - 1..offset], "{");
        assert_eq!(&source[offset..offset + 1], "}");
    }

    // --- Function body before resolution ---

    #[test]
    fn test_resolve_function_body_before_first_stmt() {
        let source = "fn foo() {\n    let x = 1;\n    let y = 2;\n}\n";
        let file = syn::parse_file(source).unwrap();
        let offset = resolve_function_body_before(&file, source, "foo", 0, 0).unwrap();
        // Should point to start of line with "    let x"
        assert!(source[offset..].starts_with("    let x"));
    }

    #[test]
    fn test_resolve_function_body_before_second_stmt() {
        let source = "fn foo() {\n    let x = 1;\n    let y = 2;\n}\n";
        let file = syn::parse_file(source).unwrap();
        let offset = resolve_function_body_before(&file, source, "foo", 1, 0).unwrap();
        assert!(source[offset..].starts_with("    let y"));
    }

    #[test]
    fn test_resolve_function_body_before_out_of_range() {
        let source = "fn foo() {\n    let x = 1;\n}\n";
        let file = syn::parse_file(source).unwrap();
        let result = resolve_function_body_before(&file, source, "foo", 5, 0);
        assert!(matches!(result, Err(AstRewriteError::StatementIndexOutOfRange { .. })));
    }

    // --- Expression resolution ---

    #[test]
    fn test_resolve_expression_single_match() {
        let source = "fn foo(a: u64, b: u64) -> u64 {\n    a + b\n}\n";
        let file = syn::parse_file(source).unwrap();
        let (start, end) =
            resolve_expression_in_function(&file, source, "foo", "a + b", 0).unwrap();
        assert_eq!(&source[start..end], "a + b");
    }

    #[test]
    fn test_resolve_expression_not_found() {
        let source = "fn foo(a: u64) -> u64 {\n    a * 2\n}\n";
        let file = syn::parse_file(source).unwrap();
        let result = resolve_expression_in_function(&file, source, "foo", "a + b", 0);
        assert!(matches!(
            result,
            Err(AstRewriteError::ExpressionNotFound { total_matches: 0, .. })
        ));
    }

    #[test]
    fn test_resolve_expression_pattern_parse_error() {
        let source = "fn foo() { 1 }\n";
        let file = syn::parse_file(source).unwrap();
        let result = resolve_expression_in_function(&file, source, "foo", "{{invalid", 0);
        assert!(matches!(result, Err(AstRewriteError::PatternParseError { .. })));
    }

    // --- Structural equality ---

    #[test]
    fn test_exprs_structurally_equal_same() {
        let a: syn::Expr = syn::parse_str("a + b").unwrap();
        let b: syn::Expr = syn::parse_str("a + b").unwrap();
        assert!(exprs_structurally_equal(&a, &b));
    }

    #[test]
    fn test_exprs_structurally_equal_different() {
        let a: syn::Expr = syn::parse_str("a + b").unwrap();
        let b: syn::Expr = syn::parse_str("a * b").unwrap();
        assert!(!exprs_structurally_equal(&a, &b));
    }

    #[test]
    fn test_exprs_structurally_equal_parens_differ() {
        let a: syn::Expr = syn::parse_str("a + b").unwrap();
        let b: syn::Expr = syn::parse_str("(a + b)").unwrap();
        assert!(!exprs_structurally_equal(&a, &b));
    }

    // --- End-to-end: resolve_target ---

    #[test]
    fn test_resolve_target_function_attribute() {
        let source = "fn get_midpoint(a: u64, b: u64) -> u64 {\n    (a + b) / 2\n}\n";
        let rewrite = SemanticRewrite {
            file_path: "test.rs".into(),
            target: AstRewriteTarget::FunctionAttribute {
                fn_name: "get_midpoint".into(),
                occurrence: 0,
            },
            kind: RewriteKind::InsertAttribute {
                attribute: "#[requires(\"a + b < u64::MAX\")]".into(),
            },
            function_name: "get_midpoint".into(),
            rationale: "prevent overflow".into(),
        };

        let resolved = resolve_target(source, &rewrite).unwrap();
        assert_eq!(resolved.offset, 0);
        assert_eq!(resolved.function_name, "get_midpoint");
    }

    #[test]
    fn test_resolve_target_expression_replacement() {
        let source = "fn foo(a: u64, b: u64) -> u64 {\n    a + b\n}\n";
        let rewrite = SemanticRewrite {
            file_path: "test.rs".into(),
            target: AstRewriteTarget::ExpressionInFunction {
                fn_name: "foo".into(),
                expr_pattern: "a + b".into(),
                occurrence: 0,
            },
            kind: RewriteKind::ReplaceExpression {
                old_text: "a + b".into(),
                new_text: "a.checked_add(b).unwrap()".into(),
            },
            function_name: "foo".into(),
            rationale: "safe arithmetic".into(),
        };

        let resolved = resolve_target(source, &rewrite).unwrap();
        // The offset should point to where "a + b" begins in the source
        assert_eq!(&source[resolved.offset..resolved.offset + 5], "a + b");
    }

    #[test]
    fn test_resolve_target_body_start() {
        let source = "fn foo() {\n    let x = 1;\n}\n";
        let rewrite = SemanticRewrite {
            file_path: "test.rs".into(),
            target: AstRewriteTarget::FunctionBodyStart { fn_name: "foo".into(), occurrence: 0 },
            kind: RewriteKind::InsertAssertion { assertion: "assert!(true);".into() },
            function_name: "foo".into(),
            rationale: "test".into(),
        };

        let resolved = resolve_target(source, &rewrite).unwrap();
        assert_eq!(&source[resolved.offset - 1..resolved.offset], "{");
    }

    #[test]
    fn test_resolve_target_unparseable_source() {
        let source = "fn foo( {{ broken";
        let rewrite = SemanticRewrite {
            file_path: "test.rs".into(),
            target: AstRewriteTarget::FunctionAttribute { fn_name: "foo".into(), occurrence: 0 },
            kind: RewriteKind::InsertAttribute { attribute: "#[requires(\"x\")]".into() },
            function_name: "foo".into(),
            rationale: "test".into(),
        };

        assert!(matches!(
            resolve_target(source, &rewrite),
            Err(AstRewriteError::SourceParseError(_))
        ));
    }

    // --- End-to-end: resolve + apply ---

    #[test]
    fn test_end_to_end_insert_attribute() {
        let source = "fn get_midpoint(a: u64, b: u64) -> u64 {\n    (a + b) / 2\n}\n";
        let rewrite = SemanticRewrite {
            file_path: "test.rs".into(),
            target: AstRewriteTarget::FunctionAttribute {
                fn_name: "get_midpoint".into(),
                occurrence: 0,
            },
            kind: RewriteKind::InsertAttribute {
                attribute: "#[requires(\"a + b < u64::MAX\")]".into(),
            },
            function_name: "get_midpoint".into(),
            rationale: "prevent overflow".into(),
        };

        let source_rewrite = resolve_target(source, &rewrite).unwrap();
        let engine = crate::RewriteEngine::new();
        let result = engine.apply_rewrite(source, &source_rewrite).unwrap();

        assert!(result.starts_with("#[requires(\"a + b < u64::MAX\")]"));
        assert!(result.contains("fn get_midpoint"));
        // Verify the result still parses
        syn::parse_file(&result).expect("rewritten source should parse");
    }

    #[test]
    fn test_end_to_end_insert_attribute_in_impl() {
        let source = "impl Calculator {\n    fn add(&self, a: u64, b: u64) -> u64 {\n        a + b\n    }\n}\n";
        let rewrite = SemanticRewrite {
            file_path: "test.rs".into(),
            target: AstRewriteTarget::FunctionAttribute { fn_name: "add".into(), occurrence: 0 },
            kind: RewriteKind::InsertAttribute {
                attribute: "    #[requires(\"a + b < u64::MAX\")]".into(),
            },
            function_name: "add".into(),
            rationale: "prevent overflow".into(),
        };

        let source_rewrite = resolve_target(source, &rewrite).unwrap();
        let engine = crate::RewriteEngine::new();
        let result = engine.apply_rewrite(source, &source_rewrite).unwrap();

        assert!(result.contains("#[requires(\"a + b < u64::MAX\")]"));
        assert!(result.contains("fn add"));
    }
}
