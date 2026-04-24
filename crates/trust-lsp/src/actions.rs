// trust-lsp/actions.rs: Code actions from verification diagnostics
//
// Maps tRust suggested_fix() results to LSP CodeAction responses.
// When a diagnostic has a suggested fix (e.g., "use checked_add()"),
// we produce a quickfix CodeAction with a TextEdit that replaces
// the flagged expression.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;

use trust_report::diagnostics::suggested_fix;

use crate::protocol::{
    CodeAction, CodeActionParams, Diagnostic, DiagnosticSeverity, TextEdit, WorkspaceEdit,
};

/// Build code actions for the given diagnostics in the requested document.
///
/// Produces one quickfix `CodeAction` per diagnostic that:
/// 1. Has severity Error or Warning (failed/unknown verification)
/// 2. Has a `data.kind` field we can map to a `suggested_fix()`
///
/// The code action inserts a comment with the suggested fix as a reminder,
/// since we cannot automatically rewrite arbitrary expressions without
/// full source analysis.
#[must_use]
pub(crate) fn code_actions_for_diagnostics(params: &CodeActionParams) -> Vec<CodeAction> {
    let mut actions = Vec::new();

    for diag in &params.context.diagnostics {
        // Only offer actions for Error/Warning diagnostics from tRust.
        let dominated_by_trust = diag.source.as_deref().is_some_and(|s| s == "tRust");
        if !dominated_by_trust {
            continue;
        }

        let dominated_by_severity = matches!(
            diag.severity,
            Some(DiagnosticSeverity::Error) | Some(DiagnosticSeverity::Warning)
        );
        if !dominated_by_severity {
            continue;
        }

        // Extract obligation kind from the diagnostic's structured data.
        let kind = diag.data.as_ref().and_then(|d| d.get("kind")).and_then(|k| k.as_str());

        if let Some(kind) = kind {
            let fix = suggested_fix(kind);
            let action = build_quickfix(&params.text_document.uri, diag, kind, fix);
            actions.push(action);
        }
    }

    actions
}

/// Build a single quickfix CodeAction from a diagnostic and its suggested fix.
fn build_quickfix(uri: &str, diagnostic: &Diagnostic, kind: &str, fix_text: &str) -> CodeAction {
    let title = format_action_title(kind, fix_text);

    // Insert a `// tRust: <fix>` comment on the line above the diagnostic.
    let comment_edit = TextEdit {
        range: crate::protocol::Range {
            start: crate::protocol::Position { line: diagnostic.range.start.line, character: 0 },
            end: crate::protocol::Position { line: diagnostic.range.start.line, character: 0 },
        },
        new_text: format!("// tRust: {fix_text}\n"),
    };

    let mut changes = FxHashMap::default();
    changes.insert(uri.to_string(), vec![comment_edit]);

    CodeAction {
        title,
        kind: Some("quickfix".to_string()),
        diagnostics: vec![diagnostic.clone()],
        edit: Some(WorkspaceEdit { changes: Some(changes) }),
        is_preferred: Some(true),
    }
}

/// Format a human-readable action title from the obligation kind.
fn format_action_title(kind: &str, fix_text: &str) -> String {
    // Truncate fix text for the title if it's very long.
    let short =
        if fix_text.len() > 60 { format!("{}...", &fix_text[..57]) } else { fix_text.to_string() };

    match kind {
        k if k.starts_with("arithmetic_overflow") => {
            format!("tRust fix: {short}")
        }
        "division_by_zero" | "remainder_by_zero" => {
            format!("tRust fix: {short}")
        }
        "index_out_of_bounds" | "slice_bounds_check" => {
            format!("tRust fix: {short}")
        }
        _ => format!("tRust: {short}"),
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use crate::protocol::{
        CodeActionContext, DiagnosticCode, Position, Range, TextDocumentIdentifier,
    };

    use super::*;

    fn make_diagnostic(kind: &str, severity: DiagnosticSeverity) -> Diagnostic {
        Diagnostic {
            range: Range {
                start: Position { line: 4, character: 4 },
                end: Position { line: 4, character: 9 },
            },
            severity: Some(severity),
            code: Some(DiagnosticCode::String("E-TRUST-001".to_string())),
            source: Some("tRust".to_string()),
            message: "test diagnostic".to_string(),
            tags: vec![],
            related_information: vec![],
            data: Some(serde_json::json!({
                "kind": kind,
                "solver": "z4",
                "time_ms": 5,
            })),
        }
    }

    fn make_params(diagnostics: Vec<Diagnostic>) -> CodeActionParams {
        CodeActionParams {
            text_document: TextDocumentIdentifier { uri: "file:///src/lib.rs".to_string() },
            context: CodeActionContext { diagnostics },
        }
    }

    #[test]
    fn test_code_action_for_overflow_error() {
        let diag = make_diagnostic("arithmetic_overflow_add", DiagnosticSeverity::Error);
        let params = make_params(vec![diag]);

        let actions = code_actions_for_diagnostics(&params);
        assert_eq!(actions.len(), 1);

        let action = &actions[0];
        assert!(action.title.contains("tRust fix"));
        assert!(action.title.contains("checked"));
        assert_eq!(action.kind.as_deref(), Some("quickfix"));
        assert_eq!(action.is_preferred, Some(true));
        assert!(action.edit.is_some());

        // Check the edit inserts a comment
        let edit = action.edit.as_ref().expect("edit");
        let changes = edit.changes.as_ref().expect("changes");
        let edits = &changes["file:///src/lib.rs"];
        assert_eq!(edits.len(), 1);
        assert!(edits[0].new_text.starts_with("// tRust:"));
    }

    #[test]
    fn test_code_action_for_division_by_zero() {
        let diag = make_diagnostic("division_by_zero", DiagnosticSeverity::Error);
        let params = make_params(vec![diag]);

        let actions = code_actions_for_diagnostics(&params);
        assert_eq!(actions.len(), 1);
        assert!(actions[0].title.contains("zero check"));
    }

    #[test]
    fn test_code_action_skips_information_severity() {
        let diag = make_diagnostic("arithmetic_overflow_add", DiagnosticSeverity::Information);
        let params = make_params(vec![diag]);

        let actions = code_actions_for_diagnostics(&params);
        assert!(actions.is_empty());
    }

    #[test]
    fn test_code_action_skips_non_trust_diagnostics() {
        let mut diag = make_diagnostic("arithmetic_overflow_add", DiagnosticSeverity::Error);
        diag.source = Some("rustc".to_string());
        let params = make_params(vec![diag]);

        let actions = code_actions_for_diagnostics(&params);
        assert!(actions.is_empty());
    }

    #[test]
    fn test_code_action_skips_diagnostics_without_data() {
        let mut diag = make_diagnostic("arithmetic_overflow_add", DiagnosticSeverity::Error);
        diag.data = None;
        let params = make_params(vec![diag]);

        let actions = code_actions_for_diagnostics(&params);
        assert!(actions.is_empty());
    }

    #[test]
    fn test_multiple_diagnostics_produce_multiple_actions() {
        let diag1 = make_diagnostic("arithmetic_overflow_add", DiagnosticSeverity::Error);
        let diag2 = make_diagnostic("index_out_of_bounds", DiagnosticSeverity::Warning);
        let params = make_params(vec![diag1, diag2]);

        let actions = code_actions_for_diagnostics(&params);
        assert_eq!(actions.len(), 2);
    }
}
