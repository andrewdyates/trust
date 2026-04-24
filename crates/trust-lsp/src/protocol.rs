// trust-lsp/protocol.rs: LSP protocol types for JSON-RPC 2.0
//
// Minimal LSP protocol types sufficient for verification diagnostics.
// No external LSP crate dependency — just serde_json over stdin/stdout.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};
use trust_types::fx::FxHashMap;

// ---------------------------------------------------------------------------
// JSON-RPC 2.0 transport
// ---------------------------------------------------------------------------

/// A JSON-RPC 2.0 request message.
#[derive(Debug, Clone, Deserialize)]
pub(crate) struct Request {
    pub(crate) id: Option<RequestId>,
    pub(crate) method: String,
    #[serde(default)]
    pub(crate) params: serde_json::Value,
}

/// A JSON-RPC 2.0 response message.
#[derive(Debug, Clone, Serialize)]
pub(crate) struct Response {
    pub(crate) jsonrpc: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(crate) id: Option<RequestId>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(crate) result: Option<serde_json::Value>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(crate) error: Option<ResponseError>,
}

impl Response {
    /// Create a success response.
    #[must_use]
    pub(crate) fn success(id: Option<RequestId>, result: serde_json::Value) -> Self {
        Self { jsonrpc: "2.0".to_string(), id, result: Some(result), error: None }
    }

    /// Create an error response.
    #[must_use]
    pub(crate) fn error(id: Option<RequestId>, code: i32, message: String) -> Self {
        Self {
            jsonrpc: "2.0".to_string(),
            id,
            result: None,
            error: Some(ResponseError { code, message, data: None }),
        }
    }
}

/// A JSON-RPC 2.0 notification (no id, no response expected).
#[derive(Debug, Clone, Serialize)]
pub(crate) struct Notification {
    pub(crate) jsonrpc: String,
    pub(crate) method: String,
    pub(crate) params: serde_json::Value,
}

impl Notification {
    /// Create a notification.
    #[must_use]
    pub(crate) fn new(method: &str, params: serde_json::Value) -> Self {
        Self { jsonrpc: "2.0".to_string(), method: method.to_string(), params }
    }
}

/// JSON-RPC request ID (integer or string).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(untagged)]
pub(crate) enum RequestId {
    Integer(i64),
    String(String),
}

/// JSON-RPC error object.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct ResponseError {
    pub(crate) code: i32,
    pub(crate) message: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(crate) data: Option<serde_json::Value>,
}

// ---------------------------------------------------------------------------
// LSP error codes
// ---------------------------------------------------------------------------

/// Standard JSON-RPC error codes used by LSP.
pub(crate) mod error_codes {
    pub(crate) const INVALID_REQUEST: i32 = -32600;
    pub(crate) const METHOD_NOT_FOUND: i32 = -32601;
    pub(crate) const SERVER_NOT_INITIALIZED: i32 = -32002;
}

// ---------------------------------------------------------------------------
// LSP capability types (minimal subset)
// ---------------------------------------------------------------------------

/// LSP InitializeParams (minimal).
#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct InitializeParams {
    #[serde(default)]
    pub(crate) root_uri: Option<String>,
}

/// LSP InitializeResult.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct InitializeResult {
    pub(crate) capabilities: ServerCapabilities,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(crate) server_info: Option<ServerInfo>,
}

/// LSP ServerCapabilities.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct ServerCapabilities {
    /// We provide diagnostics via push notifications.
    pub(crate) diagnostic_provider: Option<DiagnosticOptions>,
    /// Text document sync for open/close/change/save notifications.
    pub(crate) text_document_sync: Option<TextDocumentSyncOptions>,
    /// Code action provider (quick fixes from verification diagnostics).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(crate) code_action_provider: Option<bool>,
    /// Inlay hint provider (per-function proof status).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(crate) inlay_hint_provider: Option<bool>,
}

/// LSP DiagnosticOptions.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct DiagnosticOptions {
    pub(crate) inter_file_dependencies: bool,
    pub(crate) workspace_diagnostics: bool,
}

/// LSP TextDocumentSyncOptions.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct TextDocumentSyncOptions {
    pub(crate) open_close: bool,
    pub(crate) change: TextDocumentSyncKind,
    /// Whether the server wants save notifications.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(crate) save: Option<SaveOptions>,
}

/// LSP SaveOptions.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct SaveOptions {
    /// Whether the client should include the file content on save.
    #[serde(default)]
    pub(crate) include_text: bool,
}

/// LSP TextDocumentSyncKind (serializes as integer per LSP spec).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub(crate) enum TextDocumentSyncKind {
    None = 0,
    Full = 1,
}

impl Serialize for TextDocumentSyncKind {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_u8(*self as u8)
    }
}

impl<'de> Deserialize<'de> for TextDocumentSyncKind {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let value = u8::deserialize(deserializer)?;
        match value {
            0 => Ok(Self::None),
            1 => Ok(Self::Full),
            _ => Err(serde::de::Error::custom(format!("invalid TextDocumentSyncKind: {value}"))),
        }
    }
}

/// LSP ServerInfo.
#[derive(Debug, Clone, Serialize)]
pub(crate) struct ServerInfo {
    pub(crate) name: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(crate) version: Option<String>,
}

// ---------------------------------------------------------------------------
// LSP Diagnostic types
// ---------------------------------------------------------------------------

/// LSP PublishDiagnosticsParams.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct PublishDiagnosticsParams {
    /// The URI for which diagnostic information is reported.
    pub(crate) uri: String,
    /// The list of reported diagnostics.
    pub(crate) diagnostics: Vec<Diagnostic>,
    /// Optional document version.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(crate) version: Option<i32>,
}

/// LSP Diagnostic.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
#[serde(rename_all = "camelCase")]
pub(crate) struct Diagnostic {
    /// The range at which the message applies.
    pub(crate) range: Range,
    /// The diagnostic's severity.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(crate) severity: Option<DiagnosticSeverity>,
    /// The diagnostic's code.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(crate) code: Option<DiagnosticCode>,
    /// The source of this diagnostic (always "tRust").
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(crate) source: Option<String>,
    /// The diagnostic's message.
    pub(crate) message: String,
    /// Additional metadata tags.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub(crate) tags: Vec<DiagnosticTag>,
    /// Related diagnostic information.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub(crate) related_information: Vec<DiagnosticRelatedInformation>,
    /// Machine-readable structured data.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(crate) data: Option<serde_json::Value>,
}

/// LSP DiagnosticSeverity (serializes as integer per LSP spec).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub(crate) enum DiagnosticSeverity {
    Error = 1,
    Warning = 2,
    Information = 3,
    Hint = 4,
}

impl Serialize for DiagnosticSeverity {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_u8(*self as u8)
    }
}

impl<'de> Deserialize<'de> for DiagnosticSeverity {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let value = u8::deserialize(deserializer)?;
        match value {
            1 => Ok(Self::Error),
            2 => Ok(Self::Warning),
            3 => Ok(Self::Information),
            4 => Ok(Self::Hint),
            _ => Err(serde::de::Error::custom(format!("invalid DiagnosticSeverity: {value}"))),
        }
    }
}

/// LSP diagnostic code (string or integer).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(untagged)]
pub(crate) enum DiagnosticCode {
    Integer(i32),
    String(String),
}

/// LSP DiagnosticTag (serializes as integer per LSP spec).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub(crate) enum DiagnosticTag {
    Unnecessary = 1,
    Deprecated = 2,
}

impl Serialize for DiagnosticTag {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_u8(*self as u8)
    }
}

impl<'de> Deserialize<'de> for DiagnosticTag {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let value = u8::deserialize(deserializer)?;
        match value {
            1 => Ok(Self::Unnecessary),
            2 => Ok(Self::Deprecated),
            _ => Err(serde::de::Error::custom(format!("invalid DiagnosticTag: {value}"))),
        }
    }
}

/// LSP Range (0-based line/character).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Range {
    pub(crate) start: Position,
    pub(crate) end: Position,
}

/// LSP Position (0-based).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Position {
    pub(crate) line: u32,
    pub(crate) character: u32,
}

/// LSP DiagnosticRelatedInformation.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub(crate) struct DiagnosticRelatedInformation {
    pub(crate) location: Location,
    pub(crate) message: String,
}

/// LSP Location.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub(crate) struct Location {
    pub(crate) uri: String,
    pub(crate) range: Range,
}

// ---------------------------------------------------------------------------
// textDocument/didSave
// ---------------------------------------------------------------------------

/// LSP TextDocumentIdentifier.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct TextDocumentIdentifier {
    pub(crate) uri: String,
}

/// LSP DidSaveTextDocumentParams.
#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct DidSaveTextDocumentParams {
    /// The document that was saved.
    pub(crate) text_document: TextDocumentIdentifier,
}

// ---------------------------------------------------------------------------
// textDocument/codeAction
// ---------------------------------------------------------------------------

/// LSP CodeActionParams.
#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct CodeActionParams {
    /// The document in which the command was invoked.
    pub(crate) text_document: TextDocumentIdentifier,
    /// Context carrying additional information.
    pub(crate) context: CodeActionContext,
}

/// LSP CodeActionContext.
#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct CodeActionContext {
    /// The diagnostics the editor provides for the code action request.
    pub(crate) diagnostics: Vec<Diagnostic>,
}

/// LSP CodeAction.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct CodeAction {
    /// A short, human-readable title.
    pub(crate) title: String,
    /// The kind of the code action (e.g., "quickfix").
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(crate) kind: Option<String>,
    /// The diagnostics this action resolves.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub(crate) diagnostics: Vec<Diagnostic>,
    /// The workspace edit to apply.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(crate) edit: Option<WorkspaceEdit>,
    /// Whether this is a preferred action for the given diagnostics.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(crate) is_preferred: Option<bool>,
}

/// LSP WorkspaceEdit.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct WorkspaceEdit {
    /// Map of document URI to text edits.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(crate) changes: Option<FxHashMap<String, Vec<TextEdit>>>,
}

/// LSP TextEdit.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct TextEdit {
    /// The range of the text document to be manipulated.
    pub(crate) range: Range,
    /// The string to be inserted.
    pub(crate) new_text: String,
}

// ---------------------------------------------------------------------------
// textDocument/inlayHint
// ---------------------------------------------------------------------------

/// LSP InlayHintParams.
#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct InlayHintParams {
    /// The document to request inlay hints for.
    pub(crate) text_document: TextDocumentIdentifier,
    /// The visible range for which inlay hints should be computed.
    pub(crate) range: Range,
}

/// LSP InlayHint.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct InlayHint {
    /// The position of this hint.
    pub(crate) position: Position,
    /// The label (string or structured).
    pub(crate) label: String,
    /// The kind of this hint (Type=1, Parameter=2). We omit for custom hints.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(crate) kind: Option<u8>,
    /// Optional tooltip (markdown or plaintext).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(crate) tooltip: Option<String>,
    /// Whether the hint is padded on the left.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(crate) padding_left: Option<bool>,
    /// Whether the hint is padded on the right.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(crate) padding_right: Option<bool>,
}

// ---------------------------------------------------------------------------
// $/progress (work done)
// ---------------------------------------------------------------------------

/// LSP ProgressParams.
#[derive(Debug, Clone, Serialize)]
pub(crate) struct ProgressParams {
    /// The progress token provided by the client or server.
    pub(crate) token: ProgressToken,
    /// The progress data.
    pub(crate) value: WorkDoneProgress,
}

/// LSP ProgressToken.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(untagged)]
pub(crate) enum ProgressToken {
    Integer(i64),
    String(String),
}

/// LSP WorkDoneProgress — tagged by `kind`.
#[derive(Debug, Clone, Serialize)]
#[serde(tag = "kind", rename_all = "camelCase")]
pub(crate) enum WorkDoneProgress {
    Begin {
        title: String,
        #[serde(skip_serializing_if = "Option::is_none")]
        message: Option<String>,
        #[serde(skip_serializing_if = "Option::is_none")]
        percentage: Option<u32>,
        #[serde(skip_serializing_if = "Option::is_none")]
        cancellable: Option<bool>,
    },
    End {
        #[serde(skip_serializing_if = "Option::is_none")]
        message: Option<String>,
    },
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_request_id_integer_deserialize() {
        let json = r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"#;
        let req: Request = serde_json::from_str(json).expect("parse request");
        assert_eq!(req.id, Some(RequestId::Integer(1)));
        assert_eq!(req.method, "initialize");
    }

    #[test]
    fn test_request_id_string_deserialize() {
        let json = r#"{"jsonrpc":"2.0","id":"abc","method":"shutdown","params":null}"#;
        let req: Request = serde_json::from_str(json).expect("parse request");
        assert_eq!(req.id, Some(RequestId::String("abc".to_string())));
    }

    #[test]
    fn test_notification_no_id() {
        let json = r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#;
        let req: Request = serde_json::from_str(json).expect("parse notification as request");
        assert!(req.id.is_none());
        assert_eq!(req.method, "initialized");
    }

    #[test]
    fn test_response_success_serialize() {
        let resp =
            Response::success(Some(RequestId::Integer(1)), serde_json::json!({"capabilities": {}}));
        let json = serde_json::to_string(&resp).expect("serialize response");
        assert!(json.contains("\"jsonrpc\":\"2.0\""));
        assert!(json.contains("\"id\":1"));
        assert!(json.contains("\"result\""));
        assert!(!json.contains("\"error\""));
    }

    #[test]
    fn test_response_error_serialize() {
        let resp = Response::error(
            Some(RequestId::Integer(1)),
            error_codes::METHOD_NOT_FOUND,
            "not found".into(),
        );
        let json = serde_json::to_string(&resp).expect("serialize error response");
        assert!(json.contains("\"error\""));
        assert!(json.contains("-32601"));
        assert!(!json.contains("\"result\""));
    }

    #[test]
    fn test_diagnostic_severity_values() {
        assert_eq!(DiagnosticSeverity::Error as u8, 1);
        assert_eq!(DiagnosticSeverity::Warning as u8, 2);
        assert_eq!(DiagnosticSeverity::Information as u8, 3);
        assert_eq!(DiagnosticSeverity::Hint as u8, 4);
    }

    #[test]
    fn test_diagnostic_serialize_roundtrip() {
        let diag = Diagnostic {
            range: Range {
                start: Position { line: 4, character: 4 },
                end: Position { line: 4, character: 9 },
            },
            severity: Some(DiagnosticSeverity::Error),
            code: Some(DiagnosticCode::String("E-TRUST-001".to_string())),
            source: Some("tRust".to_string()),
            message: "possible arithmetic overflow".to_string(),
            tags: vec![],
            related_information: vec![],
            data: None,
        };

        let json = serde_json::to_string(&diag).expect("serialize");
        let parsed: Diagnostic = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(parsed, diag);
    }

    #[test]
    fn test_publish_diagnostics_params_serialize() {
        let params = PublishDiagnosticsParams {
            uri: "file:///src/midpoint.rs".to_string(),
            diagnostics: vec![],
            version: None,
        };
        let json = serde_json::to_string(&params).expect("serialize");
        assert!(json.contains("\"uri\":\"file:///src/midpoint.rs\""));
        assert!(json.contains("\"diagnostics\":[]"));
    }

    #[test]
    fn test_notification_new() {
        let notif = Notification::new("textDocument/publishDiagnostics", serde_json::json!({}));
        assert_eq!(notif.method, "textDocument/publishDiagnostics");
        assert_eq!(notif.jsonrpc, "2.0");
    }

    #[test]
    fn test_did_save_params_deserialize() {
        let json = r#"{"textDocument":{"uri":"file:///src/lib.rs"}}"#;
        let params: DidSaveTextDocumentParams = serde_json::from_str(json).expect("parse");
        assert_eq!(params.text_document.uri, "file:///src/lib.rs");
    }

    #[test]
    fn test_did_save_params_with_text() {
        let json = r#"{"textDocument":{"uri":"file:///src/lib.rs"},"text":"fn main() {}"}"#;
        let params: DidSaveTextDocumentParams = serde_json::from_str(json).expect("parse");
        assert_eq!(params.text_document.uri, "file:///src/lib.rs");
    }

    #[test]
    fn test_code_action_serialize() {
        let action = CodeAction {
            title: "Replace with checked_add".to_string(),
            kind: Some("quickfix".to_string()),
            diagnostics: vec![],
            edit: None,
            is_preferred: Some(true),
        };
        let json = serde_json::to_string(&action).expect("serialize");
        assert!(json.contains("\"title\":\"Replace with checked_add\""));
        assert!(json.contains("\"kind\":\"quickfix\""));
        assert!(json.contains("\"isPreferred\":true"));
    }

    #[test]
    fn test_inlay_hint_serialize() {
        let hint = InlayHint {
            position: Position { line: 3, character: 0 },
            label: "proved".to_string(),
            kind: None,
            tooltip: Some("All 3 obligations proved safe".to_string()),
            padding_left: Some(true),
            padding_right: None,
        };
        let json = serde_json::to_string(&hint).expect("serialize");
        assert!(json.contains("\"label\":\"proved\""));
        assert!(json.contains("\"paddingLeft\":true"));
    }

    #[test]
    fn test_work_done_progress_begin_serialize() {
        let progress = WorkDoneProgress::Begin {
            title: "tRust verification".to_string(),
            message: Some("Checking src/lib.rs".to_string()),
            percentage: Some(0),
            cancellable: Some(true),
        };
        let json = serde_json::to_string(&progress).expect("serialize");
        assert!(json.contains("\"kind\":\"begin\""));
        assert!(json.contains("\"title\":\"tRust verification\""));
        assert!(json.contains("\"percentage\":0"));
    }

    #[test]
    fn test_work_done_progress_end_serialize() {
        let progress = WorkDoneProgress::End { message: Some("Verification complete".to_string()) };
        let json = serde_json::to_string(&progress).expect("serialize");
        assert!(json.contains("\"kind\":\"end\""));
        assert!(json.contains("\"Verification complete\""));
    }

    #[test]
    fn test_code_action_params_deserialize() {
        let json = r#"{
            "textDocument": {"uri": "file:///src/lib.rs"},
            "range": {"start": {"line": 4, "character": 0}, "end": {"line": 4, "character": 10}},
            "context": {"diagnostics": []}
        }"#;
        let params: CodeActionParams = serde_json::from_str(json).expect("parse");
        assert_eq!(params.text_document.uri, "file:///src/lib.rs");
        assert!(params.context.diagnostics.is_empty());
    }

    #[test]
    fn test_inlay_hint_params_deserialize() {
        let json = r#"{
            "textDocument": {"uri": "file:///src/lib.rs"},
            "range": {"start": {"line": 0, "character": 0}, "end": {"line": 50, "character": 0}}
        }"#;
        let params: InlayHintParams = serde_json::from_str(json).expect("parse");
        assert_eq!(params.text_document.uri, "file:///src/lib.rs");
        assert_eq!(params.range.end.line, 50);
    }
}
