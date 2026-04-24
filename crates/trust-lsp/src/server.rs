// trust-lsp/server.rs: LSP server implementation
//
// Handles the LSP lifecycle (initialize/shutdown) and processes verification
// results into diagnostics. The server reads JSON-RPC messages from stdin,
// handles requests/notifications, and writes responses/notifications to stdout.
//
// New in #685:
// - textDocument/didSave handler triggers verification
// - textDocument/codeAction handler returns quickfixes
// - textDocument/inlayHint handler returns proof status per function
// - $/progress notifications during verification
// - Debounce via generation counter in VerificationState
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::io::{self, BufRead, Write};

use trust_types::JsonProofReport;

use crate::actions::code_actions_for_diagnostics;
use crate::convert::report_to_diagnostics;
use crate::inlay_hints::inlay_hints_for_report;
use crate::progress::{ProgressReporter, format_summary};
use crate::protocol::{
    CodeActionParams, DiagnosticOptions, DidSaveTextDocumentParams, InitializeParams,
    InitializeResult, InlayHintParams, Notification, Request, Response, SaveOptions,
    ServerCapabilities, ServerInfo, TextDocumentSyncKind, TextDocumentSyncOptions, error_codes,
};
use crate::transport::{TransportError, read_message, write_message};
use crate::verification::{VerificationState, run_verification};

/// Server state machine.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ServerState {
    /// Waiting for `initialize` request.
    Uninitialized,
    /// `initialize` received, waiting for `initialized` notification.
    Initializing,
    /// Ready to process requests.
    Running,
    /// `shutdown` received, waiting for `exit`.
    ShuttingDown,
}

/// The tRust LSP server.
pub(crate) struct Server<R: BufRead, W: Write> {
    reader: R,
    writer: W,
    state: ServerState,
    root_uri: Option<String>,
    /// Verification state for debounce and result caching.
    verify: VerificationState,
}

impl<R: BufRead, W: Write> Server<R, W> {
    /// Create a new server with the given reader/writer.
    pub(crate) fn new(reader: R, writer: W) -> Self {
        Self {
            reader,
            writer,
            state: ServerState::Uninitialized,
            root_uri: None,
            verify: VerificationState::new(),
        }
    }

    /// Run the server main loop until exit.
    ///
    /// Returns `Ok(())` on clean exit (after `exit` notification),
    /// or `Err` on transport/protocol errors.
    pub(crate) fn run(&mut self) -> Result<(), TransportError> {
        loop {
            let request = match read_message(&mut self.reader) {
                Ok(req) => req,
                Err(TransportError::ConnectionClosed) => return Ok(()),
                Err(e) => return Err(e),
            };

            let should_exit = self.handle_message(request)?;
            if should_exit {
                return Ok(());
            }
        }
    }

    /// Handle a single incoming message. Returns `true` if the server should exit.
    pub(crate) fn handle_message(&mut self, request: Request) -> Result<bool, TransportError> {
        match request.method.as_str() {
            "initialize" => self.handle_initialize(request)?,
            "initialized" => self.handle_initialized()?,
            "shutdown" => self.handle_shutdown(request)?,
            "exit" => return Ok(true),
            "trust/verificationResults" => self.handle_verification_results(request)?,
            "textDocument/didSave" => self.handle_did_save(request)?,
            "textDocument/codeAction" => self.handle_code_action(request)?,
            "textDocument/inlayHint" => self.handle_inlay_hint(request)?,
            _ => {
                // For uninitialized state, reject all requests.
                if self.state == ServerState::Uninitialized {
                    if let Some(id) = request.id {
                        self.send_response(Response::error(
                            Some(id),
                            error_codes::SERVER_NOT_INITIALIZED,
                            "Server not initialized".to_string(),
                        ))?;
                    }
                } else if let Some(id) = request.id {
                    // Unknown method with an id => method not found.
                    self.send_response(Response::error(
                        Some(id),
                        error_codes::METHOD_NOT_FOUND,
                        format!("Method not found: {}", request.method),
                    ))?;
                }
                // Unknown notifications are silently ignored per LSP spec.
            }
        }
        Ok(false)
    }

    /// Handle `initialize` request.
    fn handle_initialize(&mut self, request: Request) -> Result<(), TransportError> {
        if self.state != ServerState::Uninitialized {
            if let Some(id) = request.id {
                self.send_response(Response::error(
                    Some(id),
                    error_codes::INVALID_REQUEST,
                    "Server already initialized".to_string(),
                ))?;
            }
            return Ok(());
        }

        // Parse params to extract root URI.
        if let Ok(params) = serde_json::from_value::<InitializeParams>(request.params) {
            self.root_uri = params.root_uri.clone();
            self.verify.set_workspace_root(params.root_uri.as_deref());
        }

        self.state = ServerState::Initializing;

        let result = InitializeResult {
            capabilities: ServerCapabilities {
                diagnostic_provider: Some(DiagnosticOptions {
                    inter_file_dependencies: true,
                    workspace_diagnostics: true,
                }),
                text_document_sync: Some(TextDocumentSyncOptions {
                    open_close: true,
                    change: TextDocumentSyncKind::None,
                    save: Some(SaveOptions { include_text: false }),
                }),
                code_action_provider: Some(true),
                inlay_hint_provider: Some(true),
            },
            server_info: Some(ServerInfo {
                name: "trust-lsp".to_string(),
                version: Some(env!("CARGO_PKG_VERSION").to_string()),
            }),
        };

        let result_json = serde_json::to_value(result)?;
        self.send_response(Response::success(request.id, result_json))?;
        Ok(())
    }

    /// Handle `initialized` notification.
    fn handle_initialized(&mut self) -> Result<(), TransportError> {
        if self.state == ServerState::Initializing {
            self.state = ServerState::Running;
        }
        Ok(())
    }

    /// Handle `shutdown` request.
    fn handle_shutdown(&mut self, request: Request) -> Result<(), TransportError> {
        self.state = ServerState::ShuttingDown;
        self.send_response(Response::success(request.id, serde_json::Value::Null))?;
        Ok(())
    }

    /// Handle `trust/verificationResults` — custom notification carrying a
    /// `JsonProofReport` payload.
    ///
    /// Converts the report to LSP diagnostics and publishes them.
    fn handle_verification_results(&mut self, request: Request) -> Result<(), TransportError> {
        if self.state != ServerState::Running {
            return Ok(());
        }

        let report: JsonProofReport = serde_json::from_value(request.params)?;
        self.publish_report(&report)?;
        Ok(())
    }

    /// Handle `textDocument/didSave` — triggers verification for the saved file.
    ///
    /// Records the save event for debouncing, sends progress notifications,
    /// runs verification, and publishes results. If a newer save arrives
    /// before verification completes (in a threaded server), the stale
    /// result is discarded.
    fn handle_did_save(&mut self, request: Request) -> Result<(), TransportError> {
        if self.state != ServerState::Running {
            return Ok(());
        }

        let params: DidSaveTextDocumentParams = serde_json::from_value(request.params)?;
        let uri = &params.text_document.uri;
        let generation = self.verify.on_save(uri);

        // Send progress begin.
        let reporter = ProgressReporter::with_id(generation as i64);
        self.send_notification(
            "$/progress",
            reporter.begin("tRust verification", Some(&format!("Checking {uri}"))),
        )?;

        // Run verification (blocking).
        let workspace = self.verify.workspace_root().map(|p| p.to_path_buf());
        let result = workspace.as_deref().map(|root| run_verification(root, uri));

        // Check debounce: is this still the most recent save for this file?
        if !self.verify.is_current(uri, generation) {
            // A newer save superseded this one — discard results.
            self.send_notification("$/progress", reporter.end("Cancelled (newer save)"))?;
            return Ok(());
        }

        match result {
            Some(Ok(report)) => {
                // Send progress end with summary.
                let summary = &report.summary;
                let msg = format_summary(
                    summary.total_proved,
                    summary.total_failed,
                    summary.total_unknown,
                    report.metadata.total_time_ms,
                );
                self.send_notification("$/progress", reporter.end(&msg))?;

                // Store report for inlay hints and code actions.
                self.verify.set_report(uri, report.clone());

                // Publish diagnostics.
                self.publish_report(&report)?;
            }
            Some(Err(e)) => {
                self.send_notification(
                    "$/progress",
                    reporter.end(&format!("Verification error: {e}")),
                )?;
            }
            None => {
                self.send_notification("$/progress", reporter.end("No workspace root configured"))?;
            }
        }

        Ok(())
    }

    /// Handle `textDocument/codeAction` — returns quickfix actions from
    /// verification diagnostics.
    fn handle_code_action(&mut self, request: Request) -> Result<(), TransportError> {
        if self.state != ServerState::Running {
            if let Some(id) = request.id {
                self.send_response(Response::error(
                    Some(id),
                    error_codes::SERVER_NOT_INITIALIZED,
                    "Server not running".to_string(),
                ))?;
            }
            return Ok(());
        }

        let params: CodeActionParams = serde_json::from_value(request.params)?;
        let actions = code_actions_for_diagnostics(&params);
        let result = serde_json::to_value(actions)?;
        self.send_response(Response::success(request.id, result))?;
        Ok(())
    }

    /// Handle `textDocument/inlayHint` — returns per-function proof status hints.
    fn handle_inlay_hint(&mut self, request: Request) -> Result<(), TransportError> {
        if self.state != ServerState::Running {
            if let Some(id) = request.id {
                self.send_response(Response::error(
                    Some(id),
                    error_codes::SERVER_NOT_INITIALIZED,
                    "Server not running".to_string(),
                ))?;
            }
            return Ok(());
        }

        let params: InlayHintParams = serde_json::from_value(request.params)?;
        let hints = if let Some(report) = self.verify.get_report(&params.text_document.uri) {
            inlay_hints_for_report(&params, report)
        } else {
            vec![]
        };

        let result = serde_json::to_value(hints)?;
        self.send_response(Response::success(request.id, result))?;
        Ok(())
    }

    /// Convert a `JsonProofReport` to LSP diagnostics and publish them.
    pub(crate) fn publish_report(
        &mut self,
        report: &JsonProofReport,
    ) -> Result<(), TransportError> {
        let diagnostics_params = report_to_diagnostics(report);
        for params in diagnostics_params {
            self.send_notification("textDocument/publishDiagnostics", params)?;
        }
        Ok(())
    }

    /// Send a JSON-RPC response.
    fn send_response(&mut self, response: Response) -> Result<(), TransportError> {
        write_message(&mut self.writer, &response)
    }

    /// Send a JSON-RPC notification.
    fn send_notification(
        &mut self,
        method: &str,
        params: impl serde::Serialize,
    ) -> Result<(), TransportError> {
        let params_json = serde_json::to_value(params)?;
        let notif = Notification::new(method, params_json);
        write_message(&mut self.writer, &notif)
    }
}

/// Create and run a server on stdin/stdout.
///
/// This is the entry point for the `trust-lsp` binary.
pub fn run_stdio() -> Result<(), TransportError> {
    let stdin = io::stdin().lock();
    let stdout = io::stdout().lock();
    let reader = io::BufReader::new(stdin);
    let mut server = Server::new(reader, stdout);
    server.run()
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Cursor;

    fn make_lsp_message(json: &str) -> Vec<u8> {
        let body = json.as_bytes();
        let header = format!("Content-Length: {}\r\n\r\n", body.len());
        let mut msg = header.into_bytes();
        msg.extend_from_slice(body);
        msg
    }

    fn read_all_lsp_responses(output: &[u8]) -> Vec<serde_json::Value> {
        let text = std::str::from_utf8(output).expect("valid utf8");
        let mut results = Vec::new();
        let mut pos = 0;
        while pos < text.len() {
            if let Some(header_end) = text[pos..].find("\r\n\r\n") {
                let header = &text[pos..pos + header_end];
                let content_length: usize = header
                    .lines()
                    .find_map(|line| line.strip_prefix("Content-Length: "))
                    .and_then(|v| v.trim().parse().ok())
                    .expect("Content-Length");
                let body_start = pos + header_end + 4;
                let body_end = body_start + content_length;
                let body = &text[body_start..body_end];
                results.push(serde_json::from_str(body).expect("valid JSON"));
                pos = body_end;
            } else {
                break;
            }
        }
        results
    }

    #[test]
    fn test_server_initialize_lifecycle() {
        let init_req = r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"rootUri":"file:///project"}}"#;
        let initialized_notif = r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#;
        let shutdown_req = r#"{"jsonrpc":"2.0","id":2,"method":"shutdown","params":null}"#;
        let exit_notif = r#"{"jsonrpc":"2.0","method":"exit","params":null}"#;

        let mut input = make_lsp_message(init_req);
        input.extend_from_slice(&make_lsp_message(initialized_notif));
        input.extend_from_slice(&make_lsp_message(shutdown_req));
        input.extend_from_slice(&make_lsp_message(exit_notif));

        let reader = io::BufReader::new(Cursor::new(input));
        let mut output = Vec::new();
        let mut server = Server::new(reader, &mut output);

        server.run().expect("server should run cleanly");
        assert_eq!(server.state, ServerState::ShuttingDown);

        let responses = read_all_lsp_responses(&output);
        assert_eq!(responses.len(), 2); // initialize response + shutdown response

        // Initialize response
        let init_resp = &responses[0];
        assert_eq!(init_resp["id"], 1);
        assert!(init_resp["result"]["capabilities"]["diagnosticProvider"].is_object());
        assert_eq!(init_resp["result"]["serverInfo"]["name"], "trust-lsp");

        // New capabilities advertised
        assert_eq!(init_resp["result"]["capabilities"]["codeActionProvider"], true);
        assert_eq!(init_resp["result"]["capabilities"]["inlayHintProvider"], true);
        assert!(init_resp["result"]["capabilities"]["textDocumentSync"]["save"].is_object());

        // Shutdown response
        let shutdown_resp = &responses[1];
        assert_eq!(shutdown_resp["id"], 2);
        assert!(shutdown_resp["result"].is_null());
    }

    #[test]
    fn test_server_rejects_before_initialize() {
        let req = r#"{"jsonrpc":"2.0","id":1,"method":"textDocument/didOpen","params":{}}"#;
        let exit = r#"{"jsonrpc":"2.0","method":"exit","params":null}"#;

        let mut input = make_lsp_message(req);
        input.extend_from_slice(&make_lsp_message(exit));

        let reader = io::BufReader::new(Cursor::new(input));
        let mut output = Vec::new();
        let mut server = Server::new(reader, &mut output);

        server.run().expect("server should exit on exit notification");

        let responses = read_all_lsp_responses(&output);
        assert_eq!(responses.len(), 1);
        assert!(responses[0]["error"].is_object());
        assert_eq!(responses[0]["error"]["code"], error_codes::SERVER_NOT_INITIALIZED);
    }

    #[test]
    fn test_server_method_not_found() {
        let init_req = r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"#;
        let initialized = r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#;
        let unknown = r#"{"jsonrpc":"2.0","id":2,"method":"foo/bar","params":{}}"#;
        let exit = r#"{"jsonrpc":"2.0","method":"exit","params":null}"#;

        let mut input = make_lsp_message(init_req);
        input.extend_from_slice(&make_lsp_message(initialized));
        input.extend_from_slice(&make_lsp_message(unknown));
        input.extend_from_slice(&make_lsp_message(exit));

        let reader = io::BufReader::new(Cursor::new(input));
        let mut output = Vec::new();
        let mut server = Server::new(reader, &mut output);

        server.run().expect("server should run");

        let responses = read_all_lsp_responses(&output);
        assert_eq!(responses.len(), 2); // init response + method not found

        assert!(responses[1]["error"].is_object());
        assert_eq!(responses[1]["error"]["code"], error_codes::METHOD_NOT_FOUND);
    }

    #[test]
    fn test_server_publish_report() {
        use trust_types::*;

        let init_req = r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"#;
        let initialized = r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#;

        let report = JsonProofReport {
            metadata: ReportMetadata {
                schema_version: "1.0".to_string(),
                trust_version: "0.1.0".to_string(),
                timestamp: "2026-01-01T00:00:00Z".to_string(),
                total_time_ms: 10,
            },
            crate_name: "test".to_string(),
            summary: CrateSummary {
                functions_analyzed: 1,
                functions_verified: 0,
                functions_runtime_checked: 0,
                functions_with_violations: 1,
                functions_inconclusive: 0,
                total_obligations: 1,
                total_proved: 0,
                total_runtime_checked: 0,
                total_failed: 1,
                total_unknown: 0,
                verdict: CrateVerdict::HasViolations,
            },
            functions: vec![FunctionProofReport {
                function: "bad_fn".into(),
                summary: FunctionSummary {
                    total_obligations: 1,
                    proved: 0,
                    runtime_checked: 0,
                    failed: 1,
                    unknown: 0,
                    total_time_ms: 5,
                    max_proof_level: Some(ProofLevel::L0Safety),
                    verdict: FunctionVerdict::HasViolations,
                },
                obligations: vec![ObligationReport {
                    description: "overflow".to_string(),
                    kind: "arithmetic_overflow_add".to_string(),
                    proof_level: ProofLevel::L0Safety,
                    location: Some(SourceSpan {
                        file: "src/lib.rs".to_string(),
                        line_start: 5,
                        col_start: 5,
                        line_end: 5,
                        col_end: 10,
                    }),
                    outcome: ObligationOutcome::Failed { counterexample: None },
                    solver: "z4".into(),
                    time_ms: 5,
                    evidence: None,
                }],
            }],
        };

        let report_json = serde_json::to_string(&report).expect("serialize report");
        let verify_notif = format!(
            r#"{{"jsonrpc":"2.0","method":"trust/verificationResults","params":{report_json}}}"#
        );
        let exit = r#"{"jsonrpc":"2.0","method":"exit","params":null}"#;

        let mut input = make_lsp_message(init_req);
        input.extend_from_slice(&make_lsp_message(initialized));
        input.extend_from_slice(&make_lsp_message(&verify_notif));
        input.extend_from_slice(&make_lsp_message(exit));

        let reader = io::BufReader::new(Cursor::new(input));
        let mut output = Vec::new();
        let mut server = Server::new(reader, &mut output);

        server.run().expect("server should run");

        let responses = read_all_lsp_responses(&output);
        // 1 init response + 1 publishDiagnostics notification
        assert_eq!(responses.len(), 2);

        let diag_notif = &responses[1];
        assert_eq!(diag_notif["method"], "textDocument/publishDiagnostics");
        let diags = &diag_notif["params"]["diagnostics"];
        assert_eq!(diags.as_array().expect("array").len(), 1);
        assert_eq!(diags[0]["severity"], 1); // Error
        assert!(diags[0]["message"].as_str().unwrap().contains("overflow"));
        assert_eq!(diags[0]["source"], "tRust");
    }

    #[test]
    fn test_server_double_initialize_rejected() {
        let init1 = r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"#;
        let init2 = r#"{"jsonrpc":"2.0","id":2,"method":"initialize","params":{}}"#;
        let exit = r#"{"jsonrpc":"2.0","method":"exit","params":null}"#;

        let mut input = make_lsp_message(init1);
        input.extend_from_slice(&make_lsp_message(init2));
        input.extend_from_slice(&make_lsp_message(exit));

        let reader = io::BufReader::new(Cursor::new(input));
        let mut output = Vec::new();
        let mut server = Server::new(reader, &mut output);

        server.run().expect("server should run");

        let responses = read_all_lsp_responses(&output);
        assert_eq!(responses.len(), 2);

        // First init succeeds
        assert!(responses[0]["result"].is_object());

        // Second init fails
        assert!(responses[1]["error"].is_object());
        assert_eq!(responses[1]["error"]["code"], error_codes::INVALID_REQUEST);
    }

    #[test]
    fn test_server_code_action_returns_actions() {
        let init_req = r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"#;
        let initialized = r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#;
        let code_action_req = r#"{
            "jsonrpc":"2.0","id":3,"method":"textDocument/codeAction",
            "params":{
                "textDocument":{"uri":"file:///src/lib.rs"},
                "range":{"start":{"line":4,"character":0},"end":{"line":4,"character":10}},
                "context":{
                    "diagnostics":[{
                        "range":{"start":{"line":4,"character":4},"end":{"line":4,"character":9}},
                        "severity":1,
                        "code":"E-TRUST-001",
                        "source":"tRust",
                        "message":"overflow",
                        "data":{"kind":"arithmetic_overflow_add","solver":"z4","time_ms":5}
                    }]
                }
            }
        }"#;
        let exit = r#"{"jsonrpc":"2.0","method":"exit","params":null}"#;

        let mut input = make_lsp_message(init_req);
        input.extend_from_slice(&make_lsp_message(initialized));
        input.extend_from_slice(&make_lsp_message(code_action_req));
        input.extend_from_slice(&make_lsp_message(exit));

        let reader = io::BufReader::new(Cursor::new(input));
        let mut output = Vec::new();
        let mut server = Server::new(reader, &mut output);

        server.run().expect("server should run");

        let responses = read_all_lsp_responses(&output);
        // init response + code action response
        assert!(responses.len() >= 2);

        // Find the code action response (id=3)
        let ca_resp = responses.iter().find(|r| r["id"] == 3).expect("code action response");
        let result = ca_resp["result"].as_array().expect("array");
        assert_eq!(result.len(), 1);
        assert!(result[0]["title"].as_str().unwrap().contains("tRust fix"));
        assert_eq!(result[0]["kind"], "quickfix");
    }

    #[test]
    fn test_server_inlay_hint_empty_without_report() {
        let init_req = r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"#;
        let initialized = r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#;
        let hint_req = r#"{
            "jsonrpc":"2.0","id":4,"method":"textDocument/inlayHint",
            "params":{
                "textDocument":{"uri":"file:///src/lib.rs"},
                "range":{"start":{"line":0,"character":0},"end":{"line":50,"character":0}}
            }
        }"#;
        let exit = r#"{"jsonrpc":"2.0","method":"exit","params":null}"#;

        let mut input = make_lsp_message(init_req);
        input.extend_from_slice(&make_lsp_message(initialized));
        input.extend_from_slice(&make_lsp_message(hint_req));
        input.extend_from_slice(&make_lsp_message(exit));

        let reader = io::BufReader::new(Cursor::new(input));
        let mut output = Vec::new();
        let mut server = Server::new(reader, &mut output);

        server.run().expect("server should run");

        let responses = read_all_lsp_responses(&output);
        let hint_resp = responses.iter().find(|r| r["id"] == 4).expect("hint response");
        let result = hint_resp["result"].as_array().expect("array");
        assert!(result.is_empty()); // No report stored yet
    }

    #[test]
    fn test_server_did_save_sends_progress() {
        // didSave without a workspace root should still send progress notifications.
        let init_req = r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"#;
        let initialized = r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#;
        let save_notif = r#"{"jsonrpc":"2.0","method":"textDocument/didSave","params":{"textDocument":{"uri":"file:///src/lib.rs"}}}"#;
        let exit = r#"{"jsonrpc":"2.0","method":"exit","params":null}"#;

        let mut input = make_lsp_message(init_req);
        input.extend_from_slice(&make_lsp_message(initialized));
        input.extend_from_slice(&make_lsp_message(save_notif));
        input.extend_from_slice(&make_lsp_message(exit));

        let reader = io::BufReader::new(Cursor::new(input));
        let mut output = Vec::new();
        let mut server = Server::new(reader, &mut output);

        server.run().expect("server should run");

        let responses = read_all_lsp_responses(&output);
        // init response + progress begin + progress end (no workspace root)
        assert!(responses.len() >= 3);

        // Find progress notifications
        let progress_msgs: Vec<_> =
            responses.iter().filter(|r| r["method"] == "$/progress").collect();
        assert_eq!(progress_msgs.len(), 2); // begin + end

        let begin = &progress_msgs[0]["params"]["value"];
        assert_eq!(begin["kind"], "begin");
        assert_eq!(begin["title"], "tRust verification");

        let end = &progress_msgs[1]["params"]["value"];
        assert_eq!(end["kind"], "end");
        assert!(end["message"].as_str().unwrap().contains("No workspace root"));
    }
}
