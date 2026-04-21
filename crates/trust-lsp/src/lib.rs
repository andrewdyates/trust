#![allow(dead_code)]
//! trust-lsp: LSP server for tRust verification diagnostics
//!
//! Provides real-time verification feedback in VS Code / Neovim via the
//! Language Server Protocol. Converts tRust verification results (from
//! `JsonProofReport`) into LSP Diagnostic messages with:
//!
//!   - Red squiggle on failed verifications (e.g., ArithmeticOverflow counterexample)
//!   - Yellow squiggle on unknown/timeout results
//!   - Green information on proved-safe properties (e.g., "Proved safe by z4 (5ms)")
//!   - Inline counterexample values and suggested fixes
//!   - Code actions with quickfix suggestions from `suggested_fix()`
//!   - Inlay hints showing per-function proof status (proved/failed/unknown)
//!   - $/progress notifications during verification runs
//!   - On-save verification with debounce (cancel-on-new-save)
//!
//! ## Architecture
//!
//! - `protocol` — LSP protocol types (JSON-RPC 2.0, Diagnostic, Range, etc.)
//! - `transport` — Content-Length framed stdin/stdout transport
//! - `convert` — tRust `ObligationReport` -> LSP `Diagnostic` conversion
//! - `actions` — Code actions from verification diagnostics (quickfixes)
//! - `inlay_hints` — Per-function proof status inlay hints
//! - `progress` — $/progress notification helpers for verification runs
//! - `verification` — On-save verification runner with debounce state
//! - `server` — LSP lifecycle and message dispatch
//!
//! ## Custom Methods
//!
//! - `trust/verificationResults` — notification carrying a `JsonProofReport`
//!   payload. The server converts it to `textDocument/publishDiagnostics`.
//!
//! ## Usage
//!
//! ```bash
//! # Run as LSP server (stdin/stdout)
//! trust-lsp
//!
//! # Pipe verification results
//! cargo trust check --json | trust-lsp --stdin-report
//! ```
//!
//! Author: Andrew Yates <andrew@andrewdyates.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

pub(crate) mod actions;
pub(crate) mod convert;
pub(crate) mod inlay_hints;
pub(crate) mod progress;
pub(crate) mod protocol;
pub mod server;
pub mod transport;
pub(crate) mod verification;
