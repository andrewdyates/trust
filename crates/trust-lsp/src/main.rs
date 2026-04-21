// trust-lsp: LSP server binary entry point
//
// Runs the tRust verification LSP server on stdin/stdout.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn main() {
    if let Err(e) = trust_lsp::server::run_stdio() {
        eprintln!("trust-lsp error: {e}");
        std::process::exit(1);
    }
}
