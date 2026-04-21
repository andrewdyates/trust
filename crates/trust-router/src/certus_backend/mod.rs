// trust-router/certus_backend/mod.rs: Ownership-aware verification backend via certus subprocess
//
// Invokes the certus ownership-aware verifier as a subprocess, communicating via
// SMT-LIB2 over stdin/stdout. Specializes in:
// - L1Functional VCs (preconditions, postconditions) with ownership semantics
// - Ownership VCs (region non-aliasing, borrow validity, mutation exclusivity)
// - tRust #360: Unsafe-code VCs (UnsafeOperation, separation logic assertions)
//   where certus applies ownership-aware reasoning to raw pointer dereferences,
//   transmutes, FFI calls, and other unsafe operations.
//
// Binary discovery order: CERTUS_PATH env > PATH probe > graceful fallback.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

mod backend;
mod counterexample;
mod unsafe_classify;
mod unsafe_script;

#[cfg(test)]
mod tests;

use std::process::Command;
use std::sync::OnceLock;

// --- Re-exports preserving the original public API ---
#[allow(unused_imports)]
pub use backend::CertusBackend;
#[allow(unused_imports)]
pub(crate) use counterexample::{interpret_unsafe_counterexample, OwnershipViolation};
#[allow(unused_imports)]
pub(crate) use unsafe_classify::{classify_unsafe_vc, is_unsafe_sep_vc, UnsafeVcClass};

/// Default timeout for certus subprocess in milliseconds.
const DEFAULT_TIMEOUT_MS: u64 = 30_000;

/// Cached certus binary path, probed once per process.
static CERTUS_PATH: OnceLock<Option<String>> = OnceLock::new();

/// tRust: Probe for the certus binary.
///
/// Priority: `CERTUS_PATH` env var > `certus` on PATH.
/// Returns `None` if certus is not found.
fn probe_certus_path() -> Option<String> {
    // 1. Explicit env var
    if let Ok(path) = std::env::var("CERTUS_PATH")
        && std::path::Path::new(&path).exists() {
            return Some(path);
        }

    // 2. PATH probe
    if let Ok(output) = Command::new("which").arg("certus").output()
        && output.status.success() {
            let path = String::from_utf8_lossy(&output.stdout).trim().to_string();
            if !path.is_empty() {
                return Some(path);
            }
        }

    None
}

/// Get the cached certus path, probing only once.
fn cached_certus_path() -> Option<&'static String> {
    CERTUS_PATH.get_or_init(probe_certus_path).as_ref()
}
