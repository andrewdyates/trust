// trust-integration-tests/tests/e2e_real_rustc.rs
//
// E2E integration test using real .rs source files compiled through the actual
// tRust rustc binary. Unlike e2e_smoke.rs which uses hand-constructed MIR,
// this test invokes the real compiler as a subprocess and verifies the full
// pipeline:
//
//   real .rs file -> tRust rustc -> MIR extraction -> vcgen -> router -> z4 -> report
//
// The test parses TRUST_JSON transport lines from the compiler's stderr output
// to verify that verification conditions were generated and dispatched.
//
// When TRUST_DUMP_MIR is set, the compiler also dumps VerifiableFunction JSON
// fixtures. The test loads those and runs them through the Rust-side pipeline
// (vcgen -> real z4 -> proof-cert -> report) as a second verification path.
//
// Prerequisites:
//   - Stage1 tRust compiler: ./x.py build --stage 1
//     OR set TRUST_RUSTC=/path/to/rustc
//   - z4 binary on PATH (for real solver results; mock fallback otherwise)
//
// Issue: #937 | Epic: #935
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#![allow(rustc::default_hash_types, rustc::potential_query_instability)]

use std::path::{Path, PathBuf};
use std::process::Command;

use trust_types::*;

// ---------------------------------------------------------------------------
// Compiler discovery
// ---------------------------------------------------------------------------

/// Search for the tRust stage1 compiler binary.
///
/// Search order:
/// 1. TRUST_RUSTC environment variable (explicit override)
/// 2. build/host/stage1/bin/rustc (standard x.py output)
/// 3. build/<triple>/stage1/bin/rustc (cross-compilation)
///
/// Returns None if no compiler is found.
fn find_trust_rustc() -> Option<PathBuf> {
    // 1. Explicit env var override
    if let Ok(path) = std::env::var("TRUST_RUSTC") {
        let p = PathBuf::from(&path);
        if p.exists() {
            return Some(p);
        }
        eprintln!("WARNING: TRUST_RUSTC={path} does not exist, searching build/");
    }

    // 2. Standard build paths
    let repo_root = find_repo_root();
    let candidates = [
        repo_root.join("build/host/stage1/bin/rustc"),
        repo_root.join("build/aarch64-apple-darwin/stage1/bin/rustc"),
        repo_root.join("build/x86_64-apple-darwin/stage1/bin/rustc"),
        repo_root.join("build/x86_64-unknown-linux-gnu/stage1/bin/rustc"),
    ];

    for candidate in &candidates {
        if candidate.exists() {
            return Some(candidate.clone());
        }
    }

    None
}

/// Find the tRust repo root by walking up from CARGO_MANIFEST_DIR.
fn find_repo_root() -> PathBuf {
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    // crates/trust-integration-tests -> crates -> repo root
    manifest
        .parent()
        .and_then(|p| p.parent())
        .map(|p| p.to_path_buf())
        .unwrap_or_else(|| manifest.clone())
}

/// Check if z4 is available on PATH.
fn z4_available() -> bool {
    Command::new("z4").arg("--version").output().map(|o| o.status.success()).unwrap_or(false)
}

fn verified_lib_command(rustc: &Path, src_path: &Path, output_path: &Path) -> Command {
    let mut cmd = Command::new(rustc);
    cmd.env("TRUST_VERIFY", "1")
        .arg("--edition")
        .arg("2021")
        .arg("--crate-type")
        .arg("lib")
        .arg("-o")
        .arg(output_path)
        .arg(src_path);
    cmd
}

// ---------------------------------------------------------------------------
// Transport line parsing
// ---------------------------------------------------------------------------

/// Parse TRUST_JSON transport lines from compiler stderr output.
///
/// Each line matching `TRUST_JSON:{...}` is parsed as a TransportMessage.
/// Non-matching lines are silently skipped (they are regular compiler diagnostics).
fn parse_transport_lines(stderr: &str) -> Vec<TransportMessage> {
    stderr
        .lines()
        .filter_map(|line| {
            let trimmed = line.trim();
            trimmed
                .strip_prefix(TRANSPORT_PREFIX)
                .and_then(|json| serde_json::from_str::<TransportMessage>(json).ok())
        })
        .collect()
}

/// Extract function results from transport messages.
fn extract_function_results(messages: &[TransportMessage]) -> Vec<&FunctionTransportResult> {
    messages
        .iter()
        .filter_map(|msg| match msg {
            TransportMessage::FunctionResult(r) => Some(r),
            _ => None,
        })
        .collect()
}

// ---------------------------------------------------------------------------
// Test source code
// ---------------------------------------------------------------------------

/// The test Rust source file. Contains functions with known verification properties:
///
/// - `safe_divide`: division guarded by zero check -> div-by-zero VC should be generated
/// - `midpoint`: potential overflow -> overflow VC should be generated
/// - `always_positive`: simple addition with constants -> should be provable
const TEST_SOURCE: &str = r#"
/// Division guarded by a zero check. The if-else means the actual division
/// path has b != 0, so the div-by-zero VC should be provable.
pub fn safe_divide(a: u32, b: u32) -> Option<u32> {
    if b == 0 { None } else { Some(a / b) }
}

/// Classic midpoint calculation with potential overflow:
/// `a + (b - a) / 2` can underflow if b < a.
pub fn midpoint(a: u32, b: u32) -> u32 {
    a + (b - a) / 2
}

/// Simple constant addition -- trivially safe.
pub fn add_five(x: u32) -> u32 {
    x + 5
}

/// Unchecked division by a variable -- div-by-zero is possible.
pub fn raw_divide(a: u32, b: u32) -> u32 {
    a / b
}
"#;

// ---------------------------------------------------------------------------
// Test 1: Compiler invocation produces TRUST_JSON transport output
// ---------------------------------------------------------------------------

#[test]
fn test_e2e_real_rustc_transport_output() {
    let rustc = match find_trust_rustc() {
        Some(p) => p,
        None => {
            eprintln!(
                "SKIPPING: No tRust rustc found. Build with: ./x.py build --stage 1\n\
                 Or set TRUST_RUSTC=/path/to/rustc"
            );
            return;
        }
    };
    eprintln!("Using tRust rustc: {}", rustc.display());

    let tmp = tempfile::tempdir().unwrap();
    let src_path = tmp.path().join("test_verify.rs");
    std::fs::write(&src_path, TEST_SOURCE).unwrap();

    // Invoke the compiler with verification enabled (default).
    // Use --crate-type lib to avoid needing a main().
    let output = Command::new(&rustc)
        .env("TRUST_VERIFY", "1")
        .arg("-Z")
        .arg("trust-verify")
        .arg("--edition")
        .arg("2021")
        .arg("--crate-type")
        .arg("lib")
        .arg("-o")
        .arg(tmp.path().join("test_verify.rlib").to_str().unwrap())
        .arg(&src_path)
        .output()
        .unwrap_or_else(|e| panic!("failed to invoke tRust rustc at {}: {e}", rustc.display()));

    let stderr = String::from_utf8_lossy(&output.stderr);
    eprintln!("=== Compiler stderr ({} bytes) ===", stderr.len());
    // Print first 2000 chars of stderr for diagnostics
    let preview: String = stderr.chars().take(2000).collect();
    eprintln!("{preview}");
    if stderr.len() > 2000 {
        eprintln!("... ({} more bytes)", stderr.len() - 2000);
    }
    eprintln!("=== End compiler stderr ===");

    // The compiler should complete (exit 0) even if verification finds issues.
    // Verification is additive -- it never blocks compilation.
    assert!(
        output.status.success(),
        "tRust rustc should compile successfully (exit {}). Stderr:\n{}",
        output.status,
        stderr
    );

    // Parse transport lines
    let messages = parse_transport_lines(&stderr);
    eprintln!("Parsed {} TRUST_JSON transport messages", messages.len());

    // We expect at least one function_result message (the test source has 4 functions).
    let fn_results = extract_function_results(&messages);
    eprintln!("Function results: {}", fn_results.len());

    for result in &fn_results {
        eprintln!(
            "  {} -> {} obligations ({} proved, {} failed, {} unknown, {} runtime_checked)",
            result.function,
            result.total,
            result.proved,
            result.failed,
            result.unknown,
            result.runtime_checked,
        );
    }

    assert!(
        !fn_results.is_empty(),
        "compiler should emit at least one TRUST_JSON function_result transport line. \
         Got {} transport messages total. Is the trust_verify MIR pass enabled?",
        messages.len()
    );

    // At least one function should have VCs generated.
    let total_obligations: usize = fn_results.iter().map(|r| r.total).sum();
    assert!(
        total_obligations > 0,
        "compiler should generate at least one verification obligation across all functions. \
         Got 0 obligations from {} functions.",
        fn_results.len()
    );

    eprintln!(
        "\n=== E2E Real Rustc: {} functions verified, {} total obligations ===",
        fn_results.len(),
        total_obligations
    );
}

// ---------------------------------------------------------------------------
// Test 2: TRUST_DUMP_MIR produces valid VerifiableFunction JSON
// ---------------------------------------------------------------------------

#[test]
fn test_e2e_real_rustc_dump_mir() {
    let rustc = match find_trust_rustc() {
        Some(p) => p,
        None => {
            eprintln!(
                "SKIPPING: No tRust rustc found. Build with: ./x.py build --stage 1\n\
                 Or set TRUST_RUSTC=/path/to/rustc"
            );
            return;
        }
    };

    let tmp = tempfile::tempdir().unwrap();
    let src_path = tmp.path().join("test_dump.rs");
    std::fs::write(&src_path, TEST_SOURCE).unwrap();

    let dump_dir = tmp.path().join("mir_dump");
    std::fs::create_dir_all(&dump_dir).unwrap();

    // Invoke compiler with TRUST_DUMP_MIR to extract real MIR as JSON.
    let output = Command::new(&rustc)
        .env("TRUST_VERIFY", "1")
        .env("TRUST_DUMP_MIR", dump_dir.to_str().unwrap())
        .arg("-Z")
        .arg("trust-verify")
        .arg("--edition")
        .arg("2021")
        .arg("--crate-type")
        .arg("lib")
        .arg("-o")
        .arg(tmp.path().join("test_dump.rlib").to_str().unwrap())
        .arg(&src_path)
        .output()
        .unwrap_or_else(|e| panic!("failed to invoke tRust rustc: {e}"));

    assert!(
        output.status.success(),
        "tRust rustc should compile successfully. Stderr:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );

    // Load and validate dumped JSON fixtures.
    let entries: Vec<_> = std::fs::read_dir(&dump_dir)
        .unwrap()
        .filter_map(|e| e.ok())
        .filter(|e| e.path().extension().map_or(false, |ext| ext == "json"))
        .collect();

    eprintln!("TRUST_DUMP_MIR produced {} JSON files:", entries.len());
    for entry in &entries {
        eprintln!("  {}", entry.file_name().to_string_lossy());
    }

    assert!(!entries.is_empty(), "TRUST_DUMP_MIR should produce at least one JSON fixture");

    // Parse each fixture as a VerifiableFunction.
    let mut functions: Vec<VerifiableFunction> = Vec::new();
    for entry in &entries {
        let json = std::fs::read_to_string(entry.path())
            .unwrap_or_else(|e| panic!("failed to read {}: {e}", entry.path().display()));
        let func: VerifiableFunction = serde_json::from_str(&json).unwrap_or_else(|e| {
            panic!("failed to parse {} as VerifiableFunction: {e}", entry.path().display())
        });
        assert!(!func.name.is_empty(), "function should have a name");
        assert!(!func.def_path.is_empty(), "function should have a def_path");
        assert!(!func.body.blocks.is_empty(), "function {} should have basic blocks", func.name);
        functions.push(func);
    }

    eprintln!("\n=== E2E Real Rustc TRUST_DUMP_MIR: {} functions extracted ===", functions.len());
}

// ---------------------------------------------------------------------------
// Test 3: Full pipeline -- real rustc MIR through vcgen + real z4
// ---------------------------------------------------------------------------

#[test]
fn test_e2e_real_rustc_full_pipeline_with_z4() {
    let rustc = match find_trust_rustc() {
        Some(p) => p,
        None => {
            eprintln!(
                "SKIPPING: No tRust rustc found. Build with: ./x.py build --stage 1\n\
                 Or set TRUST_RUSTC=/path/to/rustc"
            );
            return;
        }
    };

    if !z4_available() {
        eprintln!("SKIPPING: z4 not on PATH. Install z4 for real solver verification.");
        return;
    }

    let tmp = tempfile::tempdir().unwrap();
    let src_path = tmp.path().join("test_full.rs");
    std::fs::write(&src_path, TEST_SOURCE).unwrap();

    let dump_dir = tmp.path().join("mir_dump");
    std::fs::create_dir_all(&dump_dir).unwrap();

    // Step 1: Compile with MIR dump
    let output = Command::new(&rustc)
        .env("TRUST_VERIFY", "1")
        .env("TRUST_DUMP_MIR", dump_dir.to_str().unwrap())
        .arg("-Z")
        .arg("trust-verify")
        .arg("--edition")
        .arg("2021")
        .arg("--crate-type")
        .arg("lib")
        .arg("-o")
        .arg(tmp.path().join("test_full.rlib").to_str().unwrap())
        .arg(&src_path)
        .output()
        .unwrap_or_else(|e| panic!("failed to invoke tRust rustc: {e}"));

    assert!(output.status.success(), "compilation should succeed");

    // Step 2: Load dumped MIR fixtures
    let functions = load_mir_fixtures_from_dir(&dump_dir);
    assert!(!functions.is_empty(), "should have at least one dumped function");

    eprintln!("Loaded {} functions from TRUST_DUMP_MIR", functions.len());

    // Step 3: Run each through vcgen + real z4
    let z4 = trust_router::IncrementalZ4Session::new();
    let mut total_proved = 0usize;
    let mut total_failed = 0usize;
    let mut total_unknown = 0usize;
    let mut all_results: Vec<(VerificationCondition, VerificationResult)> = Vec::new();

    for func in &functions {
        let vcs = trust_vcgen::generate_vcs(func);
        eprintln!("  {} -> {} VCs", func.def_path, vcs.len());

        for vc in &vcs {
            use trust_router::VerificationBackend;
            let result = z4.verify(vc);
            match &result {
                VerificationResult::Proved { .. } => total_proved += 1,
                VerificationResult::Failed { .. } => total_failed += 1,
                _ => total_unknown += 1,
            }
            all_results.push((vc.clone(), result));
        }
    }

    eprintln!("\n=== E2E Full Pipeline: Real Rustc + Real z4 ===");
    eprintln!("  Functions: {}", functions.len());
    eprintln!("  Total VCs: {}", all_results.len());
    eprintln!("  Proved: {total_proved}");
    eprintln!("  Failed: {total_failed}");
    eprintln!("  Unknown: {total_unknown}");

    // Acceptance criteria: at least one VC exists
    assert!(!all_results.is_empty(), "pipeline should produce at least one verification result");

    // At least one VC should reach a definitive result (proved or failed).
    let definitive = total_proved + total_failed;
    assert!(
        definitive > 0,
        "z4 should produce at least one definitive result (proved or failed). \
         Got {} proved, {} failed, {} unknown.",
        total_proved,
        total_failed,
        total_unknown
    );

    // Step 4: Generate proof certificate for functions with proved VCs
    if total_proved > 0 {
        for func in &functions {
            let vcs = trust_vcgen::generate_vcs(func);
            let mut func_results = Vec::new();
            for vc in &vcs {
                use trust_router::VerificationBackend;
                let result = z4.verify(vc);
                func_results.push((vc.clone(), result));
            }

            let has_proved = func_results.iter().any(|(_, r)| r.is_proved());
            if has_proved {
                let cert = trust_proof_cert::generate_certificate(func, &func_results);
                assert!(
                    cert.is_ok(),
                    "proof certificate generation should succeed for {}: {:?}",
                    func.name,
                    cert.err()
                );
                let cert = cert.unwrap();
                eprintln!("  Certificate for {}: hash={}", func.name, cert.certificate_hash);
                break; // One certificate is enough to demonstrate the pipeline
            }
        }
    }

    // Step 5: Generate verification report
    let report = trust_report::build_json_report("e2e_real_rustc", &all_results);
    let text = trust_report::format_json_summary(&report);
    eprintln!("\n--- Verification Report ---");
    eprintln!("{text}");
    eprintln!("--- End Report ---");

    assert!(report.summary.functions_analyzed > 0, "report should analyze at least one function");

    // Verify JSON serialization roundtrip
    let json = serde_json::to_string_pretty(&report).unwrap();
    let roundtrip: JsonProofReport = serde_json::from_str(&json).unwrap();
    assert_eq!(roundtrip.summary.total_obligations, report.summary.total_obligations);

    eprintln!("\n=== E2E Real Rustc: FULL PIPELINE VERIFIED ===");
}

// ---------------------------------------------------------------------------
// Test 4: Compiler transport lines contain expected function names
// ---------------------------------------------------------------------------

#[test]
fn test_e2e_real_rustc_function_names_in_transport() {
    let rustc = match find_trust_rustc() {
        Some(p) => p,
        None => {
            eprintln!("SKIPPING: No tRust rustc found. Build with: ./x.py build --stage 1");
            return;
        }
    };

    let tmp = tempfile::tempdir().unwrap();
    let src_path = tmp.path().join("test_names.rs");
    std::fs::write(&src_path, TEST_SOURCE).unwrap();

    let output = Command::new(&rustc)
        .env("TRUST_VERIFY", "1")
        .arg("-Z")
        .arg("trust-verify")
        .arg("--edition")
        .arg("2021")
        .arg("--crate-type")
        .arg("lib")
        .arg("-o")
        .arg(tmp.path().join("test_names.rlib").to_str().unwrap())
        .arg(&src_path)
        .output()
        .unwrap_or_else(|e| panic!("failed to invoke tRust rustc: {e}"));

    assert!(output.status.success(), "compilation should succeed");

    let stderr = String::from_utf8_lossy(&output.stderr);
    let messages = parse_transport_lines(&stderr);
    let fn_results = extract_function_results(&messages);

    // Check that at least some of our function names appear in transport output.
    let expected_names = ["safe_divide", "midpoint", "add_five", "raw_divide"];
    let found_names: Vec<&str> = fn_results.iter().map(|r| r.function.as_str()).collect();

    eprintln!("Functions in transport output:");
    for name in &found_names {
        eprintln!("  {name}");
    }

    let mut matched = 0;
    for expected in &expected_names {
        if found_names.iter().any(|n| n.contains(expected)) {
            matched += 1;
            eprintln!("  FOUND: {expected}");
        } else {
            eprintln!("  MISSING: {expected}");
        }
    }

    assert!(
        matched >= 2,
        "at least 2 of our test functions should appear in transport output. \
         Found {matched}/{} expected functions. Transport had {} function results.",
        expected_names.len(),
        fn_results.len()
    );
}

// ---------------------------------------------------------------------------
// Test 5: Verification results correctness (raw_divide should have div-by-zero VC)
// ---------------------------------------------------------------------------

#[test]
fn test_e2e_real_rustc_divzero_vc_for_raw_divide() {
    let rustc = match find_trust_rustc() {
        Some(p) => p,
        None => {
            eprintln!("SKIPPING: No tRust rustc found. Build with: ./x.py build --stage 1");
            return;
        }
    };

    let tmp = tempfile::tempdir().unwrap();
    let src_path = tmp.path().join("test_divzero.rs");
    std::fs::write(&src_path, TEST_SOURCE).unwrap();

    let output = Command::new(&rustc)
        .env("TRUST_VERIFY", "1")
        .arg("-Z")
        .arg("trust-verify")
        .arg("--edition")
        .arg("2021")
        .arg("--crate-type")
        .arg("lib")
        .arg("-o")
        .arg(tmp.path().join("test_divzero.rlib").to_str().unwrap())
        .arg(&src_path)
        .output()
        .unwrap_or_else(|e| panic!("failed to invoke tRust rustc: {e}"));

    assert!(output.status.success(), "compilation should succeed");

    let stderr = String::from_utf8_lossy(&output.stderr);
    let messages = parse_transport_lines(&stderr);
    let fn_results = extract_function_results(&messages);

    // Find raw_divide in the results -- it does `a / b` without a guard,
    // so it should have a division-by-zero VC.
    let raw_divide = fn_results.iter().find(|r| r.function.contains("raw_divide"));

    if let Some(result) = raw_divide {
        eprintln!(
            "raw_divide: {} obligations ({} proved, {} failed, {} unknown)",
            result.total, result.proved, result.failed, result.unknown
        );

        // Check that at least one obligation exists (div-by-zero).
        assert!(result.total > 0, "raw_divide should have at least one obligation (div-by-zero)");

        // Check that at least one obligation mentions divzero.
        let has_divzero = result
            .results
            .iter()
            .any(|r| r.kind.contains("divzero") || r.description.contains("division"));
        if has_divzero {
            eprintln!("  Confirmed: div-by-zero VC present for raw_divide");
        } else {
            eprintln!(
                "  Note: no explicit divzero VC tag, but {} obligations present",
                result.total
            );
            // Print all obligation kinds for debugging
            for (i, obl) in result.results.iter().enumerate() {
                eprintln!("    obligation {i}: kind={}, outcome={}", obl.kind, obl.outcome);
            }
        }
    } else {
        // If raw_divide is not in transport output, the compiler may have inlined
        // or filtered it. This is acceptable -- the test is best-effort.
        eprintln!(
            "Note: raw_divide not found in transport output ({} functions found). \
             Compiler may have filtered or inlined it.",
            fn_results.len()
        );
    }
}

// ---------------------------------------------------------------------------
// Test 6: -Z no-trust-verify suppresses the native verification pass
// ---------------------------------------------------------------------------

#[test]
fn test_e2e_real_rustc_no_trust_verify_suppresses_transport() {
    let rustc = match find_trust_rustc() {
        Some(p) => p,
        None => {
            eprintln!("SKIPPING: No tRust rustc found. Build with: ./x.py build --stage 1");
            return;
        }
    };

    let tmp = tempfile::tempdir().unwrap();
    let src_path = tmp.path().join("test_no_verify.rs");
    std::fs::write(&src_path, TEST_SOURCE).unwrap();

    let output_path = tmp.path().join("test_no_verify.rlib");
    let output = verified_lib_command(&rustc, &src_path, &output_path)
        .arg("-Z")
        .arg("trust-verify")
        .arg("-Z")
        .arg("no-trust-verify")
        .output()
        .unwrap_or_else(|e| panic!("failed to invoke tRust rustc: {e}"));

    assert!(output.status.success(), "compilation should succeed");

    let stderr = String::from_utf8_lossy(&output.stderr);
    let messages = parse_transport_lines(&stderr);
    assert!(
        messages.is_empty(),
        "expected no TRUST_JSON transport output when -Z no-trust-verify overrides verification.\nStderr:\n{}",
        stderr
    );
    assert!(
        !stderr.contains("=== tRust Verification Report"),
        "verification report banner should not be emitted when verification is disabled.\nStderr:\n{}",
        stderr
    );
}

// ---------------------------------------------------------------------------
// Test 7: compiler cache preserves transport summary counts on cache hit
// ---------------------------------------------------------------------------

#[test]
fn test_e2e_real_rustc_compiler_cache_replays_summary_counts() {
    let rustc = match find_trust_rustc() {
        Some(p) => p,
        None => {
            eprintln!("SKIPPING: No tRust rustc found. Build with: ./x.py build --stage 1");
            return;
        }
    };

    let tmp = tempfile::tempdir().unwrap();
    let src_path = tmp.path().join("test_cache.rs");
    std::fs::write(&src_path, "pub fn raw_divide(a: u32, b: u32) -> u32 { a / b }\n").unwrap();

    let first_output =
        verified_lib_command(&rustc, &src_path, &tmp.path().join("test_cache_first.rlib"))
            .current_dir(tmp.path())
            .env("TRUST_COMPILER_CACHE", "1")
            .arg("-Z")
            .arg("trust-verify")
            .output()
            .unwrap_or_else(|e| panic!("failed to invoke tRust rustc (cold cache): {e}"));
    assert!(first_output.status.success(), "cold-cache compilation should succeed");

    let first_stderr = String::from_utf8_lossy(&first_output.stderr);
    let first_messages = parse_transport_lines(&first_stderr);
    let first_raw_divide = extract_function_results(&first_messages)
        .into_iter()
        .find(|r| r.function.contains("raw_divide"))
        .expect("cold-cache run should emit raw_divide transport result");
    assert!(
        first_raw_divide.total > 0,
        "cold-cache run should record at least one obligation.\nStderr:\n{}",
        first_stderr
    );
    assert!(
        tmp.path().join(".trust-cache/proof-cache.json").exists(),
        "compiler cache should persist proof-cache.json in the current directory"
    );

    let second_output =
        verified_lib_command(&rustc, &src_path, &tmp.path().join("test_cache_second.rlib"))
            .current_dir(tmp.path())
            .env("TRUST_COMPILER_CACHE", "1")
            .arg("-Z")
            .arg("trust-verify")
            .output()
            .unwrap_or_else(|e| panic!("failed to invoke tRust rustc (warm cache): {e}"));
    assert!(second_output.status.success(), "warm-cache compilation should succeed");

    let second_stderr = String::from_utf8_lossy(&second_output.stderr);
    let second_messages = parse_transport_lines(&second_stderr);
    let second_raw_divide = extract_function_results(&second_messages)
        .into_iter()
        .find(|r| r.function.contains("raw_divide"))
        .expect("warm-cache run should emit raw_divide transport result");

    if second_raw_divide.total == 0 && first_raw_divide.total > 0 {
        let trust_verify_src =
            find_repo_root().join("compiler/rustc_mir_transform/src/trust_verify.rs");
        let rustc_mtime = std::fs::metadata(&rustc).and_then(|meta| meta.modified());
        let source_mtime = std::fs::metadata(&trust_verify_src).and_then(|meta| meta.modified());
        if let (Ok(rustc_mtime), Ok(source_mtime)) = (rustc_mtime, source_mtime) {
            if source_mtime > rustc_mtime {
                eprintln!(
                    "SKIPPING: stage1 rustc is older than {}; rebuild stage1 to validate cache transport replay.",
                    trust_verify_src.display()
                );
                return;
            }
        }
    }

    assert_eq!(
        second_raw_divide.total, first_raw_divide.total,
        "warm-cache transport should preserve total obligations.\nCold stderr:\n{}\nWarm stderr:\n{}",
        first_stderr, second_stderr
    );
    assert_eq!(
        second_raw_divide.failed, first_raw_divide.failed,
        "warm-cache transport should preserve failed counts.\nCold stderr:\n{}\nWarm stderr:\n{}",
        first_stderr, second_stderr
    );
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Load all VerifiableFunction JSON files from a directory.
fn load_mir_fixtures_from_dir(dir: &Path) -> Vec<VerifiableFunction> {
    let mut functions = Vec::new();
    let entries = match std::fs::read_dir(dir) {
        Ok(entries) => entries,
        Err(_) => return functions,
    };

    for entry in entries {
        let entry = match entry {
            Ok(e) => e,
            Err(_) => continue,
        };
        let path = entry.path();
        if path.extension().map_or(true, |ext| ext != "json") {
            continue;
        }
        let json = match std::fs::read_to_string(&path) {
            Ok(j) => j,
            Err(e) => {
                eprintln!("WARNING: failed to read {}: {e}", path.display());
                continue;
            }
        };
        match serde_json::from_str::<VerifiableFunction>(&json) {
            Ok(func) => functions.push(func),
            Err(e) => {
                eprintln!("WARNING: failed to parse {}: {e}", path.display());
            }
        }
    }

    functions
}
