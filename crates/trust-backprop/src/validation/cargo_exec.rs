//! Cargo command execution for validation.
//!
//! Runs `cargo check` and `cargo test` with timeouts for fail-closed validation.
//!
//! Author: Andrew Yates <andrew@andrewdyates.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::path::Path;
use std::time::Duration;

/// Result of running `cargo check` on a crate.
#[derive(Debug)]
pub(crate) struct CargoCheckResult {
    /// Whether the check passed (exit code 0, no errors).
    pub(crate) success: bool,
    /// Human-readable summary.
    pub(crate) summary: String,
}

/// Run `cargo check` on a crate directory with a timeout.
///
/// Returns `Ok(CargoCheckResult)` with the check outcome, or `Err(String)`
/// if the command cannot be spawned or times out.
pub(crate) fn run_cargo_check(crate_path: &Path, timeout: Duration) -> Result<CargoCheckResult, String> {
    if !crate_path.join("Cargo.toml").exists() {
        return Err(format!(
            "No Cargo.toml found at {}",
            crate_path.display()
        ));
    }

    let mut child = std::process::Command::new("cargo")
        .arg("check")
        .arg("--manifest-path")
        .arg(crate_path.join("Cargo.toml"))
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .map_err(|e| format!("Failed to spawn cargo check: {e}"))?;

    let start = std::time::Instant::now();
    loop {
        match child.try_wait() {
            Ok(Some(status)) => {
                let stderr = child
                    .stderr
                    .take()
                    .and_then(|mut s| {
                        use std::io::Read;
                        let mut buf = String::new();
                        s.read_to_string(&mut buf).ok().map(|_| buf)
                    })
                    .unwrap_or_default();

                let success = status.success();
                let summary = if success {
                    "no errors".to_string()
                } else {
                    // Extract error lines from stderr.
                    let error_lines: Vec<&str> = stderr
                        .lines()
                        .filter(|l| l.contains("error[") || l.contains("error:"))
                        .take(3)
                        .collect();
                    if error_lines.is_empty() {
                        "compilation failed (no error details)".to_string()
                    } else {
                        error_lines.join("; ")
                    }
                };

                return Ok(CargoCheckResult { success, summary });
            }
            Ok(None) => {
                if start.elapsed() > timeout {
                    let _ = child.kill();
                    let _ = child.wait();
                    return Err(format!(
                        "cargo check timed out after {}s (fail-closed)",
                        timeout.as_secs()
                    ));
                }
                std::thread::sleep(Duration::from_millis(100));
            }
            Err(e) => {
                return Err(format!("Failed to check cargo check status: {e}"));
            }
        }
    }
}

/// Result of running `cargo test` on a crate.
#[derive(Debug)]
pub(crate) struct CargoTestResult {
    /// Whether all tests passed (exit code 0).
    pub(crate) success: bool,
    /// Human-readable summary of the test run.
    pub(crate) summary: String,
}

/// Run `cargo test` on a crate directory with a timeout.
///
/// Returns `Ok(CargoTestResult)` with the test outcome, or `Err(String)`
/// if the command cannot be spawned or times out.
pub(crate) fn run_cargo_test(crate_path: &Path, timeout: Duration) -> Result<CargoTestResult, String> {
    if !crate_path.join("Cargo.toml").exists() {
        return Err(format!(
            "No Cargo.toml found at {}",
            crate_path.display()
        ));
    }

    let mut child = std::process::Command::new("cargo")
        .arg("test")
        .arg("--manifest-path")
        .arg(crate_path.join("Cargo.toml"))
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .map_err(|e| format!("Failed to spawn cargo test: {e}"))?;

    // Wait with timeout using a polling loop.
    let start = std::time::Instant::now();
    loop {
        match child.try_wait() {
            Ok(Some(status)) => {
                let stdout = child
                    .stdout
                    .take()
                    .and_then(|mut s| {
                        use std::io::Read;
                        let mut buf = String::new();
                        s.read_to_string(&mut buf).ok().map(|_| buf)
                    })
                    .unwrap_or_default();
                let stderr = child
                    .stderr
                    .take()
                    .and_then(|mut s| {
                        use std::io::Read;
                        let mut buf = String::new();
                        s.read_to_string(&mut buf).ok().map(|_| buf)
                    })
                    .unwrap_or_default();

                let success = status.success();
                let summary = extract_test_summary(&stdout, &stderr, success);

                return Ok(CargoTestResult { success, summary });
            }
            Ok(None) => {
                if start.elapsed() > timeout {
                    let _ = child.kill();
                    let _ = child.wait();
                    return Err(format!(
                        "cargo test timed out after {}s (fail-closed)",
                        timeout.as_secs()
                    ));
                }
                std::thread::sleep(Duration::from_millis(100));
            }
            Err(e) => {
                return Err(format!("Failed to check cargo test status: {e}"));
            }
        }
    }
}

/// Extract a human-readable summary from cargo test output.
pub(crate) fn extract_test_summary(stdout: &str, stderr: &str, success: bool) -> String {
    // Look for the "test result:" line in stdout.
    for line in stdout.lines().chain(stderr.lines()) {
        let trimmed = line.trim();
        if trimmed.starts_with("test result:") {
            return trimmed.to_string();
        }
    }
    if success {
        "all tests passed".to_string()
    } else {
        let error_lines: Vec<&str> = stderr
            .lines()
            .filter(|l| l.contains("error[") || l.contains("error:"))
            .take(3)
            .collect();
        if error_lines.is_empty() {
            "tests failed (no summary found in output)".to_string()
        } else {
            format!("compilation/test error: {}", error_lines.join("; "))
        }
    }
}
