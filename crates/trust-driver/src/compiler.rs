// trust-driver/compiler.rs: Stage1 rustc invocation
//
// Runs the tRust stage1 compiler on a .rs source file and captures
// stderr output containing verification diagnostics.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::path::Path;
use std::process::Command;

use crate::DriverError;

/// Invoke the stage1 rustc on `source`, returning raw stderr text.
///
/// The compiler emits verification results as `note:` diagnostics on stderr.
/// This function captures that output for downstream parsing by `parse_trust_output`.
#[must_use = "caller should parse the returned stderr"]
pub(crate) fn invoke_rustc(source: &Path, stage1_dir: &Path) -> Result<String, DriverError> {
    let rustc = stage1_dir.join("bin").join("rustc");
    if !rustc.exists() {
        return Err(DriverError::RustcNotFound {
            path: rustc.to_string_lossy().into_owned(),
        });
    }

    if !source.exists() {
        return Err(DriverError::SourceNotFound {
            path: source.to_string_lossy().into_owned(),
        });
    }

    let output = Command::new(&rustc)
        .arg("--edition")
        .arg("2021")
        .arg(source)
        .output()
        .map_err(|e| DriverError::CompilerSpawn {
            path: rustc.to_string_lossy().into_owned(),
            source: e,
        })?;

    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();

    // The compiler may exit non-zero if compilation fails (type errors, etc.)
    // but we still want the stderr for any verification notes that were emitted.
    // Only return an error if rustc produced no output at all and exited non-zero,
    // which indicates a hard failure (e.g., missing sysroot).
    if !output.status.success() && stderr.is_empty() {
        return Err(DriverError::CompilationFailed {
            exit_code: output.status.code(),
            stderr: "(no output)".to_string(),
        });
    }

    Ok(stderr)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_invoke_rustc_missing_compiler() {
        let result = invoke_rustc(
            Path::new("/tmp/test.rs"),
            Path::new("/nonexistent/stage1"),
        );
        assert!(result.is_err());
        match result.unwrap_err() {
            DriverError::RustcNotFound { path } => {
                assert!(path.contains("nonexistent"));
            }
            other => panic!("expected RustcNotFound, got {other:?}"),
        }
    }

    #[test]
    fn test_invoke_rustc_missing_source() {
        // Create a temp dir with a fake bin/rustc to pass the first check
        let tmp = std::env::temp_dir().join("trust-driver-test-stage1");
        let bin_dir = tmp.join("bin");
        std::fs::create_dir_all(&bin_dir).expect("create test dir");
        let fake_rustc = bin_dir.join("rustc");
        std::fs::write(&fake_rustc, "#!/bin/sh\n").expect("write fake rustc");

        let result = invoke_rustc(
            Path::new("/nonexistent/source.rs"),
            &tmp,
        );
        assert!(result.is_err());
        match result.unwrap_err() {
            DriverError::SourceNotFound { path } => {
                assert!(path.contains("nonexistent"));
            }
            other => panic!("expected SourceNotFound, got {other:?}"),
        }

        // Cleanup
        let _ = std::fs::remove_dir_all(&tmp);
    }
}
